#![expect(clippy::unwrap_used)] // TODO(emilk): remove unwraps

use core::{iter, ops::Range};
use std::sync::Arc;

use emath::{Align, GuiRounding as _, NumExt as _, Pos2, Rect, Vec2, pos2, vec2};

use crate::{
    Color32, Mesh, Stroke, Vertex,
    stroke::PathStroke,
    text::{
        ByteIndex, ByteRange,
        font::{StyledMetrics, UvRect, is_cjk, is_cjk_break_allowed},
        fonts::FontFaceKey,
    },
};

use super::{
    ByteRangeExt as _, FontsImpl, Galley, Glyph, LayoutJob, LayoutSection, PlacedRow, Row,
    RowVisuals, VariationCoords,
    font::{ClusterGlyph, Font, FontFace, ShapedGlyph},
};

// ----------------------------------------------------------------------------

/// Returns `true` if the character is a Unicode combining mark (categories Mn, Mc, Me).
///
/// These characters modify the preceding base character and should not be
/// rendered as standalone replacement glyphs when the shaper can't handle them.
#[inline]
fn is_combining_mark(c: char) -> bool {
    use unicode_general_category::{GeneralCategory, get_general_category};
    matches!(
        get_general_category(c),
        GeneralCategory::NonspacingMark
            | GeneralCategory::SpacingMark
            | GeneralCategory::EnclosingMark
    )
}

/// Represents GUI scale and convenience methods for rounding to pixels.
#[derive(Clone, Copy)]
struct PointScale {
    pub pixels_per_point: f32,
}

impl PointScale {
    #[inline(always)]
    pub fn new(pixels_per_point: f32) -> Self {
        Self { pixels_per_point }
    }

    #[inline(always)]
    pub fn pixels_per_point(&self) -> f32 {
        self.pixels_per_point
    }

    #[inline(always)]
    pub fn round_to_pixel(&self, point: f32) -> f32 {
        (point * self.pixels_per_point).round() / self.pixels_per_point
    }

    #[inline(always)]
    pub fn floor_to_pixel(&self, point: f32) -> f32 {
        (point * self.pixels_per_point).floor() / self.pixels_per_point
    }
}

// ----------------------------------------------------------------------------

/// Temporary storage before line-wrapping.
#[derive(Clone)]
struct Paragraph {
    /// Start of the next glyph to be added. In screen-space / physical pixels.
    pub cursor_x_px: f32,

    /// This is included in case there are no glyphs
    pub section_index_at_start: u32,

    pub glyphs: Vec<Glyph>,

    /// In case of an empty paragraph ("\n"), use this as height.
    pub empty_paragraph_height: f32,
}

impl Paragraph {
    pub fn from_section_index(section_index_at_start: u32) -> Self {
        Self {
            cursor_x_px: 0.0,
            section_index_at_start,
            glyphs: vec![],
            empty_paragraph_height: 0.0,
        }
    }
}

/// Layout text into a [`Galley`].
///
/// In most cases you should use [`crate::FontsView::layout_job`] instead
/// since that memoizes the input, making subsequent layouting of the same text much faster.
pub fn layout(fonts: &mut FontsImpl, pixels_per_point: f32, job: Arc<LayoutJob>) -> Galley {
    profiling::function_scope!();

    job.debug_sanity_check();

    if job.wrap.max_rows == 0 {
        // Early-out: no text
        return Galley {
            job,
            rows: Default::default(),
            rect: Rect::ZERO,
            mesh_bounds: Rect::NOTHING,
            num_vertices: 0,
            num_indices: 0,
            pixels_per_point,
            elided: true,
            intrinsic_size: Vec2::ZERO,
        };
    }

    // For most of this we ignore the y coordinate:

    let base_level = match job.direction {
        super::TextDirection::Auto => None,
        super::TextDirection::LeftToRight => Some(unicode_bidi::Level::ltr()),
        super::TextDirection::RightToLeft => Some(unicode_bidi::Level::rtl()),
    };
    let bidi = (!job.text.is_ascii() || base_level.is_some_and(|level| level.is_rtl()))
        .then(|| unicode_bidi::BidiInfo::new(&job.text, base_level));
    let mut paragraphs = vec![Paragraph::from_section_index(0)];
    {
        let mut shape_buffer = fonts.take_shape_buffer();
        for (section_index, section) in job.sections.iter().enumerate() {
            let mut font = fonts.font(&section.format.font_id.family);
            shape_buffer = layout_section(
                &mut font,
                shape_buffer,
                pixels_per_point,
                &job,
                section_index as u32,
                bidi.as_ref().map_or(&[], |info| info.levels.as_slice()),
                &mut paragraphs,
            );
        }
        fonts.return_shape_buffer(shape_buffer);
    }

    let point_scale = PointScale::new(pixels_per_point);

    let intrinsic_size = calculate_intrinsic_size(point_scale, &job, &paragraphs);

    let mut elided = false;
    let mut rows = rows_from_paragraphs(paragraphs, &job, pixels_per_point, &mut elided);
    if elided && let Some(last_placed) = rows.last_mut() {
        let last_row = Arc::make_mut(&mut last_placed.row);
        replace_last_glyph_with_overflow_character(fonts, pixels_per_point, &job, last_row);
        if let Some(last) = last_row.glyphs.last() {
            last_row.size.x = last.max_x();
        }
    }

    if let Some(bidi) = &bidi {
        let mut source_chars = job.text.char_indices().peekable();
        for placed in &mut rows {
            let row = Arc::make_mut(&mut placed.row);
            let byte_start = source_chars.peek().map_or(job.text.len(), |&(i, _)| i);
            for _ in &row.glyphs {
                source_chars.next();
            }
            let byte_end = source_chars.peek().map_or(job.text.len(), |&(i, _)| i);
            if let Some(para) = bidi
                .paragraphs
                .iter()
                .find(|p| p.range.start <= byte_start && byte_start < p.range.end)
                && let Some(text) = job.text.get(byte_start..byte_end)
                && let Some(classes) = bidi.original_classes.get(byte_start..byte_end)
                && let Some(levels) = bidi.levels.get(byte_start..byte_end)
            {
                row.paragraph_level = para.level.number();
                // Restrict the temporary data to this line; the API otherwise clones
                // every paragraph's levels once for every wrapped row.
                let line = unicode_bidi::ParagraphBidiInfo {
                    text,
                    original_classes: classes.to_vec(),
                    levels: levels.to_vec(),
                    paragraph_level: para.level,
                    is_pure_ltr: false,
                };
                let levels = line.reordered_levels(0..text.len());
                for ((offset, _), glyph) in text.char_indices().zip(&mut row.glyphs) {
                    if let Some(level) = levels.get(offset) {
                        glyph.bidi_level = level.number();
                    }
                }
                reorder_row_visually(point_scale, row);
            }
            if placed.ends_with_newline {
                source_chars.next();
            }
        }
    }

    let justify = job.justify && job.wrap.max_width.is_finite();

    if justify || job.halign != Align::LEFT {
        let num_rows = rows.len();
        for (i, placed_row) in rows.iter_mut().enumerate() {
            let is_last_row = i + 1 == num_rows;
            let justify_row = justify && !placed_row.ends_with_newline && !is_last_row;
            halign_and_justify_row(
                point_scale,
                placed_row,
                job.halign,
                job.wrap.max_width,
                justify_row,
                job.keep_trailing_whitespace,
            );
        }
    }

    // Calculate the Y positions and tessellate the text:
    galley_from_rows(point_scale, job, rows, elided, intrinsic_size)
}

/// Shared context for emitting shaped glyphs into a [`Paragraph`].
struct ShapingContext {
    pixels_per_point: f32,
    font_size: f32,
    line_height: f32,
    extra_letter_spacing: f32,
    section_index: u32,
    font_metrics: StyledMetrics,
    is_first_glyph_in_section: bool,
    bidi_level: u8,
}

impl ShapingContext {
    fn glyph(
        &self,
        chr: char,
        physical_x: i32,
        advance_width_px: f32,
        face_metrics: &StyledMetrics,
        uv_rect: UvRect,
    ) -> Glyph {
        Glyph {
            chr,
            bidi_level: self.bidi_level,
            cluster_continuation: false,
            pos: pos2(physical_x as f32 / self.pixels_per_point, f32::NAN),
            advance_width: advance_width_px / self.pixels_per_point,
            line_height: self.line_height,
            font_face_height: face_metrics.row_height,
            font_face_ascent: face_metrics.ascent,
            font_height: self.font_metrics.row_height,
            font_ascent: self.font_metrics.ascent,
            uv_rect,
            section_index: self.section_index,
            first_vertex: 0,
        }
    }
}

/// Produced by [`segment_into_runs`] for text shaping.
#[derive(Debug)]
struct TextRun {
    /// Which font face should shape this run.
    font_key: FontFaceKey,

    /// Byte range within the section text.
    byte_range: ByteRange,
    script: unicode_script::Script,
    bidi_level: u8,
}

/// Emit shaped glyphs from a [`harfrust::GlyphBuffer`] into a [`Paragraph`].
///
/// Each shaped cluster gets one bitmap, preserving all base and mark offsets.
/// Each source character retains a logical glyph entry. Letters in a ligature
/// share its advance for caret placement; combining marks have zero advance.
fn layout_shaped_run(
    font: &mut Font<'_>,
    run: &TextRun,
    run_text: &str,
    glyph_buffer: &harfrust::GlyphBuffer,
    face_metrics: &StyledMetrics,
    ctx: &mut ShapingContext,
    paragraph: &mut Paragraph,
) {
    let infos = glyph_buffer.glyph_infos();
    let positions = glyph_buffer.glyph_positions();
    let mut clusters = Vec::new();
    let mut start = 0;
    for (i, info) in infos.iter().enumerate() {
        if infos
            .get(start)
            .is_some_and(|first| first.cluster != info.cluster)
        {
            clusters.push(start..i);
            start = i;
        }
    }
    if start < infos.len() {
        clusters.push(start..infos.len());
    }
    if run.bidi_level % 2 == 1 {
        clusters.reverse();
    }

    for (cluster_index, range) in clusters.iter().enumerate() {
        let Some(first) = infos.get(range.start) else {
            continue;
        };
        let byte_start = first.cluster as usize;
        let byte_end = clusters
            .get(cluster_index + 1)
            .and_then(|next| infos.get(next.start))
            .map_or(run_text.len(), |next| next.cluster as usize);
        let Some(cluster_text) = run_text.get(byte_start..byte_end) else {
            continue;
        };
        let Some(chr) = cluster_text.chars().next() else {
            continue;
        };
        if !ctx.is_first_glyph_in_section {
            paragraph.cursor_x_px += ctx.extra_letter_spacing * ctx.pixels_per_point;
        }
        ctx.is_first_glyph_in_section = false;
        let origin = paragraph.cursor_x_px;
        let mut advance = 0.0;
        let mut outlines = smallvec::SmallVec::<[ClusterGlyph; 2]>::new();
        for (info, pos) in infos
            .get(range.clone())
            .unwrap_or_default()
            .iter()
            .zip(positions.get(range.clone()).unwrap_or_default())
        {
            let glyph_id = skrifa::GlyphId::new(info.glyph_id);
            if glyph_id != skrifa::GlyphId::NOTDEF {
                outlines.push(ClusterGlyph {
                    glyph_id,
                    offset_px: vec2(
                        advance + pos.x_offset as f32 * face_metrics.px_scale_factor,
                        -(pos.y_offset as f32 * face_metrics.px_scale_factor),
                    ),
                });
            }
            advance += pos.x_advance as f32 * face_metrics.px_scale_factor;
        }
        let mut metrics = face_metrics.clone();
        let (allocation, physical_x) = if outlines.is_empty() && !is_combining_mark(chr) {
            let fallback = font.resolve_face(chr);
            metrics = font
                .fonts_by_id
                .get(&fallback)
                .map(|face| {
                    face.styled_metrics(ctx.pixels_per_point, ctx.font_size, &Default::default())
                })
                .unwrap_or_default();
            let (_, info) = font.glyph_info(chr, &metrics);
            advance = info.advance_width_unscaled.0 * metrics.px_scale_factor;
            font.fonts_by_id
                .get_mut(&fallback)
                .map(|face| {
                    face.allocate_glyph(
                        font.atlas,
                        &metrics,
                        &ShapedGlyph {
                            glyph_id: info.id.unwrap_or(skrifa::GlyphId::NOTDEF),
                            h_pos: origin,
                            is_cjk: is_cjk(chr),
                        },
                    )
                })
                .unwrap_or_default()
        } else if let Some(face) = font.fonts_by_id.get_mut(&run.font_key) {
            face.allocate_cluster(font.atlas, face_metrics, &outlines, origin, is_cjk(chr))
        } else {
            Default::default()
        };
        if matches!(chr, '\t' | '\u{2009}' | '\u{202F}') {
            let tweak = font.fonts_by_id.get(&run.font_key).map(|face| face.tweak());
            let multiplier = if chr == '\t' {
                tweak.map_or(4.0, |t| t.tab_size)
            } else {
                tweak.map_or(0.5, |t| t.thin_space_width)
            };
            let (_, space) = font.glyph_info(' ', face_metrics);
            advance = multiplier * space.advance_width_unscaled.0 * face_metrics.px_scale_factor;
        }
        paragraph.cursor_x_px += advance;
        let letters = cluster_text
            .chars()
            .filter(|c| c.is_alphabetic() && !is_combining_mark(*c))
            .count();
        let mut caret_x = physical_x as f32;
        for (index, chr) in cluster_text.chars().enumerate() {
            let char_advance = if letters > 1 {
                if chr.is_alphabetic() && !is_combining_mark(chr) {
                    advance / letters as f32
                } else {
                    0.0
                }
            } else if index == 0 {
                advance
            } else {
                0.0
            };
            let mut glyph = ctx.glyph(
                chr,
                caret_x.round() as i32,
                char_advance,
                &metrics,
                if index == 0 {
                    allocation.uv_rect
                } else {
                    UvRect::default()
                },
            );
            glyph.cluster_continuation = index > 0;
            paragraph.glyphs.push(glyph);
            caret_x += char_advance;
        }
    }
}

// Ignores the Y coordinate.
#[must_use]
fn layout_section(
    font: &mut Font<'_>,
    mut shape_buffer: harfrust::UnicodeBuffer,
    pixels_per_point: f32,
    job: &LayoutJob,
    section_index: u32,
    levels: &[unicode_bidi::Level],
    out_paragraphs: &mut Vec<Paragraph>,
) -> harfrust::UnicodeBuffer {
    let Some(section) = job.sections.get(section_index as usize) else {
        return shape_buffer;
    };
    let LayoutSection {
        leading_space,
        byte_range,
        format,
    } = section;

    let font_size = format.font_id.size;
    let font_metrics = font.styled_metrics(pixels_per_point, font_size, &format.coords);
    let line_height = section
        .format
        .line_height
        .unwrap_or(font_metrics.row_height);
    let extra_letter_spacing = section.format.extra_letter_spacing;

    let mut paragraph = out_paragraphs.last_mut().unwrap();
    if paragraph.glyphs.is_empty() {
        paragraph.empty_paragraph_height = line_height;
    }
    paragraph.cursor_x_px += leading_space * pixels_per_point;

    let section_text = &job.text[byte_range.as_usize()];
    let mut ctx = ShapingContext {
        pixels_per_point,
        font_size,
        line_height,
        extra_letter_spacing,
        section_index,
        font_metrics,
        is_first_glyph_in_section: paragraph.glyphs.is_empty(),
        bidi_level: 0,
    };
    let mut runs = Vec::new();

    let mut segment_offset = byte_range.start.0;

    // Process each paragraph segment (split on newlines — the shaper can't handle them).
    for (seg_idx, segment) in SplitOrWhole::new(section_text, job.break_on_newline).enumerate() {
        if 0 < seg_idx {
            paragraph = out_paragraphs.push_mut(Paragraph::from_section_index(section_index));
            paragraph.empty_paragraph_height = line_height;
            ctx.is_first_glyph_in_section = true;
        }

        if segment.is_empty() {
            segment_offset = segment_offset.saturating_add(1);
            continue;
        }

        segment_into_runs(
            font,
            segment,
            levels.get(segment_offset..).unwrap_or_default(),
            &mut runs,
        );
        segment_offset = segment_offset
            .saturating_add(segment.len())
            .saturating_add(1);

        let num_runs = runs.len();
        for (run_idx, run) in runs.iter().enumerate() {
            let run_text = &segment[run.byte_range.as_usize()];
            let Some(font_face) = font.fonts_by_id.get(&run.font_key) else {
                continue;
            };

            let face_metrics =
                font_face.styled_metrics(pixels_per_point, font_size, &format.coords);

            // Set buffer flags for paragraph boundary context.
            let mut flags = harfrust::BufferFlags::empty();
            if run_idx == 0 {
                flags |= harfrust::BufferFlags::BEGINNING_OF_TEXT;
            }
            if run_idx + 1 == num_runs {
                flags |= harfrust::BufferFlags::END_OF_TEXT;
            }

            ctx.bidi_level = run.bidi_level;
            let mut directed_buffer = shape_buffer;
            directed_buffer.set_direction(if run.bidi_level % 2 == 1 {
                harfrust::Direction::RightToLeft
            } else {
                harfrust::Direction::LeftToRight
            });
            let glyph_buffer =
                shape_text(font_face, run_text, &format.coords, directed_buffer, flags);

            layout_shaped_run(
                font,
                run,
                run_text,
                &glyph_buffer,
                &face_metrics,
                &mut ctx,
                paragraph,
            );

            shape_buffer = glyph_buffer.clear();
        }
    }

    shape_buffer
}

/// Iterator that either splits on `'\n'` or yields the whole string once.
/// Avoids `Box<dyn Iterator>` and `Vec<&str>` allocation.
enum SplitOrWhole<'a> {
    Split(core::str::Split<'a, char>),
    Whole(iter::Once<&'a str>),
}

impl<'a> SplitOrWhole<'a> {
    fn new(text: &'a str, split: bool) -> Self {
        if split {
            Self::Split(text.split('\n'))
        } else {
            Self::Whole(iter::once(text))
        }
    }
}

impl<'a> Iterator for SplitOrWhole<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        match self {
            Self::Split(iter) => iter.next(),
            Self::Whole(iter) => iter.next(),
        }
    }
}

/// Calculate the intrinsic size of the text.
///
/// The result is eventually passed to `Response::intrinsic_size`.
/// This works by calculating the size of each `Paragraph` (instead of each `Row`).
fn calculate_intrinsic_size(
    point_scale: PointScale,
    job: &LayoutJob,
    paragraphs: &[Paragraph],
) -> Vec2 {
    let mut intrinsic_size = Vec2::ZERO;
    for (idx, paragraph) in paragraphs.iter().enumerate() {
        // Use the precise cursor position instead of `last_glyph.max_x()`,
        // because glyph positions are pixel-snapped but the cursor tracks
        // the exact subpixel advance. This ensures that when two galleys are
        // placed side-by-side, the gap matches what it would be within a
        // single galley.
        let width = paragraph.cursor_x_px / point_scale.pixels_per_point;
        intrinsic_size.x = f32::max(intrinsic_size.x, width);

        let mut height = paragraph
            .glyphs
            .iter()
            .map(|g| g.line_height)
            .max_by(|a, b| a.partial_cmp(b).unwrap_or(core::cmp::Ordering::Equal))
            .unwrap_or(paragraph.empty_paragraph_height);
        if idx == 0 {
            height = f32::max(height, job.first_row_min_height);
        }
        intrinsic_size.y += point_scale.round_to_pixel(height);
    }
    intrinsic_size
}

// Ignores the Y coordinate.
fn rows_from_paragraphs(
    paragraphs: Vec<Paragraph>,
    job: &LayoutJob,
    pixels_per_point: f32,
    elided: &mut bool,
) -> Vec<PlacedRow> {
    let num_paragraphs = paragraphs.len();

    let mut rows = vec![];

    for (i, paragraph) in paragraphs.into_iter().enumerate() {
        if job.wrap.max_rows <= rows.len() {
            *elided = true;
            break;
        }

        let is_last_paragraph = (i + 1) == num_paragraphs;

        if paragraph.glyphs.is_empty() {
            rows.push(PlacedRow {
                pos: pos2(0.0, f32::NAN),
                row: Arc::new(Row {
                    paragraph_level: 0,
                    section_index_at_start: paragraph.section_index_at_start,
                    glyphs: vec![],
                    visuals: Default::default(),
                    size: vec2(0.0, paragraph.empty_paragraph_height),
                }),
                ends_with_newline: !is_last_paragraph,
            });
        } else {
            // Use precise cursor position for width instead of pixel-snapped
            // `last_glyph.max_x()`, so that side-by-side galleys have the same
            // spacing as characters within a single galley.
            let paragraph_width = paragraph.cursor_x_px / pixels_per_point;
            if paragraph_width <= job.effective_wrap_width() {
                // Early-out optimization: the whole paragraph fits on one row.
                rows.push(PlacedRow {
                    pos: pos2(0.0, f32::NAN),
                    row: Arc::new(Row {
                        paragraph_level: 0,
                        section_index_at_start: paragraph.section_index_at_start,
                        glyphs: paragraph.glyphs,
                        visuals: Default::default(),
                        size: vec2(paragraph_width, 0.0),
                    }),
                    ends_with_newline: !is_last_paragraph,
                });
            } else {
                line_break(&paragraph, job, &mut rows, elided);
                let placed_row = rows.last_mut().unwrap();
                placed_row.ends_with_newline = !is_last_paragraph;
            }
        }
    }

    rows
}

fn line_break(
    paragraph: &Paragraph,
    job: &LayoutJob,
    out_rows: &mut Vec<PlacedRow>,
    elided: &mut bool,
) {
    let wrap_width = job.effective_wrap_width();

    // Keeps track of good places to insert row break if we exceed `wrap_width`.
    let mut row_break_candidates = RowBreakCandidates::default();

    let mut first_row_indentation = paragraph.glyphs[0].pos.x;
    let mut row_start_x = 0.0;
    let mut row_start_idx = 0;

    for i in 0..paragraph.glyphs.len() {
        if job.wrap.max_rows <= out_rows.len() {
            *elided = true;
            break;
        }

        let potential_row_width = paragraph.glyphs[i].max_x() - row_start_x;

        if wrap_width < potential_row_width {
            // Row break:

            if first_row_indentation > 0.0
                && !row_break_candidates.has_good_candidate(job.wrap.break_anywhere)
            {
                // Allow the first row to be completely empty, because we know there will be more space on the next row:
                // TODO(emilk): this records the height of this first row as zero, though that is probably fine since first_row_indentation usually comes with a first_row_min_height.
                out_rows.push(PlacedRow {
                    pos: pos2(0.0, f32::NAN),
                    row: Arc::new(Row {
                        paragraph_level: 0,
                        section_index_at_start: paragraph.section_index_at_start,
                        glyphs: vec![],
                        visuals: Default::default(),
                        size: Vec2::ZERO,
                    }),
                    ends_with_newline: false,
                });
                row_start_x += first_row_indentation;
                first_row_indentation = 0.0;
            } else if let Some(last_kept_index) = row_break_candidates.get(job.wrap.break_anywhere)
            {
                let glyphs: Vec<Glyph> = paragraph.glyphs[row_start_idx..=last_kept_index]
                    .iter()
                    .copied()
                    .map(|mut glyph| {
                        glyph.pos.x -= row_start_x;
                        glyph
                    })
                    .collect();

                let section_index_at_start = glyphs[0].section_index;
                let paragraph_max_x = glyphs.last().unwrap().max_x();

                out_rows.push(PlacedRow {
                    pos: pos2(0.0, f32::NAN),
                    row: Arc::new(Row {
                        paragraph_level: 0,
                        section_index_at_start,
                        glyphs,
                        visuals: Default::default(),
                        size: vec2(paragraph_max_x, 0.0),
                    }),
                    ends_with_newline: false,
                });

                // Start a new row:
                row_start_idx = last_kept_index + 1;
                row_start_x = paragraph.glyphs[row_start_idx].pos.x;
                row_break_candidates.forget_before_idx(row_start_idx);
            } else {
                // Found no place to break, so we have to overrun wrap_width.
            }
        }

        row_break_candidates.add(i, &paragraph.glyphs[i..]);
    }

    if row_start_idx < paragraph.glyphs.len() {
        // Final row of text:

        if job.wrap.max_rows <= out_rows.len() {
            *elided = true; // can't fit another row
        } else {
            let paragraph_min_x = paragraph.glyphs[row_start_idx].pos.x - row_start_x;
            let paragraph_max_x = paragraph.glyphs.last().unwrap().max_x() - row_start_x;

            let glyphs: Vec<Glyph> = paragraph.glyphs[row_start_idx..]
                .iter()
                .copied()
                .map(|mut glyph| {
                    glyph.pos.x -= row_start_x + paragraph_min_x;
                    glyph
                })
                .collect();

            let section_index_at_start = glyphs[0].section_index;

            out_rows.push(PlacedRow {
                pos: pos2(paragraph_min_x, 0.0),
                row: Arc::new(Row {
                    paragraph_level: 0,
                    section_index_at_start,
                    glyphs,
                    visuals: Default::default(),
                    size: vec2(paragraph_max_x - paragraph_min_x, 0.0),
                }),
                ends_with_newline: false,
            });
        }
    }
}

/// Trims the last glyphs in the row and replaces it with an overflow character (e.g. `…`).
///
/// Called before we have any Y coordinates.
fn replace_last_glyph_with_overflow_character(
    fonts: &mut FontsImpl,
    pixels_per_point: f32,
    job: &LayoutJob,
    row: &mut Row,
) {
    let Some(overflow_character) = job.wrap.overflow_character else {
        return;
    };

    let mut section_index = row
        .glyphs
        .last()
        .map(|g| g.section_index)
        .unwrap_or(row.section_index_at_start);
    loop {
        let section = &job.sections[section_index as usize];
        let extra_letter_spacing = section.format.extra_letter_spacing;
        let mut font = fonts.font(&section.format.font_id.family);
        let font_size = section.format.font_id.size;

        let font_id = font.resolve_face(overflow_character);
        let font_face_metrics = font
            .fonts_by_id
            .get(&font_id)
            .map(|f| f.styled_metrics(pixels_per_point, font_size, &section.format.coords))
            .unwrap_or_default();
        let (_, glyph_info) = font.glyph_info(overflow_character, &font_face_metrics);
        let mut font_face = font.fonts_by_id.get_mut(&font_id);

        let overflow_glyph_x = if let Some(prev_glyph) = row.glyphs.last() {
            prev_glyph.max_x() + extra_letter_spacing
        } else {
            0.0 // TODO(emilk): heed paragraph leading_space 😬
        };

        let advance_width_px =
            glyph_info.advance_width_unscaled.0 * font_face_metrics.px_scale_factor;
        let replacement_glyph_width = advance_width_px / pixels_per_point;

        // Check if we're within width budget:
        if overflow_glyph_x + replacement_glyph_width <= job.effective_wrap_width()
            || row.glyphs.is_empty()
        {
            // we are done

            let (replacement_glyph_alloc, physical_x) = font_face
                .as_mut()
                .map(|f| {
                    f.allocate_glyph(
                        font.atlas,
                        &font_face_metrics,
                        &ShapedGlyph {
                            glyph_id: glyph_info.id.unwrap_or(skrifa::GlyphId::NOTDEF),
                            h_pos: overflow_glyph_x * pixels_per_point,
                            is_cjk: is_cjk(overflow_character),
                        },
                    )
                })
                .unwrap_or_default();

            let font_metrics =
                font.styled_metrics(pixels_per_point, font_size, &section.format.coords);
            let line_height = section
                .format
                .line_height
                .unwrap_or(font_metrics.row_height);

            row.glyphs.push(Glyph {
                bidi_level: row.glyphs.last().map_or(0, |g| g.bidi_level),
                cluster_continuation: false,
                chr: overflow_character,
                pos: pos2(physical_x as f32 / pixels_per_point, f32::NAN),
                advance_width: advance_width_px / pixels_per_point,
                line_height,
                font_face_height: font_face_metrics.row_height,
                font_face_ascent: font_face_metrics.ascent,
                font_height: font_metrics.row_height,
                font_ascent: font_metrics.ascent,
                uv_rect: replacement_glyph_alloc.uv_rect,
                section_index,
                first_vertex: 0, // filled in later
            });
            return;
        }

        // We didn't fit - pop the last glyph and try again.
        if let Some(last_glyph) = row.glyphs.pop() {
            section_index = last_glyph.section_index;
        } else {
            section_index = row.section_index_at_start;
        }
    }
}

/// Horizontally aligned the text on a row.
///
/// Ignores the Y coordinate.
fn halign_and_justify_row(
    point_scale: PointScale,
    placed_row: &mut PlacedRow,
    halign: Align,
    wrap_width: f32,
    justify: bool,
    keep_trailing_whitespace: bool,
) {
    #![expect(clippy::useless_let_if_seq)] // False positive

    let row = Arc::make_mut(&mut placed_row.row);

    if row.glyphs.is_empty() {
        return;
    }

    let num_leading_spaces = row
        .glyphs
        .iter()
        .take_while(|glyph| glyph.chr.is_whitespace())
        .count();

    let glyph_range = if num_leading_spaces == row.glyphs.len() {
        // There is only whitespace
        (0, row.glyphs.len())
    } else if keep_trailing_whitespace {
        (num_leading_spaces, row.glyphs.len())
    } else {
        let num_trailing_spaces = row
            .glyphs
            .iter()
            .rev()
            .take_while(|glyph| glyph.chr.is_whitespace())
            .count();

        (num_leading_spaces, row.glyphs.len() - num_trailing_spaces)
    };
    let mut blocks = glyph_clusters(row);
    blocks.sort_by(|a, b| {
        let left = |block: &Range<usize>| {
            row.glyphs
                .get(block.clone())
                .unwrap_or_default()
                .iter()
                .map(|g| g.pos.x)
                .fold(f32::INFINITY, f32::min)
        };
        left(a).total_cmp(&left(b))
    });
    let in_range = |block: &Range<usize>| block.start < glyph_range.1 && glyph_range.0 < block.end;
    let num_glyphs_in_range = blocks.iter().filter(|block| in_range(block)).count();
    if num_glyphs_in_range == 0 {
        return;
    }

    let original_min_x = row
        .glyphs
        .get(glyph_range.0..glyph_range.1)
        .unwrap_or_default()
        .iter()
        .map(|g| g.pos.x)
        .fold(f32::INFINITY, f32::min);
    let original_max_x = row
        .glyphs
        .get(glyph_range.0..glyph_range.1)
        .unwrap_or_default()
        .iter()
        .map(Glyph::max_x)
        .fold(f32::NEG_INFINITY, f32::max);
    let original_width = original_max_x - original_min_x;

    let target_width = if justify && num_glyphs_in_range > 1 {
        wrap_width
    } else {
        original_width
    };

    let (target_min_x, target_max_x) = match halign {
        Align::LEFT => (0.0, target_width),
        Align::Center => (-target_width / 2.0, target_width / 2.0),
        Align::RIGHT => (-target_width, 0.0),
    };

    let num_spaces_in_range = blocks
        .iter()
        .filter(|block| {
            in_range(block)
                && row
                    .glyphs
                    .get(block.start)
                    .is_some_and(|g| g.chr.is_whitespace())
        })
        .count();

    let mut extra_x_per_glyph = if num_glyphs_in_range == 1 {
        0.0
    } else {
        (target_width - original_width) / (num_glyphs_in_range as f32 - 1.0)
    };
    extra_x_per_glyph = extra_x_per_glyph.at_least(0.0); // Don't contract

    let mut extra_x_per_space = 0.0;
    if 0 < num_spaces_in_range && num_spaces_in_range < num_glyphs_in_range {
        // Add an integral number of pixels between each glyph,
        // and add the balance to the spaces:

        extra_x_per_glyph = point_scale.floor_to_pixel(extra_x_per_glyph);

        extra_x_per_space = (target_width
            - original_width
            - extra_x_per_glyph * (num_glyphs_in_range as f32 - 1.0))
            / (num_spaces_in_range as f32);
    }

    placed_row.pos.x = point_scale.round_to_pixel(target_min_x);
    let preceding = blocks.iter().take_while(|block| !in_range(block)).count();
    let mut translate_x = -original_min_x - extra_x_per_glyph * preceding as f32;
    for block in blocks {
        let Some(glyphs) = row.glyphs.get_mut(block) else {
            continue;
        };
        let origin = glyphs.iter().map(|g| g.pos.x).fold(f32::INFINITY, f32::min);
        let translation = point_scale.round_to_pixel(origin + translate_x) - origin;
        let whitespace = glyphs.first().is_some_and(|g| g.chr.is_whitespace());
        for glyph in glyphs {
            glyph.pos.x += translation;
        }
        translate_x += extra_x_per_glyph;
        if whitespace {
            translate_x += extra_x_per_space;
        }
    }

    // Note we ignore the leading/trailing whitespace here!
    row.size.x = target_max_x - target_min_x;
}

/// Calculate the Y positions and tessellate the text.
fn galley_from_rows(
    point_scale: PointScale,
    job: Arc<LayoutJob>,
    mut rows: Vec<PlacedRow>,
    elided: bool,
    intrinsic_size: Vec2,
) -> Galley {
    let mut first_row_min_height = job.first_row_min_height;
    let mut cursor_y = 0.0;

    for placed_row in &mut rows {
        let mut max_row_height = first_row_min_height.at_least(placed_row.height());
        let row = Arc::make_mut(&mut placed_row.row);

        first_row_min_height = 0.0;
        for glyph in &row.glyphs {
            max_row_height = max_row_height.at_least(glyph.line_height);
        }
        max_row_height = point_scale.round_to_pixel(max_row_height);

        // Now position each glyph vertically:
        for glyph in &mut row.glyphs {
            let format = &job.sections[glyph.section_index as usize].format;

            glyph.pos.y = glyph.font_face_ascent

                // Apply valign to the different in height of the entire row, and the height of this `Font`:
                + format.valign.to_factor() * (max_row_height - glyph.line_height)

                // When mixing different `FontImpl` (e.g. latin and emojis),
                // we always center the difference:
                + 0.5 * (glyph.font_height - glyph.font_face_height);

            glyph.pos.y = point_scale.round_to_pixel(glyph.pos.y);
        }

        placed_row.pos.y = cursor_y;
        row.size.y = max_row_height;

        cursor_y += max_row_height;
        cursor_y = point_scale.round_to_pixel(cursor_y); // TODO(emilk): it would be better to do the calculations in pixels instead.
    }

    let format_summary = format_summary(&job);

    let mut rect = Rect::ZERO;
    let mut mesh_bounds = Rect::NOTHING;
    let mut num_vertices = 0;
    let mut num_indices = 0;

    for placed_row in &mut rows {
        rect |= placed_row.rect();

        let row = Arc::make_mut(&mut placed_row.row);
        row.visuals = tessellate_row(point_scale, &job, &format_summary, row);

        mesh_bounds |= row.visuals.mesh_bounds.translate(placed_row.pos.to_vec2());
        num_vertices += row.visuals.mesh.vertices.len();
        num_indices += row.visuals.mesh.indices.len();

        row.section_index_at_start = u32::MAX; // No longer in use.
        for glyph in &mut row.glyphs {
            glyph.section_index = u32::MAX; // No longer in use.
        }
    }

    let mut galley = Galley {
        job,
        rows,
        elided,
        rect,
        mesh_bounds,
        num_vertices,
        num_indices,
        pixels_per_point: point_scale.pixels_per_point,
        intrinsic_size,
    };

    if galley.job.round_output_to_gui {
        galley.round_output_to_gui();
    }

    galley
}

#[derive(Default)]
struct FormatSummary {
    any_background: bool,
    any_underline: bool,
    any_strikethrough: bool,
}

fn format_summary(job: &LayoutJob) -> FormatSummary {
    let mut format_summary = FormatSummary::default();
    for section in &job.sections {
        format_summary.any_background |= section.format.background != Color32::TRANSPARENT;
        format_summary.any_underline |= section.format.underline != Stroke::NONE;
        format_summary.any_strikethrough |= section.format.strikethrough != Stroke::NONE;
    }
    format_summary
}

fn tessellate_row(
    point_scale: PointScale,
    job: &LayoutJob,
    format_summary: &FormatSummary,
    row: &mut Row,
) -> RowVisuals {
    if row.glyphs.is_empty() {
        return Default::default();
    }

    let mut mesh = Mesh::default();

    mesh.reserve_triangles(row.glyphs.len() * 2);
    mesh.reserve_vertices(row.glyphs.len() * 4);

    if format_summary.any_background {
        add_row_backgrounds(point_scale, job, row, &mut mesh);
    }

    let glyph_index_start = mesh.indices.len();
    let glyph_vertex_start = mesh.vertices.len();
    tessellate_glyphs(point_scale, job, row, &mut mesh);
    let glyph_vertex_end = mesh.vertices.len();

    if format_summary.any_underline {
        add_row_hline(point_scale, row, &mut mesh, |glyph| {
            let format = &job.sections[glyph.section_index as usize].format;
            let stroke = format.underline;
            let y = glyph.logical_rect().bottom();
            (stroke, y)
        });
    }

    if format_summary.any_strikethrough {
        add_row_hline(point_scale, row, &mut mesh, |glyph| {
            let format = &job.sections[glyph.section_index as usize].format;
            let stroke = format.strikethrough;
            let y = glyph.logical_rect().center().y;
            (stroke, y)
        });
    }

    let mesh_bounds = mesh.calc_bounds();

    RowVisuals {
        mesh,
        mesh_bounds,
        glyph_index_start,
        glyph_vertex_range: glyph_vertex_start..glyph_vertex_end,
    }
}

/// Create background for glyphs that have them.
/// Creates as few rectangular regions as possible.
fn add_row_backgrounds(point_scale: PointScale, job: &LayoutJob, row: &Row, mesh: &mut Mesh) {
    if row.glyphs.is_empty() {
        return;
    }

    let mut end_run = |run: Option<(Color32, Rect, f32)>| {
        if let Some((color, rect, expand)) = run {
            let rect = rect.expand(expand);
            let rect = rect.round_to_pixels(point_scale.pixels_per_point());
            mesh.add_colored_rect(rect, color);
        }
    };

    let mut run = None;
    for glyph in visual_glyphs(row) {
        let format = &job.sections[glyph.section_index as usize].format;
        let color = format.background;
        let rect = glyph.logical_rect();

        if color == Color32::TRANSPARENT {
            end_run(run.take());
        } else if let Some((existing_color, bounds, expand)) = run {
            if existing_color == color
                && bounds.top() == rect.top()
                && bounds.bottom() == rect.bottom()
                && format.expand_bg == expand
            {
                run = Some((color, bounds.union(rect), expand));
            } else {
                end_run(run.take());
                run = Some((color, rect, format.expand_bg));
            }
        } else {
            run = Some((color, rect, format.expand_bg));
        }
    }
    end_run(run);
}

fn tessellate_glyphs(point_scale: PointScale, job: &LayoutJob, row: &mut Row, mesh: &mut Mesh) {
    for glyph in &mut row.glyphs {
        glyph.first_vertex = mesh.vertices.len() as u32;
        let uv_rect = glyph.uv_rect;
        if !uv_rect.is_nothing() {
            let mut left_top = glyph.pos + uv_rect.offset;
            left_top.x = point_scale.round_to_pixel(left_top.x);
            left_top.y = point_scale.round_to_pixel(left_top.y);

            let rect = Rect::from_min_max(left_top, left_top + uv_rect.size);
            let uv = Rect::from_min_max(
                pos2(uv_rect.min[0] as f32, uv_rect.min[1] as f32),
                pos2(uv_rect.max[0] as f32, uv_rect.max[1] as f32),
            );

            let format = &job.sections[glyph.section_index as usize].format;

            let color = format.color;

            if format.italics {
                let idx = mesh.vertices.len() as u32;
                mesh.add_triangle(idx, idx + 1, idx + 2);
                mesh.add_triangle(idx + 2, idx + 1, idx + 3);

                let top_offset = rect.height() * 0.25 * Vec2::X;

                mesh.vertices.push(Vertex {
                    pos: rect.left_top() + top_offset,
                    uv: uv.left_top(),
                    color,
                });
                mesh.vertices.push(Vertex {
                    pos: rect.right_top() + top_offset,
                    uv: uv.right_top(),
                    color,
                });
                mesh.vertices.push(Vertex {
                    pos: rect.left_bottom(),
                    uv: uv.left_bottom(),
                    color,
                });
                mesh.vertices.push(Vertex {
                    pos: rect.right_bottom(),
                    uv: uv.right_bottom(),
                    color,
                });
            } else {
                mesh.add_rect_with_uv(rect, uv, color);
            }
        }
    }
}

/// Add a horizontal line over a row of glyphs with a stroke and y decided by a callback.
fn add_row_hline(
    point_scale: PointScale,
    row: &Row,
    mesh: &mut Mesh,
    stroke_and_y: impl Fn(&Glyph) -> (Stroke, f32),
) {
    let mut path = crate::tessellator::Path::default(); // reusing path to avoid re-allocations.

    let mut end_line = |line: Option<(Stroke, Pos2, f32)>| {
        if let Some((stroke, start, right)) = line {
            let stop = pos2(right, start.y);
            path.clear();
            path.add_line_segment([start, stop]);
            let feathering = 1.0 / point_scale.pixels_per_point();
            path.stroke_open(feathering, &PathStroke::from(stroke), mesh);
        }
    };

    let mut line = None;
    for glyph in visual_glyphs(row) {
        let (stroke, mut y) = stroke_and_y(glyph);
        stroke.round_center_to_pixel(point_scale.pixels_per_point, &mut y);

        if stroke.is_empty() {
            end_line(line.take());
        } else if let Some((existing_stroke, start, right)) = line {
            if existing_stroke == stroke && start.y == y {
                line = Some((
                    stroke,
                    pos2(start.x.min(glyph.pos.x), y),
                    right.max(glyph.max_x()),
                ));
            } else {
                end_line(line.take());
                line = Some((stroke, pos2(glyph.pos.x, y), glyph.max_x()));
            }
        } else {
            line = Some((stroke, pos2(glyph.pos.x, y), glyph.max_x()));
        }
    }
    end_line(line);
}

// ----------------------------------------------------------------------------

/// Keeps track of good places to break a long row of text.
/// Will focus primarily on spaces, secondarily on things like `-`
#[derive(Clone, Copy, Default)]
struct RowBreakCandidates {
    /// Breaking at ` ` or other whitespace
    /// is always the primary candidate.
    space: Option<usize>,

    /// Logograms (single character representing a whole word) or kana (Japanese hiragana and katakana) are good candidates for line break.
    cjk: Option<usize>,

    /// Breaking anywhere before a CJK character is acceptable too.
    pre_cjk: Option<usize>,

    /// Breaking at a dash is a super-
    /// good idea.
    dash: Option<usize>,

    /// This is nicer for things like URLs, e.g. www.
    /// example.com.
    punctuation: Option<usize>,

    /// Breaking after just random character is some
    /// times necessary.
    any: Option<usize>,
}

impl RowBreakCandidates {
    fn add(&mut self, index: usize, glyphs: &[Glyph]) {
        if glyphs.get(1).is_some_and(|next| next.cluster_continuation) {
            return;
        }
        let Some(first) = glyphs.first() else {
            return;
        };
        let chr = first.chr;
        const NON_BREAKING_SPACE: char = '\u{A0}';
        if chr.is_whitespace() && chr != NON_BREAKING_SPACE {
            self.space = Some(index);
        } else if is_cjk(chr) && (glyphs.len() == 1 || is_cjk_break_allowed(glyphs[1].chr)) {
            self.cjk = Some(index);
        } else if chr == '-' {
            self.dash = Some(index);
        } else if chr.is_ascii_punctuation() {
            self.punctuation = Some(index);
        } else if glyphs.len() > 1 && is_cjk(glyphs[1].chr) {
            self.pre_cjk = Some(index);
        }
        self.any = Some(index);
    }

    fn word_boundary(&self) -> Option<usize> {
        [self.space, self.cjk, self.pre_cjk]
            .into_iter()
            .max()
            .flatten()
    }

    fn has_good_candidate(&self, break_anywhere: bool) -> bool {
        if break_anywhere {
            self.any.is_some()
        } else {
            self.word_boundary().is_some()
        }
    }

    fn get(&self, break_anywhere: bool) -> Option<usize> {
        if break_anywhere {
            self.any
        } else {
            self.word_boundary()
                .or(self.dash)
                .or(self.punctuation)
                .or(self.any)
        }
    }

    fn forget_before_idx(&mut self, index: usize) {
        let Self {
            space,
            cjk,
            pre_cjk,
            dash,
            punctuation,
            any,
        } = self;
        if space.is_some_and(|s| s < index) {
            *space = None;
        }
        if cjk.is_some_and(|s| s < index) {
            *cjk = None;
        }
        if pre_cjk.is_some_and(|s| s < index) {
            *pre_cjk = None;
        }
        if dash.is_some_and(|s| s < index) {
            *dash = None;
        }
        if punctuation.is_some_and(|s| s < index) {
            *punctuation = None;
        }
        if any.is_some_and(|s| s < index) {
            *any = None;
        }
    }
}

// ----------------------------------------------------------------------------

/// Segment text into runs where each run uses a single font face.
///
/// Grapheme clusters are never split across runs: if a combining mark
/// falls back to a different font than its base character, it stays
/// with the base character's font (the shaper will handle it).
///
/// Runs share a font face, bidi level, and Unicode script. Common and inherited
/// characters join the surrounding script so punctuation and marks keep context.
///
/// Results are appended to `out` (which is cleared first) to allow
/// the caller to reuse the allocation across calls.
fn segment_into_runs(
    font: &mut Font<'_>,
    text: &str,
    levels: &[unicode_bidi::Level],
    out: &mut Vec<TextRun>,
) {
    use unicode_script::{Script, UnicodeScript as _};
    use unicode_segmentation::UnicodeSegmentation as _;

    out.clear();

    for (byte_offset, grapheme_str) in text.grapheme_indices(true) {
        let bidi_level = levels.get(byte_offset).map_or(0, |level| level.number());
        let byte_offset = ByteIndex(byte_offset);
        let byte_end = byte_offset + grapheme_str.len();

        let base_char = grapheme_str.chars().next().unwrap_or(' ');
        let font_key = font.resolve_face(base_char);
        let script = base_char.script();
        let weak_script = matches!(script, Script::Common | Script::Inherited);

        if let Some(last_run) = out.last_mut()
            && last_run.font_key == font_key
            && last_run.bidi_level == bidi_level
            && (weak_script
                || last_run.script == script
                || matches!(last_run.script, Script::Common | Script::Inherited))
        {
            if !weak_script {
                last_run.script = script;
            }
            last_run.byte_range.end = byte_end;
            continue;
        }
        out.push(TextRun {
            font_key,
            byte_range: byte_offset..byte_end,
            script,
            bidi_level,
        });
    }
}

fn visual_glyphs(row: &Row) -> Vec<&Glyph> {
    let mut glyphs: Vec<_> = row.glyphs.iter().collect();
    glyphs.sort_by(|a, b| a.pos.x.total_cmp(&b.pos.x));
    glyphs
}

fn glyph_clusters(row: &Row) -> Vec<Range<usize>> {
    let mut blocks: Vec<Range<usize>> = Vec::new();
    for (i, glyph) in row.glyphs.iter().enumerate() {
        if glyph.cluster_continuation
            && let Some(block) = blocks.last_mut()
        {
            block.end = i + 1;
        } else {
            blocks.push(i..i + 1);
        }
    }
    blocks
}

/// Reposition complete shaped clusters while retaining logical character indices.
fn reorder_row_visually(scale: PointScale, row: &mut Row) {
    if !row.glyphs.iter().any(Glyph::is_rtl) {
        return;
    }
    let blocks = glyph_clusters(row);
    let levels: Vec<_> = blocks
        .iter()
        .filter_map(|block| row.glyphs.get(block.start))
        .map(|g| {
            unicode_bidi::Level::new(g.bidi_level).unwrap_or_else(|_| unicode_bidi::Level::ltr())
        })
        .collect();
    let origins: Vec<_> = blocks
        .iter()
        .filter_map(|block| row.glyphs.get(block.start))
        .map(|g| g.pos.x)
        .collect();
    let mut pen = origins.first().copied().unwrap_or(0.0);
    for index in unicode_bidi::BidiInfo::reorder_visual(&levels) {
        let Some(block) = blocks.get(index) else {
            continue;
        };
        let Some(&origin) = origins.get(index) else {
            continue;
        };
        let Some(glyphs) = row.glyphs.get_mut(block.clone()) else {
            continue;
        };
        let width = origins
            .get(index + 1)
            .copied()
            .unwrap_or_else(|| glyphs.iter().map(Glyph::max_x).fold(origin, f32::max))
            - origin;
        let cluster_width: f32 = glyphs.iter().map(|g| g.advance_width).sum();
        for glyph in glyphs {
            let logical_offset = glyph.pos.x - origin;
            let visual_offset = if glyph.is_rtl() {
                cluster_width - logical_offset - glyph.advance_width
            } else {
                logical_offset
            };
            // Character boxes follow reading direction; the combined bitmap
            // stays anchored to the cluster origin, including every mark offset.
            if !glyph.uv_rect.is_nothing() {
                glyph.uv_rect.offset.x += logical_offset - visual_offset;
            }
            glyph.pos.x = scale.round_to_pixel(pen + visual_offset);
        }
        pen += width;
    }
}

/// Shape a text run and return the raw [`harfrust::GlyphBuffer`].
///
/// The caller should iterate `glyph_infos()` / `glyph_positions()` (both
/// `Copy` slices) and convert font units to pixels using `metrics.px_scale_factor`.
/// After iteration, recycle the buffer via `glyph_buffer.clear()`.
fn shape_text(
    font_face: &FontFace,
    text: &str,
    coords: &VariationCoords,
    mut buffer: harfrust::UnicodeBuffer,
    flags: harfrust::BufferFlags,
) -> harfrust::GlyphBuffer {
    let font_ref = font_face.skrifa_font_ref();
    let tweak = font_face.tweak();

    // Build shaper with variable font instance if variation coordinates are set.
    let variations: Vec<harfrust::Variation> = iter::chain(tweak.coords.as_ref(), coords.as_ref())
        .map(|&(tag, value)| harfrust::Variation { tag, value })
        .collect();

    let instance = if variations.is_empty() {
        None
    } else {
        Some(harfrust::ShaperInstance::from_variations(
            font_ref, variations,
        ))
    };

    let shaper = font_face
        .shaper_data()
        .shaper(font_ref)
        .instance(instance.as_ref())
        .build();

    buffer.set_flags(flags);
    buffer.push_str(text);
    buffer.guess_segment_properties();

    shaper.shape(buffer, harfrust::ShapeOptions::new())
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use core::iter;

    use super::{super::*, *};
    use crate::text::cursor::CCursor;

    #[test]
    fn test_zero_max_width() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let mut layout_job = LayoutJob::single_section("W".into(), TextFormat::default());
        layout_job.wrap.max_width = 0.0;
        let galley = layout(&mut fonts, pixels_per_point, layout_job.into());
        assert_eq!(galley.rows.len(), 1);
    }

    #[test]
    fn test_truncate_with_newline() {
        // No matter where we wrap, we should be appending the newline character.

        let pixels_per_point = 1.0;

        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let text_format = TextFormat {
            font_id: FontId::monospace(12.0),
            ..Default::default()
        };

        for text in ["Hello\nworld", "\nfoo"] {
            for break_anywhere in [false, true] {
                for max_width in [0.0, 5.0, 10.0, 20.0, f32::INFINITY] {
                    let mut layout_job =
                        LayoutJob::single_section(text.into(), text_format.clone());
                    layout_job.wrap.max_width = max_width;
                    layout_job.wrap.max_rows = 1;
                    layout_job.wrap.break_anywhere = break_anywhere;

                    let galley = layout(&mut fonts, pixels_per_point, layout_job.into());

                    assert!(galley.elided);
                    assert_eq!(galley.rows.len(), 1);
                    let row_text = galley.rows[0].text();
                    assert!(
                        row_text.ends_with('…'),
                        "Expected row to end with `…`, got {row_text:?} when line-breaking the text {text:?} with max_width {max_width} and break_anywhere {break_anywhere}.",
                    );
                }
            }
        }

        {
            let mut layout_job = LayoutJob::single_section("Hello\nworld".into(), text_format);
            layout_job.wrap.max_width = 50.0;
            layout_job.wrap.max_rows = 1;
            layout_job.wrap.break_anywhere = false;

            let galley = layout(&mut fonts, pixels_per_point, layout_job.into());

            assert!(galley.elided);
            assert_eq!(galley.rows.len(), 1);
            let row_text = galley.rows[0].text();
            assert_eq!(row_text, "Hello…");
        }
    }

    #[test]
    fn test_cjk() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let mut layout_job = LayoutJob::single_section(
            "日本語とEnglishの混在した文章".into(),
            TextFormat::default(),
        );
        layout_job.wrap.max_width = 90.0;
        let galley = layout(&mut fonts, pixels_per_point, layout_job.into());
        assert_eq!(
            galley.rows.iter().map(|row| row.text()).collect::<Vec<_>>(),
            vec!["日本語と", "Englishの混在", "した文章"]
        );
    }

    #[test]
    fn test_pre_cjk() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let mut layout_job = LayoutJob::single_section(
            "日本語とEnglishの混在した文章".into(),
            TextFormat::default(),
        );
        layout_job.wrap.max_width = 110.0;
        let galley = layout(&mut fonts, pixels_per_point, layout_job.into());
        assert_eq!(
            galley.rows.iter().map(|row| row.text()).collect::<Vec<_>>(),
            vec!["日本語とEnglish", "の混在した文章"]
        );
    }

    #[test]
    fn test_truncate_width() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let mut layout_job =
            LayoutJob::single_section("# DNA\nMore text".into(), TextFormat::default());
        layout_job.wrap.max_width = f32::INFINITY;
        layout_job.wrap.max_rows = 1;
        layout_job.round_output_to_gui = false;
        let galley = layout(&mut fonts, pixels_per_point, layout_job.into());
        assert!(galley.elided);
        assert_eq!(
            galley.rows.iter().map(|row| row.text()).collect::<Vec<_>>(),
            vec!["# DNA…"]
        );
        let row = &galley.rows[0];
        assert_eq!(row.pos, Pos2::ZERO);
        assert_eq!(row.rect().max.x, row.glyphs.last().unwrap().max_x());
    }

    #[test]
    fn test_truncate_with_pixels_per_point() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        for pixels_per_point in [
            0.33, 0.5, 0.67, 1.0, 1.25, 1.33, 1.5, 1.75, 2.0, 3.0, 4.0, 5.0,
        ] {
            for ch in ['W', 'A', 'n', 't', 'i'] {
                let target_width = 50.0;
                let text = (0..20).map(|_| ch).collect::<String>();

                let mut job = LayoutJob::single_section(text, TextFormat::default());
                job.wrap.max_width = target_width;
                job.wrap.max_rows = 1;
                let elided_galley = layout(&mut fonts, pixels_per_point, job.into());
                assert!(elided_galley.elided);

                let test_galley = layout(
                    &mut fonts,
                    pixels_per_point,
                    Arc::new(LayoutJob::single_section(
                        iter::chain(
                            (0..elided_galley.rows[0].char_count_excluding_newline().0).map(|_| ch),
                            iter::once('…'),
                        )
                        .collect::<String>(),
                        TextFormat::default(),
                    )),
                );

                assert!(elided_galley.size().x >= 0.0);
                assert!(elided_galley.size().x <= target_width);
                assert!(test_galley.size().x > target_width);
            }
        }
    }

    #[test]
    fn test_empty_row() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let font_id = FontId::default();
        let font_height = fonts
            .font(&font_id.family)
            .styled_metrics(pixels_per_point, font_id.size, &VariationCoords::default())
            .row_height;

        let job = LayoutJob::simple(String::new(), font_id, Color32::WHITE, f32::INFINITY);

        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 1, "Expected one row");
        assert_eq!(
            galley.rows[0].row.glyphs.len(),
            0,
            "Expected no glyphs in the empty row"
        );
        assert_eq!(
            galley.size(),
            Vec2::new(0.0, font_height.round()),
            "Unexpected galley size"
        );
        assert_eq!(
            galley.intrinsic_size(),
            Vec2::new(0.0, font_height.round()),
            "Unexpected intrinsic size"
        );
    }

    #[test]
    fn test_end_with_newline() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let font_id = FontId::default();
        let font_height = fonts
            .font(&font_id.family)
            .styled_metrics(pixels_per_point, font_id.size, &VariationCoords::default())
            .row_height;

        let job = LayoutJob::simple("Hi!\n".to_owned(), font_id, Color32::WHITE, f32::INFINITY);

        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 2, "Expected two rows");
        assert_eq!(
            galley.rows[1].row.glyphs.len(),
            0,
            "Expected no glyphs in the empty row"
        );
        assert_eq!(
            galley.size().round(),
            Vec2::new(17.0, font_height.round() * 2.0),
            "Unexpected galley size"
        );
        assert_eq!(
            galley.intrinsic_size().round(),
            Vec2::new(17.0, font_height.round() * 2.0),
            "Unexpected intrinsic size"
        );
    }

    #[test]
    fn test_combining_diacritics() {
        // ɔ̃ = U+0254 (LATIN SMALL LETTER OPEN O) + U+0303 (COMBINING TILDE)
        // With text shaping, the combining tilde should NOT produce a separate
        // advance — it should be positioned above ɔ via GPOS anchors.
        // Note: the default fonts don't contain U+0254, so the replacement glyph
        // is used. The key test is that the combining mark does NOT add extra width.
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let job_combined = LayoutJob::simple(
            "ɔ\u{0303}".to_owned(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley_combined = layout(&mut fonts, pixels_per_point, job_combined.into());

        let job_base = LayoutJob::simple(
            "ɔ".to_owned(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley_base = layout(&mut fonts, pixels_per_point, job_base.into());

        let width_combined = galley_combined.size().x;
        let width_base = galley_base.size().x;

        assert!(
            (width_combined - width_base).abs() < 2.0,
            "Combining diacritic should not add significant width. \
             Base width: {width_base}, Combined width: {width_combined}"
        );

        let glyphs = &galley_combined.rows[0].row.glyphs;
        assert!(!glyphs.is_empty(), "Expected at least 1 glyph for ɔ̃");
    }

    fn bidi_layout(
        fonts: &mut FontsImpl,
        text: &str,
        width: f32,
        direction: TextDirection,
    ) -> Galley {
        let mut job = LayoutJob::simple(
            text.into(),
            FontId::proportional(24.0),
            Color32::WHITE,
            width,
        );
        job.direction = direction;
        layout(fonts, 1.0, job.into())
    }

    #[test]
    fn bidi_visual_digits_carets_selection_and_wrap() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let galley = bidi_layout(&mut fonts, "אב 12", f32::INFINITY, TextDirection::Auto);
        let row = &galley.rows[0];
        let visual: String = visual_glyphs(row).iter().map(|g| g.chr).collect();
        assert_eq!(visual, "12 בא");
        assert_eq!(row.x_offset(CharIndex(0)), row.glyphs[0].max_x());
        assert_eq!(row.x_offset(CharIndex(5)), row.glyphs[4].max_x());
        assert_eq!(
            row.selection_x_ranges(0..1),
            vec![row.glyphs[0].pos.x..row.glyphs[0].max_x()]
        );
        let left = galley.cursor_left_one_character(&CCursor::new(0));
        assert_eq!(left.index, CharIndex(1));
        assert_eq!(galley.cursor_right_one_character(&left).index, CharIndex(0));
        let mixed = bidi_layout(&mut fonts, "ab אב cd", f32::INFINITY, TextDirection::Auto);
        let row = &mixed.rows[0];
        let selected = row.selection_x_ranges(1..4);
        assert_eq!(
            selected.len(),
            2,
            "logical selection must omit unselected bet"
        );
        assert!(
            selected
                .iter()
                .all(|span| span.end <= row.glyphs[4].pos.x || span.start >= row.glyphs[4].max_x()),
            "{selected:?}, {:?}",
            row.glyphs
        );
        for width in [25.0, 50.0, 100.0] {
            let wrapped = bidi_layout(&mut fonts, "אב 12 גד 34", width, TextDirection::Auto);
            assert_eq!(
                wrapped.rows.iter().map(|r| r.text()).collect::<String>(),
                "אב 12 גד 34"
            );
            assert!(
                wrapped
                    .rows
                    .iter()
                    .all(|r| r.glyphs.iter().all(|g| g.pos.x.is_finite()))
            );
        }
    }

    #[test]
    fn bidi_parentheses_use_mirrored_glyphs() {
        let mut fonts = FontsImpl::new(
            TextOptions {
                subpixel_binning: false,
                ..Default::default()
            },
            FontDefinitions::default(),
        );
        let mixed = bidi_layout(&mut fonts, "אב (12)", f32::INFINITY, TextDirection::Auto);
        let right = bidi_layout(&mut fonts, ")", f32::INFINITY, TextDirection::LeftToRight);
        let left = bidi_layout(&mut fonts, "(", f32::INFINITY, TextDirection::LeftToRight);
        assert_eq!(
            mixed.rows[0].glyphs[3].uv_rect,
            right.rows[0].glyphs[0].uv_rect
        );
        assert_eq!(
            mixed.rows[0].glyphs[6].uv_rect,
            left.rows[0].glyphs[0].uv_rect
        );
    }

    #[test]
    fn bidi_run_boundary_has_two_hit_testable_caret_positions() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let galley = bidi_layout(&mut fonts, "ab אב cd", f32::INFINITY, TextDirection::Auto);
        let upstream = CCursor {
            index: CharIndex(3),
            prefer_next_row: false,
        };
        let downstream = CCursor {
            index: CharIndex(3),
            prefer_next_row: true,
        };
        let before = galley.pos_from_cursor(upstream).center();
        let after = galley.pos_from_cursor(downstream).center();
        assert!(after.x > before.x + 10.0);
        for position in [before, after] {
            let hit = galley.cursor_from_pos(position.to_vec2());
            assert!((galley.pos_from_cursor(hit).center().x - position.x).abs() < 0.01);
        }
        for cursor in [upstream, downstream] {
            let left = galley.cursor_left_one_character(&cursor);
            let back = galley.cursor_right_one_character(&left);
            assert_eq!(back.index, cursor.index);
            assert_eq!(back.prefer_next_row, cursor.prefer_next_row);
        }
        let wrapped = bidi_layout(&mut fonts, "אב גד הו", 50.0, TextDirection::Auto);
        assert!(wrapped.rows.len() > 1);
        let first = &wrapped.rows[0];
        let at_left = wrapped.cursor_from_pos(vec2(0.0, first.rect().center().y));
        let next = wrapped.cursor_left_one_character(&at_left);
        assert_eq!(wrapped.layout_from_cursor(next).row, 1);
    }

    #[test]
    fn bidi_empty_fonts_and_elision_never_slice_inside_a_character() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::empty());
        for text in ["مرحبا\nاب", "مَرْحَبًا\n", "אב\nمرحبا"] {
            let _ = bidi_layout(&mut fonts, text, 20.0, TextDirection::Auto);
        }
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let mut job = LayoutJob::simple(
            "مرحبا بالعالم".into(),
            FontId::proportional(24.0),
            Color32::WHITE,
            60.0,
        );
        job.wrap.max_rows = 1;
        let galley = layout(&mut fonts, 1.0, job.into());
        assert!(galley.elided);
        assert!(
            galley.rows[0].glyphs.first().unwrap().pos.x
                >= galley.rows[0].glyphs.last().unwrap().pos.x
        );
    }

    #[test]
    fn bidi_explicit_direction_and_trailing_whitespace() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let ltr = bidi_layout(
            &mut fonts,
            "12 אב",
            f32::INFINITY,
            TextDirection::LeftToRight,
        );
        let rtl = bidi_layout(
            &mut fonts,
            "12 אב",
            f32::INFINITY,
            TextDirection::RightToLeft,
        );
        assert_eq!(
            visual_glyphs(&ltr.rows[0])
                .iter()
                .map(|g| g.chr)
                .collect::<String>(),
            "12 בא"
        );
        assert_eq!(
            visual_glyphs(&rtl.rows[0])
                .iter()
                .map(|g| g.chr)
                .collect::<String>(),
            "בא 12"
        );
        let galley = bidi_layout(&mut fonts, "אב 12   ", 65.0, TextDirection::LeftToRight);
        for row in &galley.rows {
            for g in row
                .glyphs
                .iter()
                .rev()
                .take_while(|g| g.chr.is_whitespace())
            {
                assert_eq!(
                    g.bidi_level, 0,
                    "UAX9 L1 resets each wrapped line's trailing spaces"
                );
            }
        }
    }

    #[test]
    #[ignore = "requires CRAFT_FONTS_DIR with the licensed Noto Sans Arabic font"]
    fn bidi_arabic_real_font_clusters() {
        let path = std::path::PathBuf::from(
            std::env::var_os("CRAFT_FONTS_DIR").expect("set CRAFT_FONTS_DIR"),
        )
        .join("fonts/noto-sans-arabic/NotoSansArabic.ttf");
        let mut definitions = FontDefinitions::default();
        definitions.font_data.insert(
            "arabic".into(),
            Arc::new(FontData::from_owned(
                std::fs::read(path).expect("Noto font"),
            )),
        );
        definitions
            .families
            .get_mut(&FontFamily::Proportional)
            .unwrap()
            .insert(0, "arabic".into());
        let mut fonts = FontsImpl::new(TextOptions::default(), definitions);
        for text in [
            "ب",
            "ببب",
            "العربية",
            "السَّلَامُ",
            "لا",
            "مَرْحَبًا 123 (ABC)",
            "abc العربية ١٢٣",
            "بَتُثِ",
            "دَرْس",
            "x لا y",
        ] {
            for width in [30.0, 75.0, f32::INFINITY] {
                let galley = bidi_layout(&mut fonts, text, width, TextDirection::Auto);
                assert_eq!(
                    galley.rows.iter().map(|r| r.text()).collect::<String>(),
                    text
                );
                assert_eq!(galley.end().index.0, text.chars().count());
                for row in &galley.rows {
                    assert!(!row.glyphs.first().is_some_and(|g| g.cluster_continuation));
                    for (index, glyph) in row.glyphs.iter().enumerate() {
                        if glyph.cluster_continuation {
                            assert!(glyph.uv_rect.is_nothing());
                            assert!(index > 0);
                        } else if glyph.chr.is_alphabetic() {
                            assert!(
                                !glyph.uv_rect.is_nothing(),
                                "visible real Arabic glyph {glyph:?}"
                            );
                        }
                    }
                }
            }
        }
        for text in ["د", "دَ", "دَرْس", "مَرْحَبًا", "abc دَرْس xyz"] {
            let mut job = LayoutJob::simple(
                text.into(),
                FontId::proportional(24.0),
                Color32::WHITE,
                f32::INFINITY,
            );
            let format = &mut job.sections[0].format;
            format.background = Color32::RED;
            format.expand_bg = 0.0;
            format.underline = Stroke::new(2.0, Color32::GREEN);
            format.strikethrough = Stroke::new(2.0, Color32::BLUE);
            let decorated = layout(&mut fonts, 1.0, job.into());
            let row = &decorated.rows[0];
            let left = row
                .glyphs
                .iter()
                .map(|g| g.logical_rect().left())
                .reduce(f32::min)
                .unwrap();
            let right = row
                .glyphs
                .iter()
                .map(|g| g.logical_rect().right())
                .reduce(f32::max)
                .unwrap();
            for color in [Color32::RED, Color32::GREEN, Color32::BLUE] {
                let vertices: Vec<_> = row
                    .visuals
                    .mesh
                    .vertices
                    .iter()
                    .filter(|v| v.color == color)
                    .collect();
                let painted_left = vertices.iter().map(|v| v.pos.x).reduce(f32::min).unwrap();
                let painted_right = vertices.iter().map(|v| v.pos.x).reduce(f32::max).unwrap();
                assert!(
                    painted_left <= left + 0.5 && painted_right >= right - 0.5,
                    "{text:?} decoration {color:?} covers {painted_left}..{painted_right}, expected {left}..{right}"
                );
                assert!(
                    painted_left >= left - 2.0 && painted_right <= right + 2.0,
                    "decoration must stay within its run, including stroke feathering"
                );
            }
        }
        let unspaced = bidi_layout(&mut fonts, "دَرْس لا", f32::INFINITY, TextDirection::Auto);
        let mut justified = unspaced.rows[0].clone();
        halign_and_justify_row(
            PointScale::new(1.0),
            &mut justified,
            Align::LEFT,
            300.0,
            true,
            false,
        );
        assert_eq!(justified.size.x, 300.0);
        for cluster in glyph_clusters(&unspaced.rows[0]) {
            let original = &unspaced.rows[0].glyphs[cluster.clone()];
            let spaced = &justified.glyphs[cluster];
            let shift = spaced[0].pos.x - original[0].pos.x;
            for (before, after) in original.iter().zip(spaced) {
                assert!(
                    (after.pos.x - before.pos.x - shift).abs() < 0.001,
                    "justification must keep marks and ligature characters in their shaped cluster"
                );
                assert_eq!(before.advance_width, after.advance_width);
                assert_eq!(before.uv_rect, after.uv_rect);
            }
        }
        let marked_word = bidi_layout(&mut fonts, "دَرْس", f32::INFINITY, TextDirection::Auto);
        let first_step = marked_word.cursor_left_one_character(&CCursor::new(0));
        assert_eq!(
            first_step.index.0, 2,
            "arrow movement keeps a base and its mark together"
        );
        assert_eq!(
            marked_word
                .cursor_left_one_character(&CCursor::new(1))
                .index
                .0,
            2
        );
        assert_eq!(
            marked_word
                .cursor_right_one_character(&CCursor::new(1))
                .index
                .0,
            0
        );
        let second_step = marked_word.cursor_left_one_character(&first_step);
        assert_eq!(second_step.index.0, 4);
        // A mark and its base share one bitmap. Its ink must remain attached when reordering.
        let bare = bidi_layout(&mut fonts, "د", f32::INFINITY, TextDirection::Auto);
        let marked = bidi_layout(&mut fonts, "دَ", f32::INFINITY, TextDirection::Auto);
        assert_eq!(marked.rows[0].glyphs.len(), 2);
        assert!(marked.rows[0].glyphs[1].cluster_continuation);
        assert!(marked.rows[0].glyphs[0].uv_rect.size.y > bare.rows[0].glyphs[0].uv_rect.size.y);
        assert_eq!(
            marked.rows[0].glyphs[0].advance_width,
            bare.rows[0].glyphs[0].advance_width
        );
        assert_eq!(
            marked.rows[0].x_offset(CharIndex(2)),
            marked.rows[0].glyphs[0].pos.x
        );
    }

    #[test]
    fn bidi_preserves_logical_text() {
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        for text in ["اب 12", "a אבג b", "אב"] {
            let job = LayoutJob::simple(
                text.into(),
                FontId::proportional(18.0),
                Color32::WHITE,
                f32::INFINITY,
            );
            let galley = layout(&mut fonts, 1.0, job.into());
            assert_eq!(galley.rows[0].text(), text);
        }
    }

    #[test]
    fn test_shaping_basic_latin() {
        // Basic test: shaped Latin text should produce the same number of glyphs as characters.
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let job = LayoutJob::simple(
            "Hello".to_owned(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 1);
        assert_eq!(galley.rows[0].row.glyphs.len(), 5);
        assert!(galley.size().x > 0.0);
    }

    #[test]
    fn test_shaping_empty_string() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let job = LayoutJob::simple(
            String::new(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 1);
        assert_eq!(galley.rows[0].row.glyphs.len(), 0);
    }

    #[test]
    fn test_shaping_multiple_newlines() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let job = LayoutJob::simple(
            "A\n\nB".to_owned(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 3, "Expected 3 rows for 'A\\n\\nB'");
        assert_eq!(galley.rows[0].row.glyphs.len(), 1); // "A"
        assert_eq!(galley.rows[1].row.glyphs.len(), 0); // empty line
        assert_eq!(galley.rows[2].row.glyphs.len(), 1); // "B"
    }

    #[test]
    fn test_shaping_mixed_font_fallback() {
        // Text with both Latin and emoji should work without panicking,
        // even though they use different font faces.
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());

        let job = LayoutJob::simple(
            "Hi 🎉 bye".to_owned(),
            FontId::proportional(14.0),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(&mut fonts, pixels_per_point, job.into());

        assert_eq!(galley.rows.len(), 1);
        // "Hi " (3) + "🎉" (1) + " bye" (4) = at least 8 glyphs
        assert!(
            galley.rows[0].row.glyphs.len() >= 8,
            "Expected >= 8 glyphs, got {}",
            galley.rows[0].row.glyphs.len()
        );
    }

    #[test]
    fn test_gpos_kerning() {
        // GPOS kerning: pairs like "AV", "VA", "AT" should be tighter than
        // the sum of individual character widths. Without text shaping, egui
        // only uses the legacy `kern` table, so these pairs had diff ≈ 0.
        // With harfrust, GPOS kerning applies proper negative adjustments.
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let font_id = FontId::proportional(14.0);

        for pair in ["AV", "VA", "AT"] {
            let (pair_w, _, _) = measure_text(&mut fonts, pair, &font_id, pixels_per_point);
            let chars: Vec<char> = pair.chars().collect();
            let (w1, _, _) = measure_text(
                &mut fonts,
                &chars[0].to_string(),
                &font_id,
                pixels_per_point,
            );
            let (w2, _, _) = measure_text(
                &mut fonts,
                &chars[1].to_string(),
                &font_id,
                pixels_per_point,
            );
            let sum = w1 + w2;
            let kern_adjustment = sum - pair_w;

            assert!(
                kern_adjustment > 0.5,
                "GPOS kerning for '{pair}': expected pair to be noticeably tighter \
                 than sum of individuals. pair_width={pair_w:.2}, sum={sum:.2}, \
                 kern_adjustment={kern_adjustment:.2} (should be > 0.5)",
            );
        }
    }

    /// Regression test for <https://github.com/emilk/egui/issues/8087>.
    ///
    /// Multi-codepoint grapheme clusters (flag emojis, combining marks) must
    /// produce exactly as many glyphs as characters so that cursor positioning
    /// and text selection remain correct.
    #[test]
    fn test_grapheme_cluster_glyph_count() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let font_id = FontId::default();

        // Each test case: (input text, expected char count)
        let cases: &[(&str, usize)] = &[
            // Flag emoji: two Regional Indicator codepoints → one visual glyph
            ("\u{1F1EF}\u{1F1F5}", 2), // 🇯🇵
            // Flag surrounded by ASCII
            ("A\u{1F1EB}\u{1F1F7}B", 4), // A🇫🇷B
            // Base char + combining acute accent
            ("e\u{0301}", 2), // é as decomposed
            // Multiple combining marks
            ("o\u{0302}\u{0323}", 3), // ộ
            // Plain ASCII (sanity check)
            ("Hello", 5),
        ];

        for &(text, expected_chars) in cases {
            let job = LayoutJob::simple(
                text.to_owned(),
                font_id.clone(),
                Color32::WHITE,
                f32::INFINITY,
            );
            let galley = layout(&mut fonts, pixels_per_point, job.into());

            let total_glyphs: usize = galley.rows.iter().map(|r| r.row.glyphs.len()).sum();

            assert_eq!(
                total_glyphs,
                expected_chars,
                "Glyph count mismatch for {text:?}: \
                 expected {expected_chars} glyphs (one per char), got {total_glyphs}. \
                 Glyphs: {:?}",
                galley.rows[0]
                    .row
                    .glyphs
                    .iter()
                    .map(|g| (g.chr, g.advance_width))
                    .collect::<Vec<_>>(),
            );

            // Verify that Row::text() reconstructs the input text.
            let row_text: String = galley.rows.iter().map(|r| r.text()).collect();
            assert_eq!(row_text, text, "Row::text() mismatch for {text:?}");

            // Verify cursor round-trip: end cursor index == char count.
            assert_eq!(
                galley.end().index.0,
                expected_chars,
                "Galley::end().index mismatch for {text:?}",
            );
        }
    }

    /// Regression test for <https://github.com/emilk/egui/issues/8576>.
    ///
    /// The shaper returns a right-to-left run in visual order, with decreasing
    /// cluster offsets. Such a run must still produce one glyph per character.
    #[test]
    fn test_right_to_left_run_glyph_count() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let font_id = FontId::default();

        let cases = [
            "ب",
            "بب",
            "ببب",
            "אב",
            "a אבג b",
            "שלום 42 עולם",
            // Base char + combining mark inside a right-to-left run
            "ב\u{05BC}א",
        ];

        for text in cases {
            let job = LayoutJob::simple(
                text.to_owned(),
                font_id.clone(),
                Color32::WHITE,
                f32::INFINITY,
            );
            let galley = layout(&mut fonts, pixels_per_point, job.into());

            let total_glyphs: usize = galley.rows.iter().map(|r| r.row.glyphs.len()).sum();
            let num_chars = text.chars().count();

            assert_eq!(total_glyphs, num_chars, "Glyph count mismatch for {text:?}");
            assert_eq!(
                galley.end().index.0,
                num_chars,
                "Galley::end().index mismatch for {text:?}",
            );
        }
    }

    /// Verify that cursor positioning round-trips correctly for text
    /// containing multi-codepoint grapheme clusters (regression test for #8087).
    #[test]
    fn test_grapheme_cluster_cursor_roundtrip() {
        let pixels_per_point = 1.0;
        let mut fonts = FontsImpl::new(TextOptions::default(), FontDefinitions::default());
        let font_id = FontId::default();

        // "A" + flag emoji (2 codepoints) + "B" = 4 chars
        let text = "A\u{1F1EF}\u{1F1F5}B";
        let job = LayoutJob::simple(
            text.to_owned(),
            font_id.clone(),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(&mut fonts, pixels_per_point, job.into());

        // Walking through every cursor index should produce valid positions.
        for i in 0..=galley.end().index.0 {
            let cursor = CCursor {
                index: CharIndex(i),
                prefer_next_row: false,
            };
            let rect = galley.pos_from_cursor(cursor);
            assert!(
                rect.is_finite(),
                "pos_from_cursor returned non-finite rect for index {i}",
            );

            // Round-trip: position → cursor → position should be stable.
            let cursor2 = galley.cursor_from_pos(Vec2::new(rect.center().x, rect.center().y));
            let rect2 = galley.pos_from_cursor(cursor2);
            assert!(
                (rect.min.x - rect2.min.x).abs() < 1.0,
                "Cursor round-trip unstable at index {i}: \
                 first={}, second={}, cursor2.index={}",
                rect.min.x,
                rect2.min.x,
                cursor2.index,
            );
        }
    }

    fn measure_text(
        fonts: &mut FontsImpl,
        text: &str,
        font_id: &FontId,
        pixels_per_point: f32,
    ) -> (f32, usize, Vec<(char, f32)>) {
        let job = LayoutJob::simple(
            text.to_owned(),
            font_id.clone(),
            Color32::WHITE,
            f32::INFINITY,
        );
        let galley = layout(fonts, pixels_per_point, job.into());
        let glyphs = &galley.rows[0].row.glyphs;
        let details: Vec<_> = glyphs.iter().map(|g| (g.chr, g.advance_width)).collect();
        (galley.size().x, glyphs.len(), details)
    }
}
