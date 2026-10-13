use std::sync::Arc;

use emath::Pos2;
use epaint::{
    Stroke,
    text::{
        CharIndex,
        cursor::{CCursor, LayoutCursor},
    },
};

use crate::{
    Galley, Painter, Rect, Ui, Visuals, pos2, text_selection::text_cursor_state::cursor_rect, vec2,
};

use super::CCursorRange;

#[derive(Clone, Debug)]
pub struct RowVertexIndices {
    pub row: usize,
    pub vertex_indices: [u32; 6],
}

/// Adds text selection rectangles to the galley.
pub fn paint_text_selection(
    galley: &mut Arc<Galley>,
    visuals: &Visuals,
    cursor_range: &CCursorRange,
    mut new_vertex_indices: Option<&mut Vec<RowVertexIndices>>,
) {
    if cursor_range.is_empty() {
        return;
    }

    // We need to modify the galley (add text selection painting to it),
    // and so we need to clone it if it is shared:
    let galley: &mut Galley = Arc::make_mut(galley);

    let background_color = visuals.selection.bg_fill;
    let text_color = visuals.selection.stroke.color;

    let [min, max] = cursor_range.sorted_cursors();
    let min = galley.layout_from_cursor(min);
    let max = galley.layout_from_cursor(max);

    for ri in min.row..=max.row {
        let placed_row = &mut galley.rows[ri];
        let row = Arc::make_mut(&mut placed_row.row);

        let first_column = if ri == min.row { min.column.0 } else { 0 };
        let last_column = if ri == max.row {
            max.column.0
        } else {
            row.glyphs.len()
        };
        let mut ranges = row.selection_x_ranges(first_column..last_column);
        if ri < max.row && placed_row.ends_with_newline {
            let x = row.x_offset(row.char_count_excluding_newline());
            let width = row.height() / 2.0;
            ranges.push(if row.paragraph_level % 2 == 1 {
                x - width..x
            } else {
                x..x + width
            });
        }
        let mesh = &mut row.visuals.mesh;

        if !row.glyphs.is_empty() {
            // Change color of the selected text:
            let first_glyph_index = if ri == min.row { min.column.0 } else { 0 };
            let last_glyph_index = if ri == max.row {
                max.column.0
            } else {
                row.glyphs.len()
            };

            let first_vertex_index = row
                .glyphs
                .get(first_glyph_index)
                .map_or(row.visuals.glyph_vertex_range.end, |g| g.first_vertex as _);
            let last_vertex_index = row
                .glyphs
                .get(last_glyph_index)
                .map_or(row.visuals.glyph_vertex_range.end, |g| g.first_vertex as _);

            for vi in first_vertex_index..last_vertex_index {
                mesh.vertices[vi].color = text_color;
            }
        }

        for range in ranges {
            let rect = Rect::from_min_max(pos2(range.start, 0.0), pos2(range.end, row.size.y));
            let glyph_index_start = row.visuals.glyph_index_start;
            let num_indices_before = mesh.indices.len();
            mesh.add_colored_rect(rect, background_color);
            let mut selection_triangles = [0; 6];
            if let Some(indices) = mesh.indices.get(num_indices_before..) {
                selection_triangles.copy_from_slice(indices);
            }
            // Rotate the appended background triangles in front of the glyphs.
            if let Some(indices) = mesh.indices.get_mut(glyph_index_start..) {
                indices.rotate_right(6);
            }
            if let Some(new_vertex_indices) = &mut new_vertex_indices {
                new_vertex_indices.push(RowVertexIndices {
                    row: ri,
                    vertex_indices: selection_triangles,
                });
            }
        }
        row.visuals.mesh_bounds = mesh.calc_bounds();
    }
}

#[expect(clippy::too_many_arguments)]
pub(crate) fn paint_ime_preedit_text_visuals(
    pos: Pos2,
    ui: &Ui,
    painter: &Painter,
    galley: &Arc<Galley>,
    row_height: f32,
    preedit_range: core::ops::Range<CCursor>,
    mut relative_active_range: Option<core::ops::Range<CCursor>>,
    time_since_last_interaction: f64,
) {
    /// Instead of implementing [`PartialOrd`] and [`Ord`] for [`CCursor`] to
    /// make [`std::ops::Range::is_empty`] available, we use this helper
    /// function instead.
    ///
    /// These traits are intentionally not implemented because
    /// [`CCursor::prefer_next_row`] makes it difficult to define a clear
    /// ordering between two [`CCursor`]s.
    fn is_cursor_range_empty(range: &core::ops::Range<CCursor>) -> bool {
        range.start.index == range.end.index
    }

    if is_cursor_range_empty(&preedit_range) {
        return;
    }

    if let Some(relative_active_range) = &mut relative_active_range
        && relative_active_range.end.index > preedit_range.end.index - preedit_range.start.index
    {
        relative_active_range.end.index = preedit_range.end.index - preedit_range.start.index;
    }

    let visuals = ui.visuals();
    let active_underline_stroke = visuals.ime_composition.active_underline_stroke;
    let inactive_underline_stroke = visuals.ime_composition.inactive_underline_stroke;

    if let Some(relative_active_range) = &relative_active_range
        && !is_cursor_range_empty(relative_active_range)
    {
        if relative_active_range.start.index > CharIndex::ZERO {
            paint_underlines(
                pos,
                painter,
                galley,
                galley.layout_from_cursor(preedit_range.start),
                galley.layout_from_cursor(preedit_range.start + relative_active_range.start.index),
                inactive_underline_stroke,
            );
        }

        paint_underlines(
            pos,
            painter,
            galley,
            galley.layout_from_cursor(preedit_range.start + relative_active_range.start.index),
            galley.layout_from_cursor(preedit_range.start + relative_active_range.end.index),
            active_underline_stroke,
        );

        if !is_cursor_range_empty(
            &(relative_active_range.end..(preedit_range.end - preedit_range.start.index)),
        ) {
            paint_underlines(
                pos,
                painter,
                galley,
                galley.layout_from_cursor(preedit_range.start + relative_active_range.end.index),
                galley.layout_from_cursor(preedit_range.end),
                inactive_underline_stroke,
            );
        }
    } else {
        paint_underlines(
            pos,
            painter,
            galley,
            galley.layout_from_cursor(preedit_range.start),
            galley.layout_from_cursor(preedit_range.end),
            inactive_underline_stroke,
        );
    }

    if let Some(relative_active_range) = relative_active_range
        && is_cursor_range_empty(&relative_active_range)
    {
        let active_cursor = preedit_range.start + relative_active_range.start.index;
        let cursor_rect = cursor_rect(galley, &active_cursor, row_height);

        paint_text_cursor(
            ui,
            painter,
            cursor_rect.translate(pos.to_vec2()),
            time_since_last_interaction,
        );
    }
}

fn paint_underlines(
    pos: Pos2,
    painter: &Painter,
    galley: &Arc<Galley>,
    min: LayoutCursor,
    max: LayoutCursor,
    stroke: Stroke,
) {
    for ri in min.row..=max.row {
        let placed_row = &galley.rows[ri];
        let row = &placed_row.row;

        let start = if ri == min.row { min.column.0 } else { 0 };
        let end = if ri == max.row {
            max.column.0
        } else {
            row.glyphs.len()
        };
        let offset_y = placed_row.pos.y + row.size.y;
        for range in row.selection_x_ranges(start..end) {
            painter.line_segment(
                [
                    pos + vec2(range.start, offset_y),
                    pos + vec2(range.end, offset_y),
                ],
                stroke,
            );
        }
    }
}

/// Paint one end of the selection, e.g. the primary cursor.
///
/// This will never blink.
pub fn paint_cursor_end(painter: &Painter, visuals: &Visuals, cursor_rect: Rect) {
    let stroke = visuals.text_cursor.stroke;

    let top = cursor_rect.center_top();
    let bottom = cursor_rect.center_bottom();

    painter.line_segment([top, bottom], stroke);

    if false {
        // Roof/floor:
        let extrusion = 3.0;
        let width = 1.0;
        painter.line_segment(
            [top - vec2(extrusion, 0.0), top + vec2(extrusion, 0.0)],
            (width, stroke.color),
        );
        painter.line_segment(
            [bottom - vec2(extrusion, 0.0), bottom + vec2(extrusion, 0.0)],
            (width, stroke.color),
        );
    }
}

/// Paint one end of the selection, e.g. the primary cursor, with blinking (if enabled).
pub fn paint_text_cursor(
    ui: &Ui,
    painter: &Painter,
    primary_cursor_rect: Rect,
    time_since_last_interaction: f64,
) {
    if ui.visuals().text_cursor.blink {
        let on_duration = ui.visuals().text_cursor.on_duration;
        let off_duration = ui.visuals().text_cursor.off_duration;
        let total_duration = on_duration + off_duration;

        let time_in_cycle = (time_since_last_interaction % (total_duration as f64)) as f32;

        let wake_in = if time_in_cycle < on_duration {
            // Cursor is visible
            paint_cursor_end(painter, ui.visuals(), primary_cursor_rect);
            on_duration - time_in_cycle
        } else {
            // Cursor is not visible
            total_duration - time_in_cycle
        };

        ui.request_repaint_after_secs(wake_in);
    } else {
        paint_cursor_end(painter, ui.visuals(), primary_cursor_rect);
    }
}
