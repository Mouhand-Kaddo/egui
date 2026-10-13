use core::ops::Range;

use emath::TSTransform;
use epaint::text::{CharIndex, PlacedRow};

use crate::{Context, Galley, Id};

use super::CCursorRange;
use unicode_segmentation::UnicodeSegmentation as _;

/// AccessKit's `word_starts` uses `u8` indices, so text runs cannot exceed this length.
pub(crate) const MAX_CHARS_PER_TEXT_RUN: usize = 255;

/// Runs stay in logical source order. Each has one bidi level and bounded length.
pub(super) fn text_run_ranges(row: &PlacedRow) -> Vec<Range<usize>> {
    let mut ranges: Vec<Range<usize>> = Vec::new();
    let mut previous_level = row.paragraph_level;
    for index in 0..row.char_count_including_newline().0 {
        let level = row
            .glyphs
            .get(index)
            .map_or(row.paragraph_level, |g| g.bidi_level);
        if let Some(last) = ranges.last_mut()
            && level == previous_level
            && last.len() < MAX_CHARS_PER_TEXT_RUN
        {
            last.end = index + 1;
        } else {
            ranges.push(index..index + 1);
        }
        previous_level = level;
    }
    if ranges.is_empty() {
        ranges.push(0..0);
    }
    ranges
}

fn text_run_position(
    parent: Id,
    galley: &Galley,
    row: usize,
    column: CharIndex,
    prefer_next_run: bool,
) -> Option<accesskit::TextPosition> {
    let row_data = galley.rows.get(row)?;
    let ranges = text_run_ranges(row_data);
    for (chunk, range) in ranges.iter().enumerate() {
        if range.start <= column.0
            && column.0 <= range.end
            && (column.0 < range.end || !prefer_next_run || chunk + 1 == ranges.len())
        {
            return Some(accesskit::TextPosition {
                node: parent.with(row).with(chunk).accesskit_id(),
                character_index: column.0 - range.start,
            });
        }
    }
    None
}

/// Update AccessKit with logical text and the visual geometry of each directional run.
pub fn update_accesskit_for_text_widget(
    ctx: &Context,
    widget_id: Id,
    cursor_range: Option<CCursorRange>,
    role: accesskit::Role,
    global_from_galley: TSTransform,
    galley: &Galley,
) {
    let parent_id = ctx.accesskit_node_builder(widget_id, |builder| {
        if let Some(cursor_range) = &cursor_range {
            let anchor = galley.layout_from_cursor(cursor_range.secondary);
            let focus = galley.layout_from_cursor(cursor_range.primary);
            if let Some(anchor) = text_run_position(
                widget_id,
                galley,
                anchor.row,
                anchor.column,
                cursor_range.secondary.prefer_next_row,
            ) && let Some(focus) = text_run_position(
                widget_id,
                galley,
                focus.row,
                focus.column,
                cursor_range.primary.prefer_next_row,
            ) {
                builder.set_text_selection(accesskit::TextSelection { anchor, focus });
            }
        }
        builder.set_role(role);
        widget_id
    });
    let Some(parent_id) = parent_id else {
        return;
    };
    for (row_index, row) in galley.rows.iter().enumerate() {
        let runs = text_run_ranges(row);
        let mut word_indices = Vec::new();
        let mut char_offset = 0usize;
        for word in row.text().split_word_bounds() {
            if !word.chars().all(char::is_whitespace) {
                word_indices.push(char_offset);
            }
            char_offset = char_offset.saturating_add(word.chars().count());
        }
        let scale = global_from_galley.scaling.abs();
        for (chunk, range) in runs.iter().enumerate() {
            let glyph_end = range.end.min(row.glyphs.len());
            let glyphs = row.glyphs.get(range.start..glyph_end).unwrap_or_default();
            let rtl = glyphs
                .first()
                .map_or(row.paragraph_level % 2 == 1, |g| g.is_rtl());
            let newline_x = row.x_offset(CharIndex(row.glyphs.len()));
            let includes_newline = range.end > row.glyphs.len();
            let newline_width = row.height() / 2.0;
            let newline_left = if row.paragraph_level % 2 == 1 {
                newline_x - newline_width
            } else {
                newline_x
            };
            let mut min_x = glyphs
                .iter()
                .map(|g| g.pos.x)
                .reduce(f32::min)
                .unwrap_or(newline_x);
            let mut max_x = glyphs
                .iter()
                .map(|g| g.max_x())
                .reduce(f32::max)
                .unwrap_or(newline_x);
            if includes_newline {
                min_x = min_x.min(newline_left);
                max_x = max_x.max(newline_left + newline_width);
            }
            let local_rect = emath::Rect::from_min_max(
                emath::pos2(row.pos.x + min_x, row.min_y()),
                emath::pos2(row.pos.x + max_x, row.max_y()),
            );
            let rect = global_from_galley * local_rect;
            let mut value = String::new();
            let mut lengths = Vec::new();
            let mut positions = Vec::new();
            let mut widths = Vec::new();
            let first_word = word_indices.partition_point(|&index| index < range.start);
            let end_word = word_indices.partition_point(|&index| index < range.end);
            let word_starts: Vec<u8> = word_indices
                .get(first_word..end_word)
                .unwrap_or_default()
                .iter()
                .map(|&index| (index - range.start) as u8)
                .collect();
            for glyph in glyphs {
                value.push(glyph.chr);
                lengths.push(glyph.chr.len_utf8() as u8);
                positions.push(
                    if rtl {
                        max_x - glyph.max_x()
                    } else {
                        glyph.pos.x - min_x
                    } * scale,
                );
                widths.push(glyph.advance_width * scale);
            }
            if includes_newline {
                value.push('\n');
                lengths.push(1);
                positions.push(
                    if rtl {
                        max_x - newline_left - newline_width
                    } else {
                        newline_left - min_x
                    } * scale,
                );
                widths.push(newline_width * scale);
            }
            let run_id = parent_id.with(row_index).with(chunk);
            ctx.register_accesskit_parent(run_id, parent_id);
            ctx.accesskit_node_builder(run_id, |builder| {
                builder.set_role(accesskit::Role::TextRun);
                builder.set_text_direction(if rtl {
                    accesskit::TextDirection::RightToLeft
                } else {
                    accesskit::TextDirection::LeftToRight
                });
                builder.set_bounds(accesskit::Rect {
                    x0: rect.min.x.into(),
                    y0: rect.min.y.into(),
                    x1: rect.max.x.into(),
                    y1: rect.max.y.into(),
                });
                builder.set_value(value);
                builder.set_character_lengths(lengths);
                builder.set_character_positions(positions);
                builder.set_character_widths(widths);
                builder.set_word_starts(word_starts);
                if chunk > 0 {
                    builder.set_previous_on_line(
                        parent_id.with(row_index).with(chunk - 1).accesskit_id(),
                    );
                }
                if chunk + 1 < runs.len() {
                    builder
                        .set_next_on_line(parent_id.with(row_index).with(chunk + 1).accesskit_id());
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Color32, Event, FontId, os::OperatingSystem, text::CCursor};

    fn accesskit_context() -> Context {
        let ctx = Context::default();
        ctx.enable_accesskit();
        if let Some(root) = std::env::var_os("CRAFT_FONTS_DIR") {
            let path =
                std::path::PathBuf::from(root).join("fonts/noto-sans-arabic/NotoSansArabic.ttf");
            let mut definitions = crate::FontDefinitions::default();
            definitions.font_data.insert(
                "arabic".into(),
                std::sync::Arc::new(crate::FontData::from_owned(
                    std::fs::read(path).expect("Noto Arabic"),
                )),
            );
            definitions
                .families
                .get_mut(&crate::FontFamily::Proportional)
                .unwrap()
                .insert(0, "arabic".into());
            ctx.set_fonts(definitions);
        }
        ctx
    }

    #[test]
    fn bidi_accesskit_long_alternating_runs_preserve_words_and_source() {
        let ctx = accesskit_context();
        let text = format!(
            "{}{}{}",
            "a ".repeat(140),
            "a ب ".repeat(8192),
            "z".repeat(270)
        );
        let widget = Id::new("long_bidi_accesskit");
        let mut output = ctx.run_ui(Default::default(), |ui| {
            let galley = ui.fonts_mut(|fonts| {
                fonts.layout(
                    text.clone(),
                    FontId::proportional(24.0),
                    Color32::WHITE,
                    f32::INFINITY,
                )
            });
            update_accesskit_for_text_widget(
                ui.ctx(),
                widget,
                None,
                accesskit::Role::TextInput,
                TSTransform::IDENTITY,
                &galley,
            );
        });
        output.textures_delta.clear();
        let update = output.platform_output.accesskit_update.as_ref().unwrap();
        let nodes: std::collections::HashMap<_, _> =
            update.nodes.iter().map(|(id, node)| (*id, node)).collect();
        let parent = nodes[&widget.accesskit_id()];
        let mut actual_text = String::new();
        let mut actual_word_starts = Vec::new();
        let mut offset = 0;
        let mut full_chunks = 0;
        for id in parent.children() {
            let node = nodes[id];
            assert_eq!(node.role(), accesskit::Role::TextRun);
            let value = node.value().unwrap();
            let lengths = node.character_lengths();
            assert_eq!(lengths.len(), value.chars().count());
            assert_eq!(
                lengths.iter().map(|&n| usize::from(n)).sum::<usize>(),
                value.len()
            );
            assert!(!lengths.is_empty() && lengths.len() <= MAX_CHARS_PER_TEXT_RUN);
            full_chunks += usize::from(lengths.len() == MAX_CHARS_PER_TEXT_RUN);
            assert_eq!(node.character_positions().unwrap().len(), lengths.len());
            assert_eq!(node.character_widths().unwrap().len(), lengths.len());
            for &start in node.word_starts() {
                assert!(usize::from(start) < lengths.len());
                actual_word_starts.push(offset + usize::from(start));
            }
            offset += lengths.len();
            actual_text.push_str(value);
        }
        assert!(
            full_chunks >= 2,
            "long spans must exercise bounded text-run splitting"
        );
        assert_eq!(actual_text, text);
        let mut previous_space = true;
        let expected_word_starts: Vec<_> = text
            .chars()
            .enumerate()
            .filter_map(|(index, chr)| {
                let begins_word = previous_space && !chr.is_whitespace();
                previous_space = chr.is_whitespace();
                begins_word.then_some(index)
            })
            .collect();
        assert_eq!(actual_word_starts, expected_word_starts);
    }

    #[test]
    fn bidi_accesskit_tree_keeps_logical_text_geometry_and_selection() {
        let ctx = accesskit_context();
        let widget = Id::new("bidi_accesskit");
        for text in [
            "مَرْحَبًا ١٢٣".to_owned(),
            "ab العربية 12 cd\nدَرْس".into(),
            format!("{} العربية 42", "a".repeat(270)),
        ] {
            let count = text.chars().count();
            let expected_range = CCursorRange::two(CCursor::new(1), CCursor::new(count - 1));
            let mut captured = None;
            let mut output = ctx.run_ui(Default::default(), |ui| {
                let galley = ui.fonts_mut(|fonts| {
                    fonts.layout(
                        text.clone(),
                        FontId::proportional(24.0),
                        Color32::WHITE,
                        f32::INFINITY,
                    )
                });
                update_accesskit_for_text_widget(
                    ui.ctx(),
                    widget,
                    Some(expected_range),
                    accesskit::Role::TextInput,
                    TSTransform {
                        translation: emath::vec2(30.0, 40.0),
                        scaling: 1.5,
                    },
                    &galley,
                );
                captured = Some(galley);
            });
            output.textures_delta.clear();
            let update = output.platform_output.accesskit_update.as_ref().unwrap();
            let parent = &update
                .nodes
                .iter()
                .find(|(id, _)| *id == widget.accesskit_id())
                .unwrap()
                .1;
            let nodes: Vec<_> = parent
                .children()
                .iter()
                .map(|id| {
                    &update
                        .nodes
                        .iter()
                        .find(|(candidate, _)| candidate == id)
                        .unwrap()
                        .1
                })
                .collect();
            assert_eq!(
                nodes
                    .iter()
                    .map(|node| node.value().unwrap())
                    .collect::<String>(),
                text
            );
            assert!(
                nodes.iter().any(
                    |node| node.text_direction() == Some(accesskit::TextDirection::RightToLeft)
                )
            );
            assert!(
                nodes.iter().any(
                    |node| node.text_direction() == Some(accesskit::TextDirection::LeftToRight)
                )
            );
            let expected_runs: Vec<_> = captured
                .as_ref()
                .unwrap()
                .rows
                .iter()
                .flat_map(|row| {
                    text_run_ranges(row)
                        .into_iter()
                        .map(move |range| (row, range))
                })
                .collect();
            for (node, (row, range)) in nodes.into_iter().zip(expected_runs) {
                assert_eq!(node.role(), accesskit::Role::TextRun);
                let bounds = node.bounds().unwrap();
                assert!(bounds.x0 <= bounds.x1 && bounds.y0 <= bounds.y1);
                let lengths = node.character_lengths();
                let positions = node.character_positions().unwrap();
                let widths = node.character_widths().unwrap();
                assert_eq!(lengths.len(), positions.len());
                assert_eq!(lengths.len(), widths.len());
                assert!(lengths.len() <= MAX_CHARS_PER_TEXT_RUN);
                assert_eq!(
                    lengths.iter().map(|&n| usize::from(n)).sum::<usize>(),
                    node.value().unwrap().len()
                );
                let rtl = node.text_direction() == Some(accesskit::TextDirection::RightToLeft);
                for (offset, index) in range.enumerate() {
                    if let Some(glyph) = row.glyphs.get(index) {
                        let x = if rtl {
                            bounds.x1 - f64::from(positions[offset] + widths[offset])
                        } else {
                            bounds.x0 + f64::from(positions[offset])
                        };
                        let expected = f64::from(30.0 + 1.5 * (row.pos.x + glyph.pos.x));
                        assert!(
                            (x - expected).abs() < 0.001,
                            "accessible character bounds must match the painted source glyph"
                        );
                        assert!((widths[offset] - glyph.advance_width * 1.5).abs() < 0.001);
                    }
                }
                if node.value().unwrap().ends_with('\n') {
                    assert!(
                        widths.last().unwrap() > &0.0,
                        "painted newline selection has a width"
                    );
                }
                for (&position, &width) in positions.iter().zip(widths) {
                    assert!(position >= -0.001 && width >= 0.0);
                    assert!(f64::from(position + width) <= bounds.x1 - bounds.x0 + 0.01);
                }
            }
            let galley = captured.unwrap();
            let mut row_start = 0;
            for (row_index, row) in galley.rows.iter().enumerate() {
                for pair in text_run_ranges(row).windows(2) {
                    let column = CharIndex(pair[1].start);
                    for prefer_next_run in [false, true] {
                        let position =
                            text_run_position(widget, &galley, row_index, column, prefer_next_run)
                                .unwrap();
                        let event = Event::AccessKitActionRequest(accesskit::ActionRequest {
                            action: accesskit::Action::SetTextSelection,
                            target_node: widget.accesskit_id(),
                            target_tree: accesskit::TreeId::ROOT,
                            data: Some(accesskit::ActionData::SetTextSelection(
                                accesskit::TextSelection {
                                    anchor: position,
                                    focus: position,
                                },
                            )),
                        });
                        let mut boundary = CCursorRange::default();
                        assert!(boundary.on_event(
                            OperatingSystem::Windows,
                            &event,
                            &galley,
                            widget
                        ));
                        assert_eq!(boundary.primary.index.0, row_start + column.0);
                        assert_eq!(boundary.primary.prefer_next_row, prefer_next_run);
                    }
                }
                row_start += row.char_count_including_newline().0;
            }
            let mut actual = CCursorRange::default();
            let selection = *parent.text_selection().unwrap();
            let event = Event::AccessKitActionRequest(accesskit::ActionRequest {
                action: accesskit::Action::SetTextSelection,
                target_node: widget.accesskit_id(),
                target_tree: accesskit::TreeId::ROOT,
                data: Some(accesskit::ActionData::SetTextSelection(selection)),
            });
            assert!(actual.on_event(OperatingSystem::Windows, &event, &galley, widget));
            assert_eq!(actual.slice_str(&text), expected_range.slice_str(&text));
            let mut invalid = *parent.text_selection().unwrap();
            invalid.focus.character_index = usize::MAX;
            let event = Event::AccessKitActionRequest(accesskit::ActionRequest {
                action: accesskit::Action::SetTextSelection,
                target_node: widget.accesskit_id(),
                target_tree: accesskit::TreeId::ROOT,
                data: Some(accesskit::ActionData::SetTextSelection(invalid)),
            });
            assert!(!actual.on_event(OperatingSystem::Windows, &event, &galley, widget));
        }
    }
}
