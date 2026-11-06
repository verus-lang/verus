//! Apply byte-range edits without reprinting the original source.
use std::borrow::Cow;
use std::ops::Range;

use anyhow::{Context, Result, ensure};
use proc_macro2::{LineColumn, Span};

pub(crate) struct Positions<'a> {
    source: &'a str,
    lines: Vec<usize>,
}

impl<'a> Positions<'a> {
    pub(crate) fn new(source: &'a str) -> Self {
        // parse_file strips a BOM before tokenization; spans on the first line
        // therefore start after it. Keep the original BOM in the output.
        let start = if source.starts_with('\u{feff}') { '\u{feff}'.len_utf8() } else { 0 };
        let mut lines = vec![start];
        lines.extend(source.match_indices('\n').map(|(i, _)| i + 1));
        Self { source, lines }
    }

    fn offset(&self, at: LineColumn) -> Result<usize> {
        // proc_macro2 columns count Unicode scalar values, not UTF-8 bytes.
        let start = *self.lines.get(at.line.wrapping_sub(1)).context("invalid source span")?;
        let line = &self.source[start..];
        let offset = line.char_indices().map(|(i, _)| i).nth(at.column).unwrap_or(line.len());
        Ok(start + offset)
    }

    pub(crate) fn range(&self, span: Span) -> Result<Range<usize>> {
        let range = self.offset(span.start())?..self.offset(span.end())?;
        ensure!(range.start <= range.end && range.end <= self.source.len(), "invalid source span");
        Ok(range)
    }
}

pub(crate) struct Edit {
    pub(crate) range: Range<usize>,
    pub(crate) replacement: Option<Cow<'static, str>>,
}

pub(crate) fn apply(source: &str, mut edits: Vec<Edit>) -> Result<String> {
    edits.sort_by_key(|e| (e.range.start, std::cmp::Reverse(e.range.end)));
    let mut merged: Vec<Edit> = Vec::new();
    for edit in edits {
        if let Some(last) = merged.last_mut() {
            let overlaps = edit.range.start < last.range.end;
            let adjacent_deletions = edit.range.start == last.range.end
                && last.replacement.is_none()
                && edit.replacement.is_none();
            if overlaps || adjacent_deletions {
                last.range.end = last.range.end.max(edit.range.end);
                continue;
            }
        }
        merged.push(edit);
    }
    // Whole-line annotations should not leave rows of indentation behind.
    // Comments outside a removed node's span are kept, including trailing ones.
    for edit in &mut merged {
        if edit.replacement.is_some() {
            continue;
        }
        let range = &mut edit.range;
        let line_start = source[..range.start].rfind('\n').map_or(0, |i| i + 1);
        let line_end = source[range.end..].find('\n').map_or(source.len(), |i| range.end + i);
        if source[line_start..range.start].trim().is_empty()
            && source[range.end..line_end].trim().is_empty()
        {
            range.start = line_start;
            range.end = if line_end < source.len() { line_end + 1 } else { line_end };
        }
    }
    let mut output = String::with_capacity(source.len());
    let mut cursor = 0;
    for Edit { range, replacement } in merged {
        if range.start > cursor {
            output.push_str(&source[cursor..range.start]);
        }
        if let Some(replacement) = replacement {
            output.push_str(&replacement);
        }
        cursor = cursor.max(range.end);
    }
    output.push_str(&source[cursor..]);
    Ok(output)
}
