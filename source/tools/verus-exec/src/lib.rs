//! Source-preserving snapshots of executable Verus code.
use std::ops::Range;

use anyhow::{Context, Result, ensure};
use proc_macro2::{LineColumn, Span};
use verus_builtin_macros_syntax::{ErasureKind, source_erasures};

/// Remove proof artifacts, retaining the bytes of executable code and comments.
/// Both `verus!` and attribute syntax are recognized by the macro syntax visitor.
pub fn strip_source(source: &str) -> Result<String> {
    let erasures = source_erasures(source).map_err(parse_error)?;
    let positions = Positions::new(source);
    let ranges = erasures
        .into_iter()
        .map(|erasure| {
            let mut range = positions.range(erasure.span)?;
            let mut replacement = None;
            match erasure.kind {
                ErasureKind::WrapperOpen => {
                    // Remove blank boundary lines introduced by verus! { ... }.
                    // Leave the first code/comment line's indentation intact.
                    while let Some(newline) = source[range.end..].find('\n') {
                        let end = range.end + newline + 1;
                        if !source[range.end..end].trim().is_empty() {
                            break;
                        }
                        range.end = end;
                    }
                    let line = source[..range.start].rfind('\n').map_or(0, |i| i + 1);
                    if source[line..range.start].trim().is_empty() {
                        range.start = line;
                    }
                }
                ErasureKind::WrapperClose => {
                    let mut start = range.start;
                    loop {
                        let line = source[..start].rfind('\n').map_or(0, |i| i + 1);
                        if !source[line..start].trim().is_empty() {
                            break;
                        }
                        range.start = line;
                        if line == 0 {
                            break;
                        }
                        start = line - 1;
                    }
                }
                ErasureKind::Unit => replacement = Some("{}"),
                ErasureKind::Node => {}
            }
            Ok(Edit { range, replacement })
        })
        .collect::<Result<Vec<_>>>()?;
    erase_ranges(source, ranges)
}

fn parse_error(error: verus_syn::Error) -> anyhow::Error {
    let at = error.span().start();
    anyhow::anyhow!("{} at {}:{}", error, at.line, at.column + 1)
}

struct Positions<'a> {
    source: &'a str,
    lines: Vec<usize>,
}

impl<'a> Positions<'a> {
    fn new(source: &'a str) -> Self {
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

    fn range(&self, span: Span) -> Result<Range<usize>> {
        let range = self.offset(span.start())?..self.offset(span.end())?;
        ensure!(range.start <= range.end && range.end <= self.source.len(), "invalid source span");
        Ok(range)
    }
}

struct Edit {
    range: Range<usize>,
    replacement: Option<&'static str>,
}

fn erase_ranges(source: &str, mut edits: Vec<Edit>) -> Result<String> {
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
            output.push_str(replacement);
        }
        cursor = cursor.max(range.end);
    }
    output.push_str(&source[cursor..]);
    Ok(output)
}
