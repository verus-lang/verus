//! Source-preserving snapshots of executable Verus code.
use std::borrow::Cow;
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
                ErasureKind::Unit => replacement = Some(Cow::Borrowed("{}")),
                ErasureKind::Replace(text) => replacement = Some(Cow::Borrowed(text)),
                ErasureKind::Identifier(name) => replacement = Some(Cow::Owned(name)),
                ErasureKind::ConstructorSuffix(tokens) => {
                    // Format only the generated suffix. The original constructor
                    // path, generic arguments, and their comments remain intact.
                    let expr =
                        verus_syn::parse_str(&format!("Ghost{tokens}")).map_err(parse_error)?;
                    let formatted = verus_prettyplease::unparse_expr(&expr);
                    replacement = Some(Cow::Owned(formatted["Ghost".len()..].to_owned()));
                }
                ErasureKind::ExpandMacro { name, tokens } => {
                    let expanded = expand_macro(&name, tokens)
                        .map_err(parse_error)
                        .with_context(|| format!("expanding {name}!"))?;
                    let expanded = if name == "atomic_with_ghost" {
                        // Parse expressions in a Rust body so nested known macros
                        // can use the same source visitor and replacement logic.
                        let prefix = "fn __verus_exec_expression() {\n";
                        let wrapped = strip_source(&format!("{prefix}{expanded}\n}}"))?;
                        wrapped[prefix.len()..wrapped.len() - 2].to_owned()
                    } else {
                        strip_source(&expanded)?
                    };
                    let line = source[..range.start].rfind('\n').map_or(0, |i| i + 1);
                    let indentation: String = source[line..range.start]
                        .chars()
                        .take_while(|c| matches!(c, ' ' | '\t'))
                        .collect();
                    let newline = if source.contains("\r\n") { "\r\n" } else { "\n" };
                    replacement = Some(Cow::Owned(
                        expanded
                            .trim_end()
                            .split('\n')
                            .collect::<Vec<_>>()
                            .join(&format!("{newline}{indentation}")),
                    ));
                }
                ErasureKind::ReturnName => {
                    // The space following `result:` belongs to the removed
                    // binding. Keep comments and line breaks in the type.
                    range.end += source[range.end..]
                        .chars()
                        .take_while(|c| matches!(c, ' ' | '\t'))
                        .map(char::len_utf8)
                        .sum::<usize>();
                }
                ErasureKind::Node => {}
            }
            Ok(Edit { range, replacement })
        })
        .collect::<Result<Vec<_>>>()?;
    erase_ranges(source, ranges)
}

fn expand_macro(name: &str, tokens: proc_macro2::TokenStream) -> verus_syn::Result<String> {
    use verus_builtin_macros_syntax::{erase_generated, expand_atomic, expand_struct};
    if name == "atomic_with_ghost" {
        let expr = verus_syn::parse2(expand_atomic(tokens)?)?;
        return Ok(verus_prettyplease::unparse_expr(&expr));
    }
    let tokens = if name == "struct_with_invariants" {
        expand_struct(tokens)?
    } else {
        erase_generated(verus_state_machines_macros_syntax::expand(
            tokens,
            name != "state_machine",
            name == "tokenized_state_machine_vstd",
        )?)?
    };
    let file = verus_syn::parse2(tokens)?;
    Ok(verus_prettyplease::unparse(&file))
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
    replacement: Option<Cow<'static, str>>,
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
            output.push_str(&replacement);
        }
        cursor = cursor.max(range.end);
    }
    output.push_str(&source[cursor..]);
    Ok(output)
}
