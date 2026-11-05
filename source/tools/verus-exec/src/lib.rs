//! Source-preserving snapshots of executable Verus code.
mod edits;
mod expansion;

use std::borrow::Cow;

use anyhow::Result;
use verus_builtin_macros_syntax::{
    Erasure, ErasureKind, source_erasures, source_expression_erasures,
};

use edits::{Edit, Positions};

/// Remove proof artifacts, retaining the bytes of executable code and comments.
/// Both `verus!` and attribute syntax are recognized by the macro syntax visitor.
pub fn strip_source(source: &str) -> Result<String> {
    apply_erasures(source, source_erasures(source).map_err(parse_error)?)
}

fn strip_expression(source: &str) -> Result<String> {
    apply_erasures(source, source_expression_erasures(source).map_err(parse_error)?)
}

// Syntax decisions belong to the macro visitor. Here they become concrete text
// edits; only generated syntax is formatted. Range merging lives in edits.rs.
fn apply_erasures(source: &str, erasures: Vec<Erasure>) -> Result<String> {
    let positions = Positions::new(source);
    let edits = erasures
        .into_iter()
        .map(|erasure| render_erasure(source, &positions, erasure))
        .collect::<Result<Vec<_>>>()?;
    edits::apply(source, edits)
}

fn render_erasure(source: &str, positions: &Positions<'_>, erasure: Erasure) -> Result<Edit> {
    let mut range = positions.range(erasure.span)?;
    let replacement = match erasure.kind {
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
            None
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
            None
        }
        ErasureKind::Unit => Some(Cow::Borrowed("{}")),
        ErasureKind::Replace(text) => Some(Cow::Borrowed(text)),
        ErasureKind::Identifier(name) => Some(Cow::Owned(name)),
        ErasureKind::ConstructorSuffix(tokens) => {
            // The suffix is also valid syntax for an absolute-path call. Format
            // it directly, keeping the original path and generic arguments.
            let expr = verus_syn::parse2(tokens).map_err(parse_error)?;
            Some(Cow::Owned(verus_prettyplease::unparse_expr(&expr)))
        }
        ErasureKind::ExpandMacro { kind, tokens } => {
            let expanded = expansion::expand(kind, tokens)?;
            Some(Cow::Owned(expansion::format_generated(source, range.start, &expanded)))
        }
        ErasureKind::ReturnName => {
            // The space following result: belongs to the removed binding.
            // Keep comments and line breaks in the type.
            range.end += source[range.end..]
                .chars()
                .take_while(|c| matches!(c, ' ' | '\t'))
                .map(char::len_utf8)
                .sum::<usize>();
            None
        }
        ErasureKind::Node => None,
    };
    Ok(Edit { range, replacement })
}

fn parse_error(error: verus_syn::Error) -> anyhow::Error {
    let at = error.span().start();
    anyhow::anyhow!("{} at {}:{}", error, at.line, at.column + 1)
}
