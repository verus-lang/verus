//! Dispatch existing macro generators and format only their generated sections.
use anyhow::{Context, Result};
use proc_macro2::TokenStream;
use verus_builtin_macros_syntax::{ExecMacro, erase_generated, expand_atomic, expand_struct};

pub(crate) fn expand(kind: ExecMacro, tokens: TokenStream) -> Result<String> {
    let expanded = generate(kind, tokens)
        .map_err(crate::parse_error)
        .with_context(|| format!("expanding {}!", kind.name()))?;
    // Generated output may contain nested known macros. Reuse source recording
    // with the appropriate grammar, rather than wrapping an expression in an item.
    if kind.is_expression() {
        crate::strip_expression(&expanded)
    } else {
        crate::strip_source(&expanded)
    }
}

fn generate(kind: ExecMacro, tokens: TokenStream) -> verus_syn::Result<String> {
    let tokens = match kind {
        ExecMacro::AtomicWithGhost => {
            let expr = verus_syn::parse2(expand_atomic(tokens)?)?;
            return Ok(verus_prettyplease::unparse_expr(&expr));
        }
        ExecMacro::StructWithInvariants => expand_struct(tokens)?,
        ExecMacro::StateMachine => {
            erase_generated(verus_state_machines_macros_syntax::expand(tokens, false, false)?)?
        }
        ExecMacro::TokenizedStateMachine => {
            erase_generated(verus_state_machines_macros_syntax::expand(tokens, true, false)?)?
        }
        ExecMacro::TokenizedStateMachineVstd => {
            erase_generated(verus_state_machines_macros_syntax::expand(tokens, true, true)?)?
        }
    };
    let file = verus_syn::parse2(tokens)?;
    Ok(verus_prettyplease::unparse(&file))
}

pub(crate) fn format_generated(source: &str, start: usize, expanded: &str) -> String {
    let line = source[..start].rfind('\n').map_or(0, |i| i + 1);
    let indentation: String =
        source[line..start].chars().take_while(|c| matches!(c, ' ' | '\t')).collect();
    let newline = if source.contains("\r\n") { "\r\n" } else { "\n" };
    expanded.trim_end().split('\n').collect::<Vec<_>>().join(&format!("{newline}{indentation}"))
}
