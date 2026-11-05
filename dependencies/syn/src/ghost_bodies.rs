//! Parsing without the bodies of ghost item functions.
//!
//! When `verus!` erases ghost code, it discards the bodies of `spec` and
//! `proof` functions that are items of a module or an impl, before looking at
//! them. Parsing these bodies, which make up much of the code generated for
//! state machines, is wasted work in that case; `SkipGhostItemBodies` lets the
//! caller skip it.

use crate::buffer::Cursor;
use crate::parse::ParseStream;
use crate::verus::FnMode;
use crate::Result;
use std::cell::Cell;

std::thread_local! {
    static SKIP: Cell<bool> = const { Cell::new(false) };
}

/// While a `SkipGhostItemBodies` guard is alive, the body of a `spec` or `proof`
/// function that is an item (of the parsed items, a module or an impl, but not
/// inside a block) is parsed as a block without statements: its braces (hence
/// its span) and inner attributes are kept, its other tokens are skipped.
pub struct SkipGhostItemBodies {
    _set: SetSkip,
}

impl SkipGhostItemBodies {
    pub fn enter() -> SkipGhostItemBodies {
        SkipGhostItemBodies { _set: SetSkip::to(true) }
    }
}

/// Sets the flag, restoring the previous value when dropped.
struct SetSkip {
    previous: bool,
}

impl SetSkip {
    fn to(value: bool) -> SetSkip {
        SetSkip { previous: SKIP.with(|s| s.replace(value)) }
    }
}

impl Drop for SetSkip {
    fn drop(&mut self) {
        SKIP.with(|s| s.set(self.previous));
    }
}

/// Whether to skip the body of an item function with this mode.
pub(crate) fn skip_body(mode: &FnMode) -> bool {
    SKIP.with(Cell::get)
        && matches!(
            mode,
            FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_)
        )
}

/// Runs `f` (which parses the statements of a block) with skipping disabled:
/// item functions inside blocks are kept.
pub(crate) fn in_block<R>(f: impl FnOnce() -> R) -> R {
    let _set = SetSkip::to(false);
    f()
}

/// Skips the remaining tokens of `input`.
pub(crate) fn skip_rest(input: ParseStream) -> Result<()> {
    input.step(|cursor| Ok(((), Cursor::end_of_scope(*cursor))))
}
