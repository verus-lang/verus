#![feature(proc_macro_hygiene)]

use proof_with_lib::{negate, Counter, Doubler, Shadowed, Twice};
use vstd::prelude::*;

// `proof_with!` redirects a cross-crate free-function call to the exported counterpart.
#[verus_spec(
    with Tracked(t): Tracked<u8>
    requires t == 1u8,
)]
pub fn call_free_function() {
    proof_with!{Tracked(t)}
    let r = negate(true, 1);
    proof!{ assert(r == false); }
}

// `proof_with!` supports a cross-crate inherent method with an extra tracked result.
#[verus_spec(
    with Tracked(t): Tracked<u8>
    requires t == 1u8,
)]
pub fn call_method(c: &Counter) {
    proof_with!{Tracked(t) => Tracked(next)}
    let r = c.bump();
    proof!{
        assert(r == 7u8);
        assert(next == 1u8);
    }
}

// The stub is ordinary exec code without ghost or tracked parameters, so a non-Verus crate
// can compile and run it, as `consume_proof_with_lib` does.
pub fn call_stub() -> bool {
    negate(true, 1)
}

// Cross-crate trait calls resolve counterparts through the generated companion trait.
#[verus_spec(
    with Ghost(g): Ghost<u64>
    requires g < 100,
)]
pub fn call_trait_method(t: &Twice) {
    proof_with!{Ghost(g)}
    let r = t.double(3);
    proof!{ assert(r == 6u64); }
}

// Lookup cannot choose a shadowing cross-crate inherent counterpart before type checking.
// Qualified syntax identifies the inherent method.
#[verus_spec(
    with Ghost(g): Ghost<u64>
    requires g < 100,
)]
pub fn call_inherent_shadow(s: &Shadowed) {
    proof_with!{Ghost(g)}
    let r = Shadowed::double(s, 3);
    proof!{ assert(r == 4u64); }
}
