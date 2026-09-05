// Minimal reproduction (crash variant) of the same Verus bug as
// verus-bug-repro-silent.rs. Identical except the impl's own generic
// parameter is renamed from `Foo` to `Bar`, removing the name collision with
// the trait method's own `Foo`. This turns the silent failures in the other
// repro into an internal compiler panic, proving that `Foo` (the trait
// method's own generic parameter) was never substituted at all during
// contract inheritance - it was merely, coincidentally, resolving by name to
// the impl's own `Foo` when one happened to exist in scope.
//
// Run with:
//   cd source && source ../tools/activate
//   ./target-verus/release/verus verus-bug-repro-crash.rs --crate-type=lib
//
// Expect a panic: "internal error: generated ill-typed AIR code: ...
// use of undeclared variable Foo&."

use verus_builtin_macros::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub trait Val: Sized {
    spec fn val(self) -> nat;
}

pub trait ValProps: Val {
    proof fn nonzero<Foo: Val>(&self, other: &Foo)
        requires
            self.val() != 0,
            other.val() != 0,
        ensures
            self.val() + other.val() > 0,
    ;
}

pub struct Wrapper<Bar: Val>(Bar);

impl<Bar: Val> Val for Wrapper<Bar> {
    closed spec fn val(self) -> nat {
        self.0.val()
    }
}

impl<Bar: Val> ValProps for Wrapper<Bar> {
    proof fn nonzero<Baz: Val>(&self, other: &Baz) {
        assert(other.val() != 0); // panics before this can even be checked
    }
}

} // verus!
