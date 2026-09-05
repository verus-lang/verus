// Minimal reproduction (silent-failure variant) of a Verus bug: trait-method-impl
// contract inheritance (`Lowerer::inheritance` in vir/src/ast_to_sst_func.rs) only
// substitutes `Self` into inherited requires/ensures, never a method-level generic
// parameter. See verus-bug-trait-method-generic-contract-inheritance.md.
//
// Run with:
//   cd source && source ../tools/activate
//   ./target-verus/release/verus verus-bug-repro-silent.rs --crate-type=lib
//
// Expect 2 errors: `other.val() != 0` fails to verify despite being this method's
// own `requires`, and the `ensures` clause fails even though it is directly
// `assume`d (with the correct, real types) immediately beforehand.

use verus_builtin_macros::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub trait Val: Sized {
    spec fn val(self) -> nat;
}

// `nonzero`'s own generic parameter `Foo` is distinct from `Self`.
pub trait ValProps: Val {
    proof fn nonzero<Foo: Val>(&self, other: &Foo)
        requires
            self.val() != 0,
            other.val() != 0,
        ensures
            self.val() + other.val() > 0,
    ;
}

// The impl's own generic parameter happens to also be named `Foo` - the same
// name the trait declaration uses for `nonzero`'s own generic parameter.
pub struct Wrapper<Foo: Val>(Foo);

impl<Foo: Val> Val for Wrapper<Foo> {
    closed spec fn val(self) -> nat {
        self.0.val()
    }
}

impl<Foo: Val> ValProps for Wrapper<Foo> {
    proof fn nonzero<Baz: Val>(&self, other: &Baz) {
        // `other.val() != 0` is one of this method's own inherited `requires`.
        // It should be trivially available as a hypothesis - it isn't.
        assert(other.val() != 0); // FAILS

        // Even directly assuming the literal ensures goal (correctly typed)
        // doesn't help: the postcondition Verus actually checks isn't the
        // proposition written in the trait declaration above.
        assume(self.val() + other.val() > 0);
    } // the `ensures` clause still FAILS
}

} // verus!
