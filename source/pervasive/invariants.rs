#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use crate::pervasive::*;

// TODO right now this file contains the minimal type definitions needed for rust_verify
// but we need to make a library to make the Invariant type actually usable
//  * constructors, destructors
//  * utility for creating unique namespaces

#[proof]
#[verifier(external_body)]
pub struct Invariant<V> {
    dummy: std::marker::PhantomData<V>,
}

// note the names of `inv` and `namespace` are harcoded.
// TODO right now they are only translated if the user refers to them in their code
// which can cause a crash otherwise

// TODO move this to be inside the `impl`:
#[proof]
#[verifier(external_body)]
#[verifier(returns(proof))]
pub fn invariant_new<V, F: Fn(V) -> bool>(#[proof] v: V, #[spec] inv: F, #[spec] ns: int) -> Invariant<V> {
  requires([
    inv(v),
  ]);
  ensures(|i: Invariant<V>|
    forall(|v: V| i.inv(v) == inv(v)) // TODO replace this with function equality
    && equal(i.namespace(), ns)
  );

  unimplemented!();
}

#[proof]
impl<V> Invariant<V> {
    #[verifier(pub_abstract)]
    #[spec]
    pub fn inv(&self, _v: V) -> bool {
        arbitrary()
    }

    // If you want to open two invariants I and J at the same time,
    // you need to show that I.namespace() != J.namespace()
    // The namespace can be declared upon allocation of the invariant.

    #[verifier(pub_abstract)]
    #[spec]
    pub fn namespace(&self) -> int {
        arbitrary()
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn destruct(#[proof] self) -> V {
        ensures(|v: V| self.inv(v));

        unimplemented!();
    }
}

#[proof]
pub struct InvariantBlockGuard;

// NOTE: These 2 methods are removed in the conversion to VIR; they are only used
// for encoding and borrow-checking.
// In the VIR these are all replaced by the OpenInvariant block.
// This means that the bodies, preconditions, and even their modes are not important.
//
// An example usage of the macro is like
//
//   i: Invariant<X>
//
//   open_invariant!(&i => inner => {
//      { modify `inner` here }
//   });
//
//  where `inner` will have type `X`.
//
//  The purpose of the `guard` object, used below, is to ensure the borrow on `i` will
//  last the entire block.

#[verifier(external_body)]
pub fn open_invariant_begin<'a, V>(_inv: &'a Invariant<V>) -> (&'a InvariantBlockGuard, V) {
    requires([false]);
    unimplemented!();
}

#[verifier(external_body)]
pub fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) {
    requires([false]);
    unimplemented!();
}

#[macro_export]
macro_rules! open_invariant {
    ($eexpr:expr => $iident:ident => $bblock:block) => {
        #[verifier(invariant_block)] {
            #[allow(unused_mut)] let (guard, mut $iident) = crate::open_invariant_begin($eexpr);
            $bblock
            crate::open_invariant_end(guard, $iident);
        }
    }
}
