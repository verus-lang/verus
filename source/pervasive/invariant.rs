#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;

// TODO:
//  * utility for conveniently creating unique namespaces

// note the names of `inv` and `namespace` are harcoded into the VIR crate.

// LocalInvariant is NEVER `Sync`.
//
// Furthermore, for either type:
//
//  * If an Invariant<T> is Sync, then T must be Send
//      * We could put the T in an Invariant, sync the invariant to another thread,
//        and then extract the T, having effectively send it to the other thread.
//  * If Invariant<T> is Send, then T must be Send
//      * We could put the T in an Invariant, send the invariant to another thread,
//        and then take the T out.
//
// So the Sync/Send-ness of the Invariant depends on the Send-ness of T;
// however, the Sync-ness of T is unimportant (the invariant doesn't give you an extra
// ability to share a reference to a T across threads).
//
// In conclusion, we should have:
//
//    T                   AtomicInvariant<T>  LocalInvariant<T>
//
//    {}          ==>     {}                  {}
//    Send        ==>     Send+Sync           Send
//    Sync        ==>     {}                  {}
//    Sync+Send   ==>     Send+Sync           Send

verus!{
pub trait InvariantPredicate<K, V> {
    spec fn inv(k: K, v: V) -> bool;
}
}

#[proof]
#[verifier(external_body)]
pub struct AtomicInvariant<#[verifier(strictly_positive)] K, #[verifier(strictly_positive)] V, #[verifier(strictly_positive)] Pred> {
    dummy: builtin::SyncSendIfSend<V>,
    dummy1: core::marker::PhantomData<(K, Pred)>,
}

#[proof]
#[verifier(external_body)]
pub struct LocalInvariant<#[verifier(strictly_positive)] K, #[verifier(strictly_positive)] V, #[verifier(strictly_positive)] Pred> {
    dummy: builtin::SendIfSend<V>,
    dummy1: core::marker::PhantomData<(K, Pred)>,
}

macro_rules! declare_invariant_impl {
    ($invariant:ident) => {
        #[proof]
        impl<K, V, Pred: InvariantPredicate<K, V>> $invariant<K, V, Pred> {
            fndecl!(pub fn constant(&self) -> K);
            fndecl!(pub fn namespace(&self) -> int);

            pub fn inv(&self, v: V) -> bool {
                Pred::inv(self.constant(), v)
            }

            #[proof]
            #[verifier(external_body)]
            #[verifier(returns(proof))]
            pub fn new(#[spec] k: K, #[proof] v: V, #[spec] ns: int) -> $invariant<K, V, Pred> {
                requires([
                    Pred::inv(k, v),
                ]);
                ensures(|i: $invariant<K, V, Pred>| [
                    equal(i.constant(), k),
                    equal(i.namespace(), ns),
                ]);

                unimplemented!();
            }

            #[proof]
            #[verifier(external_body)]
            #[verifier(returns(proof))]
            pub fn into_inner(#[proof] self) -> V {
                ensures(|v: V| self.inv(v));

                unimplemented!();
            }
        }
    }
}

declare_invariant_impl!(AtomicInvariant);
declare_invariant_impl!(LocalInvariant);

#[doc(hidden)]
#[proof]
pub struct InvariantBlockGuard;

// NOTE: These 3 methods are removed in the conversion to VIR; they are only used
// for encoding and borrow-checking.
// In the VIR these are all replaced by the OpenInvariant block.
// This means that the bodies, preconditions, and even their modes are not important.
//
// An example usage of the macro is like
//
//   i: AtomicInvariant<X>
//
//   open_invariant!(&i => inner => {
//      { modify `inner` here }
//   });
//
//  where `inner` will have type `X`.
//
//  The purpose of the `guard` object, used below, is to ensure the borrow on `i` will
//  last the entire block.

#[doc(hidden)]
#[verifier(external)]
pub fn open_atomic_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(_inv: &'a AtomicInvariant<K, V, Pred>) -> (&'a InvariantBlockGuard, V) {
    unimplemented!();
}

#[doc(hidden)]
#[verifier(external)]
pub fn open_local_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(_inv: &'a LocalInvariant<K, V, Pred>) -> (&'a InvariantBlockGuard, V) {
    unimplemented!();
}

#[doc(hidden)]
#[verifier(external)]
pub fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) {
    unimplemented!();
}

#[macro_export]
macro_rules! open_atomic_invariant {
    ($eexpr:expr => $iident:ident => $bblock:block) => {
        #[verifier(invariant_block)] {
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::pervasive::invariant::open_atomic_invariant_begin($eexpr);
            $bblock
            $crate::pervasive::invariant::open_invariant_end(guard, $iident);
        }
    }
}

#[macro_export]
macro_rules! open_local_invariant {
    ($eexpr:expr => $iident:ident => $bblock:block) => {
        #[verifier(invariant_block)] {
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::pervasive::invariant::open_local_invariant_begin($eexpr);
            $bblock
            $crate::pervasive::invariant::open_invariant_end(guard, $iident);
        }
    }
}
