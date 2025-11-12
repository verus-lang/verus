#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16, AtomicU32,
    AtomicU8, AtomicUsize, Ordering,
};

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use super::atomic::*;
use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
use super::invariant::{InvariantPredicate, AtomicInvariant};
use std::marker::PhantomData;

verus! {

broadcast use crate::group_vstd_default;

pub struct Release<T> {
    val: T,
}

pub struct Acquire<T> {
    val: T,
}

impl<T> Release<T> {
    #[verifier::type_invariant]
    uninterp spec fn inv(self) -> bool;

    pub closed spec fn get(self) -> T {
        self.val
    }
}

impl<T> Acquire<T> {
    // #[verifier::type_invariant]
    // uninterp spec fn inv(self) -> bool;

    pub closed spec fn get(self) -> T {
        self.val
    }
}

pub trait AtomicInvariantPredicate<K, V, G> {
    spec fn atomic_inv(k: K, v: V, g: G) -> bool;
}

#[verifier::external_body]
struct PAtomicRelaxedU32 {
    ato: core::sync::atomic::AtomicU32,
}

#[verifier::external_body]
tracked struct PermissionRelaxedU32 {
    no_copy: NoCopy,
    unused: u32,
}

ghost struct PermissionRelaxedDataU32 {
    patomic: int,
    value: u32,
}

impl PermissionRelaxedU32 {
    #[verifier::external_body]  /* vattr */
    uninterp spec fn view(self) -> PermissionRelaxedDataU32;

    closed spec fn is_for(&self, patomic: PAtomicRelaxedU32) -> bool {
        self.view().patomic == patomic.id()
    }

    closed spec fn points_to(&self, v: u32) -> bool {
        self.view().value == v
    }

    #[verifier::inline]
    closed spec fn value(&self) -> u32 {
        self.view().value
    }

    #[verifier::inline]
    closed spec fn id(&self) -> AtomicCellId {
        self.view().patomic
    }
}

// DANGER: UNSOUND
impl PAtomicRelaxedU32 {
    uninterp spec fn id(&self) -> int;

    #[inline(always)]
    #[verifier::external_body]
    const fn new(i: u32) -> (res: (PAtomicRelaxedU32, Tracked<PermissionRelaxedU32>))
        ensures
            equal(res.1@.view(), PermissionRelaxedDataU32 { patomic: res.0.id(), value: i }),
    {
        let p = PAtomicRelaxedU32 { ato: <core::sync::atomic::AtomicU32>::new(i) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]  /* vattr */
    #[verifier::atomic]  /* vattr */
    fn fetch_add_wrapping(&self, Tracked(perm): Tracked<&mut PermissionRelaxedU32>, n: u32) -> (ret:
        u32)
        requires
            equal(self.id(), old(perm).view().patomic),
        ensures
            equal(old(perm).view().value, ret),
            perm.view().patomic == old(perm).view().patomic,
            perm.view().value as int == wrapping_add_u32(old(perm).view().value as int, n as int),
        opens_invariants none
        no_unwind
    {
        return self.ato.fetch_add(n, Ordering::Relaxed);
    }

    #[inline(always)]
    #[verifier::external_body] /* vattr */
    fn into_inner(self, Tracked(perm): Tracked<PermissionRelaxedU32>) -> (ret: u32)
        requires
            equal(self.id(), perm.view().patomic),
        ensures equal(perm.view().value, ret),
        opens_invariants none
        no_unwind
    {
        return self.ato.into_inner();
    }
}

pub struct AtomicPredRelaxedU32<Pred> { p: Pred }

impl<K, G, Pred> InvariantPredicate<(K, int), (PermissionRelaxedU32, G)> for AtomicPredRelaxedU32<Pred>
    where Pred: AtomicInvariantPredicate<K, u32, G>
{
    // may need to make open again
    closed spec fn inv(k_loc: (K, int), perm_g: (PermissionRelaxedU32, G)) -> bool {
        let (k, loc) = k_loc;
        let (perm, g) = perm_g;

        perm.id() == loc
            && Pred::atomic_inv(k, perm.view().value, g)
    }
}

pub struct AtomicRelaxedU32<K, G, Pred>
    //where Pred: AtomicInvariantPredicate<K, u32, G>
{
    #[doc(hidden)]
    patomic: PAtomicRelaxedU32,

    #[doc(hidden)]
    atomic_inv: Tracked<AtomicInvariant<(K, int), (PermissionRelaxedU32, G), AtomicPredRelaxedU32<Pred>>>,
}

impl<K, G, Pred> AtomicRelaxedU32<K, G, Pred>
    where Pred: AtomicInvariantPredicate<K, u32, G>
{
    pub closed spec fn well_formed(&self) -> bool {
        self.atomic_inv@.constant().1 == self.patomic.id()
    }

    pub closed spec fn constant(&self) -> K {
        self.atomic_inv@.constant().0
    }

    #[inline(always)]
    pub const fn new(Ghost(k): Ghost<K>, u: u32, Tracked(g): Tracked<G>) -> (t: Self)
        requires Pred::atomic_inv(k, u, g),
        ensures t.well_formed() && t.constant() == k,
    {

        let (patomic, Tracked(perm)) = PAtomicRelaxedU32::new(u);

        let tracked pair = (perm, g);
        assert(Pred::atomic_inv(k, u, g));
        assert(perm.view().patomic == patomic.id());
        let tracked atomic_inv = AtomicInvariant::new(
            (k, patomic.id()), pair, 0);

        AtomicRelaxedU32 {
            patomic,
            atomic_inv: Tracked(atomic_inv),
        }
    }

    pub fn fetch_add_wrapping<T, U, F>(&self, n: u32, Tracked(resource_in): Tracked<Release<T>>, tracked f: proof_fn<F>(u32, u32, u32, K, G, T) -> tracked (G, U)) -> (out: (u32, Tracked<Acquire<U>>)) 
        where F: ProofFn + ProofFnReqEns<S<Pred>>
        requires 
            self.well_formed(),
    {
        let result;
        let resource_out;
        crate::vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            assert(self.atomic_inv@.inv(pair));
            assert(self.atomic_inv@.constant().1 == pair.0.id());
            assert(Pred::atomic_inv(self.atomic_inv@.constant().0, pair.0.view().value, pair.1));

            #[allow(unused_mut)]
            let tracked (mut perm, mut g) = pair;
            assert(Pred::atomic_inv(self.atomic_inv@.constant().0, pair.0.view().value, pair.1));

            let ghost prev = perm.view().value;
            result = self.patomic.fetch_add_wrapping(Tracked(&mut perm), n);
            let ghost ret = result;
            let ghost next = perm.view().value;
            let tracked resource_out_inner;

            assert(Pred::atomic_inv(self.atomic_inv@.constant().0, pair.0.view().value, pair.1));

            proof { 
                let input = (prev, next, ret, self.constant(), g, resource_in.get());
                assert(Pred::atomic_inv(input.3, input.0, input.4));
                assert(f.requires(input));
                let tracked output = f(input.0, input.1, input.2, input.3, input.4, input.5);
                assert(f.ensures(input, output)); 
                assert(Pred::atomic_inv(input.3, input.1, output.0));
                let tracked (new_g, temp) = output;
                pair = (perm, new_g);
                resource_out_inner = temp;
            }

            resource_out = Tracked(Acquire { val: resource_out_inner });
        });
        (result, resource_out)
    }

    #[inline(always)]
    pub fn into_inner(self) -> (res: (u32, Tracked<G>))
        requires self.well_formed(),
        ensures Pred::atomic_inv(self.constant(), res.0, res.1@),
    {
        let Self { patomic, atomic_inv: Tracked(atomic_inv) } = self;
        let tracked (perm, g) = atomic_inv.into_inner();
        let v = patomic.into_inner(Tracked(perm));
        (v, Tracked(g))
    }
}

pub struct S<Pred> {
    phantom: PhantomData<Pred>,
} 
impl<T, U, K, G, Pred: AtomicInvariantPredicate<K, u32, G>> ProofFnReqEnsDef<(u32, u32, u32, K, G, T), (G, U)> for S<Pred>
    // where 
    //     Pred: AtomicInvariantPredicate<K, u32, G>
{
    open spec fn req(input: (u32, u32, u32, K, G, T)) -> bool {
        let prev = input.0;
        // let next = input.1; 
        // let ret = input.2;
        let constant = input.3; 
        let ghost_in = input.4; 
        // let pred = input.5;
        Pred::atomic_inv(constant, prev, ghost_in)
    }
    open spec fn ens(input: (u32, u32, u32, K, G, T), output: (G, U)) -> bool {
        // let prev = input.0;
        let next = input.1; 
        // let ret = input.2;
        let constant = input.3; 
        // let ghost_in = input.4; 
        // let pred = input.5;
        let ghost_out = output.0;
        Pred::atomic_inv(constant, next, ghost_out)
    }
}

} // verus!
