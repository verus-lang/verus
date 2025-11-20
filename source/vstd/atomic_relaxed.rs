#![allow(unused_imports)]

use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicPtr, AtomicU16, AtomicU32,
    AtomicU8, AtomicUsize, Ordering,
};

#[cfg(target_has_atomic = "64")]
use core::sync::atomic::{AtomicI64, AtomicU64};

use super::atomic::*;
use super::invariant::{AtomicInvariant, InvariantPredicate};
use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
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
    pub closed spec fn get(self) -> T {
        self.val
    }

    proof fn tracked_get(tracked self) -> (tracked out: T)
        ensures
            out == self.get(),
    {
        self.val
    }

    pub proof fn to_tup<U>(tracked self, tracked u: Release<U>) -> (tracked out: Release<(T, U)>)
        ensures
            out.get().0 == self.get(),
            out.get().1 == u.get(),
    {
        Release { val: (self.val, u.val) }
    }
}

impl<T> Acquire<T> {
    pub closed spec fn get(self) -> T {
        self.val
    }
}

#[verifier::external_body]
pub fn fence_release<P>(Tracked(resource): Tracked<P>) -> (out: Tracked<Release<P>>)
    ensures
        resource == out@.get(),
{
    core::sync::atomic::fence(Ordering::Release);
    Tracked(Release { val: resource })
}

#[verifier::external_body]
pub fn fence_acquire<P>(Tracked(resource): Tracked<Acquire<P>>) -> (out: Tracked<P>)
    ensures
        resource.get() == out@,
{
    core::sync::atomic::fence(Ordering::Acquire);
    Tracked(resource.get())
}

pub unsafe trait UnsyncRelaxed {

}

pub axiom fn ghost_release_wrap<T: UnsyncRelaxed>(tracked r: T) -> (tracked out: Release<T>)
    ensures
        out.get() == r,
;

pub axiom fn ghost_release_unwrap<T: UnsyncRelaxed>(tracked r: Release<T>) -> (tracked out: T)
    ensures
        out == r.get(),
;

pub axiom fn ghost_acquire_wrap<T: UnsyncRelaxed>(tracked r: T) -> (tracked out: Acquire<T>)
    ensures
        out.get() == r,
;

pub axiom fn ghost_acquire_unwrap<T: UnsyncRelaxed>(tracked r: Acquire<T>) -> (tracked out: T)
    ensures
        out == r.get(),
;

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
    #[verifier::external_body]  /* vattr */
    fn into_inner(self, Tracked(perm): Tracked<PermissionRelaxedU32>) -> (ret: u32)
        requires
            equal(self.id(), perm.view().patomic),
        ensures
            equal(perm.view().value, ret),
        opens_invariants none
        no_unwind
    {
        return self.ato.into_inner();
    }
}

pub struct AtomicPredRelaxedU32<Pred> {
    p: Pred,
}

impl<K, G, Pred> InvariantPredicate<(K, int), (PermissionRelaxedU32, G)> for AtomicPredRelaxedU32<
    Pred,
> where Pred: AtomicInvariantPredicate<K, u32, G> {
    closed spec fn inv(k_loc: (K, int), perm_g: (PermissionRelaxedU32, G)) -> bool {
        let (k, loc) = k_loc;
        let (perm, g) = perm_g;

        perm.id() == loc && Pred::atomic_inv(k, perm.view().value, g)
    }
}

pub struct AtomicRelaxedU32<K, G, Pred> {
    #[doc(hidden)]
    patomic: PAtomicRelaxedU32,
    #[doc(hidden)]
    atomic_inv: Tracked<
        AtomicInvariant<(K, int), (PermissionRelaxedU32, G), AtomicPredRelaxedU32<Pred>>,
    >,
}

impl<K, G, Pred> AtomicRelaxedU32<K, G, Pred> where Pred: AtomicInvariantPredicate<K, u32, G> {
    pub closed spec fn well_formed(&self) -> bool {
        self.atomic_inv@.constant().1 == self.patomic.id()
    }

    pub closed spec fn constant(&self) -> K {
        self.atomic_inv@.constant().0
    }

    #[inline(always)]
    pub const fn new(Ghost(k): Ghost<K>, u: u32, Tracked(g): Tracked<G>) -> (t: Self)
        requires
            Pred::atomic_inv(k, u, g),
        ensures
            t.well_formed() && t.constant() == k,
    {
        let (patomic, Tracked(perm)) = PAtomicRelaxedU32::new(u);
        let tracked pair = (perm, g);
        let tracked atomic_inv = AtomicInvariant::new((k, patomic.id()), pair, 0);
        AtomicRelaxedU32 { patomic, atomic_inv: Tracked(atomic_inv) }
    }

    pub fn fetch_add_wrapping<T, U, F, C>(
        &self,
        n: u32,
        Tracked(resource_in): Tracked<Option<Release<T>>>,
        Tracked(f): Tracked<
            proof_fn<F>(
                prev: u32,
                next: u32,
                ret: u32,
                operand: u32,
                constant: K,
                tracked ghost_in: G,
                tracked resource_in: Option<T>,
            ) -> tracked (G, Option<U>),
        >,
    ) -> (out: (u32, Tracked<Option<Acquire<U>>>)) where
        F: ProofFn + ProofFnReqEns<RelaxedAtomicProofUpdate<Pred, C>>,
        C: ClientReqEns<T, U, K>,

        requires
            ({
                let resource_in_inner = match resource_in {
                    Some(res) => Some(res.get()),
                    None => None,
                };
                C::req(n, resource_in_inner, self.constant())
            }),
            self.well_formed(),
        ensures
            ({
                let resource_out_inner = match out.1@ {
                    Some(res) => Some(res.get()),
                    None => None,
                };
                C::ens(out.0, resource_out_inner, self.constant())
            }),
    {
        let ret;
        let tracked resource_out;
        crate::vstd::invariant::open_atomic_invariant!(self.atomic_inv.borrow() => pair => {
            let tracked (mut perm, mut g) = pair;
            let ghost prev = perm.view().value;
            ret = self.patomic.fetch_add_wrapping(Tracked(&mut perm), n);
            let ghost next = perm.view().value;

            proof {
                let tracked resource_in_inner =
                    match resource_in {
                        Some(x) => Some(x.tracked_get()),
                        None => None
                    };
                // these asserts are needed for triggers
                assert(f.requires((prev, next, ret, n, self.constant(), g, resource_in_inner)));
                let tracked output = f(prev, next, ret, n, self.constant(), g, resource_in_inner);
                assert(f.ensures((prev, next, ret, n, self.constant(), g, resource_in_inner), output));
                let tracked (new_g, resource_out_inner) = output;
                pair = (perm, new_g);
                resource_out =
                    match resource_out_inner {
                        Some(t) => Some(Acquire{ val: t }),
                        None => None
                    };
            }

        });
        (ret, Tracked(resource_out))
    }

    #[inline(always)]
    pub fn into_inner(self) -> (res: (u32, Tracked<G>))
        requires
            self.well_formed(),
        ensures
            Pred::atomic_inv(self.constant(), res.0, res.1@),
    {
        let Self { patomic, atomic_inv: Tracked(atomic_inv) } = self;
        let tracked (perm, g) = atomic_inv.into_inner();
        let v = patomic.into_inner(Tracked(perm));
        (v, Tracked(g))
    }
}

pub open spec fn faa_u32_spec(prev: u32, next: u32, ret: u32, operand: u32) -> bool {
    next as int == wrapping_add_u32(prev as int, operand as int) && ret == prev
}

pub trait ClientReqEns<T, U, K> {
    spec fn req(operand: u32, resource_in: Option<T>, constant: K) -> bool;

    spec fn ens(ret: u32, resource_out: Option<U>, constant: K) -> bool;
}

pub struct RelaxedAtomicProofUpdate<Pred, C> {
    phantom_p: PhantomData<Pred>,
    phantom_c: PhantomData<C>,
}

impl<T, U, K, G, Pred, C> ProofFnReqEnsDef<
    (u32, u32, u32, u32, K, G, Option<T>),
    (G, Option<U>),
> for RelaxedAtomicProofUpdate<Pred, C> where
    Pred: AtomicInvariantPredicate<K, u32, G>,
    C: ClientReqEns<T, U, K>,
 {
    open spec fn req(input: (u32, u32, u32, u32, K, G, Option<T>)) -> bool {
        let prev = input.0;
        let next = input.1;
        let ret = input.2;
        let operand = input.3;
        let constant = input.4;
        let ghost_in = input.5;
        let resource_in = input.6;
        &&& Pred::atomic_inv(constant, prev, ghost_in)
        &&& faa_u32_spec(prev, next, ret, operand)
        &&& C::req(operand, resource_in, constant)
    }

    open spec fn ens(input: (u32, u32, u32, u32, K, G, Option<T>), output: (G, Option<U>)) -> bool {
        let next = input.1;
        let ret = input.2;
        let constant = input.4;
        let pred = input.6;
        let ghost_out = output.0;
        let resource_out = output.1;
        &&& Pred::atomic_inv(constant, next, ghost_out)
        &&& C::ens(ret, resource_out, constant)
    }
}

} // verus!
