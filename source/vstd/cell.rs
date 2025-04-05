#![allow(deprecated)]
#![allow(unused_imports)]

use core::cell::UnsafeCell;
use core::marker;
use core::{mem, mem::MaybeUninit};

use super::invariant::*;
use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
pub use super::raw_ptr::MemContents;
use super::set::*;
use super::*;

verus! {

broadcast use {super::map::group_map_axioms, super::set::group_set_axioms};
// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

/// `PCell<V>` (which stands for "permissioned call") is the primitive Verus `Cell` type.
///
/// Technically, it is a wrapper around
/// `core::cell::UnsafeCell<core::mem::MaybeUninit<V>>`, and thus has the same runtime
/// properties: there are no runtime checks (as there would be for Rust's traditional
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)).
/// Its data may be uninitialized.
///
/// Furthermore (and unlike both
/// [`core::cell::Cell`](https://doc.rust-lang.org/core/cell/struct.Cell.html) and
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)),
/// a `PCell<V>` may be `Sync` (depending on `V`).
/// Thanks to verification, Verus ensures that access to the cell is data-race-free.
///
/// `PCell` uses a _ghost permission token_ similar to [`simple_pptr::PPtr`] -- see the [`simple_pptr::PPtr`]
/// documentation for the basics.
/// For `PCell`, the associated type of the permission token is [`cell::PointsTo`].
///
/// ### Differences from `PPtr`.
///
/// The key difference is that, whereas [`simple_pptr::PPtr`] represents a fixed address in memory,
/// a `PCell` has _no_ fixed address because a `PCell` might be moved.
/// As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,
/// it is a unique identifier that is fixed for a given cell, even when it is moved.
///
/// The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`].
/// Despite the fact that it is, in some ways, "like a pointer", note that
/// `CellId` does not support any meangingful arithmetic,
/// has no concept of a "null ID",
/// and has no runtime representation.
///
/// Also note that the `PCell` might be dropped before the `PointsTo` token is dropped,
/// although in that case it will no longer be possible to use the `PointsTo` in `exec` code
/// to extract data from the cell.
///
/// ### Example (TODO)
#[verifier::external_body]
#[verifier::accept_recursive_types(V)]
pub struct PCell<V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

/// `PCell` is _always_ safe to `Send` or `Sync`. Rather, it is the [`PointsTo`] object where `Send` and `Sync` matter.
/// (It doesn't matter if you move the bytes to another thread if you can't access them.)
#[verifier::external]
unsafe impl<T> Sync for PCell<T> {

}

#[verifier::external]
unsafe impl<T> Send for PCell<T> {

}

/// Permission object associated with a [`PCell<V>`].
///
/// See the documentation of [`PCell<V>`] for more information.
// PointsTo<V>, on the other hand, needs to inherit both Send and Sync from the V,
// which it does by default in the given definition.
// (Note: this depends on the current behavior that #[verifier::spec] fields are still counted for marker traits)
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsTo<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct PointsToData<V> {
    pub pcell: CellId,
    #[cfg_attr(not(verus_verify_core), deprecated = "use `pcell_points!`, or `mem_contents()` instead")]
    pub value: Option<V>,
}

#[doc(hidden)]
pub open spec fn option_from_mem_contents<V>(val: MemContents<V>) -> Option<V> {
    match val {
        MemContents::Init(v) => Some(v),
        MemContents::Uninit => None,
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! pcell_opt_internal {
    [$pcell:expr => $val:expr] => {
        $crate::vstd::cell::PointsToData {
            pcell: $pcell,
            value: $val,
        }
    };
}

#[cfg_attr(not(verus_verify_core), deprecated = "use pcell_points! instead")]
#[macro_export]
macro_rules! pcell_opt {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::vstd::cell::pcell_opt_internal!($($tail)*)
        )
    }
}

pub use pcell_opt_internal;
pub use pcell_opt;

#[doc(hidden)]
#[macro_export]
macro_rules! pcell_points_internal {
    [$pcell:expr => $val:expr] => {
        $crate::vstd::cell::PointsToData {
            pcell: $pcell,
            value: $crate::vstd::cell::option_from_mem_contents($val),
        }
    };
}

#[macro_export]
macro_rules! pcell_points {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::vstd::cell::pcell_points_internal!($($tail)*)
        )
    }
}

pub use pcell_points_internal;
pub use pcell_points;

#[verifier::external_body]
pub struct CellId {
    id: int,
}

impl<V> PointsTo<V> {
    /// The [`CellId`] of the [`PCell`] this permission is associated with.
    pub uninterp spec fn id(&self) -> CellId;

    /// The contents of the cell, either unitialized or initialized to some `V`.
    pub uninterp spec fn mem_contents(&self) -> MemContents<V>;

    pub open spec fn view(self) -> PointsToData<V> {
        PointsToData { pcell: self.id(), value: option_from_mem_contents(self.mem_contents()) }
    }

    #[cfg_attr(not(verus_verify_core), deprecated = "use mem_contents() instead")]
    pub open spec fn opt_value(&self) -> Option<V> {
        match self.mem_contents() {
            MemContents::Init(value) => Some(value),
            MemContents::Uninit => None,
        }
    }

    /// Is this cell initialized?
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.mem_contents().is_init()
    }

    /// Is this cell uninitialized?
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.mem_contents().is_uninit()
    }

    /// Value of the cell (if initialized)
    #[verifier::inline]
    pub open spec fn value(&self) -> V
        recommends
            self.is_init(),
    {
        self.mem_contents().value()
    }
}

impl<V> PCell<V> {
    /// A unique ID for the cell.
    pub uninterp spec fn id(&self) -> CellId;

    /// Return an empty ("uninitialized") cell.
    #[inline(always)]
    #[verifier::external_body]
    pub const fn empty() -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@@ === pcell_points![ pt.0.id() => MemContents::Uninit ],
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@@ === pcell_points! [ pt.0.id() => MemContents::Init(v) ],
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::new(v)) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            old(perm)@ === pcell_points![ self.id() => MemContents::Uninit ],
        ensures
            perm@ === pcell_points![ self.id() => MemContents::Init(v) ],
        opens_invariants none
        no_unwind
    {
        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm).is_init(),
        ensures
            perm.id() === old(perm)@.pcell,
            perm.mem_contents() === MemContents::Uninit,
            v === old(perm).value(),
        opens_invariants none
        no_unwind
    {
        unsafe {
            let mut m = MaybeUninit::uninit();
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm).is_init(),
        ensures
            perm.id() === old(perm)@.pcell,
            perm.mem_contents() === MemContents::Init(in_v),
            out_v === old(perm).value(),
        opens_invariants none
        no_unwind
    {
        unsafe {
            let mut m = MaybeUninit::new(in_v);
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    // The reason for the the lifetime parameter 'a is
    // that `self` actually contains the data in its interior, so it needs
    // to outlive the returned borrow.
    #[inline(always)]
    #[verifier::external_body]
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@.pcell,
            perm.is_init(),
        ensures
            *v === perm.value(),
        opens_invariants none
        no_unwind
    {
        unsafe { (*self.ucell.get()).assume_init_ref() }
    }

    //////////////////////////////////
    // Untrusted functions below here
    #[inline(always)]
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            self.id() === perm@.pcell,
            perm.is_init(),
        ensures
            v === perm.value(),
        opens_invariants none
        no_unwind
    {
        let tracked mut perm = perm;
        self.take(Tracked(&mut perm))
    }
    // TODO this should replace the external_body implementation of `new` above;
    // however it requires unstable features: const_mut_refs and const_refs_to_cell
    //#[inline(always)]
    //pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
    //    ensures (pt.1@@ === PointsToData{ pcell: pt.0.id(), value: MemContents::Init(v) }),
    //{
    //    let (p, Tracked(mut t)) = Self::empty();
    //    p.put(Tracked(&mut t), v);
    //    (p, Tracked(t))
    //}

}

impl<V: Copy> PCell<V> {
    #[inline(always)]
    #[verifier::external_body]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm).is_init(),
        ensures
            perm.id() === old(perm)@.pcell,
            perm.mem_contents() === MemContents::Init(in_v),
        opens_invariants none
        no_unwind
    {
        let _out = self.replace(Tracked(&mut *perm), in_v);
    }
}

struct InvCellPred {}

impl<T> InvariantPredicate<(Set<T>, PCell<T>), PointsTo<T>> for InvCellPred {
    closed spec fn inv(k: (Set<T>, PCell<T>), perm: PointsTo<T>) -> bool {
        let (possible_values, pcell) = k;
        {
            &&& perm.is_init()
            &&& possible_values.contains(perm.value())
            &&& pcell.id() === perm@.pcell
        }
    }
}

#[verifier::reject_recursive_types(T)]
pub struct InvCell<T> {
    possible_values: Ghost<Set<T>>,
    pcell: PCell<T>,
    perm_inv: Tracked<LocalInvariant<(Set<T>, PCell<T>), PointsTo<T>, InvCellPred>>,
}

impl<T> InvCell<T> {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        &&& self.perm_inv@.constant() === (self.possible_values@, self.pcell)
    }

    pub closed spec fn inv(&self, val: T) -> bool {
        &&& self.possible_values@.contains(val)
    }

    pub fn new(val: T, Ghost(f): Ghost<spec_fn(T) -> bool>) -> (cell: Self)
        requires
            f(val),
        ensures
            forall|v| f(v) <==> cell.inv(v),
    {
        let (pcell, Tracked(perm)) = PCell::new(val);
        let ghost possible_values = Set::new(f);
        let tracked perm_inv = LocalInvariant::new((possible_values, pcell), perm, 0);
        InvCell { possible_values: Ghost(possible_values), pcell, perm_inv: Tracked(perm_inv) }
    }
}

impl<T> InvCell<T> {
    pub fn replace(&self, val: T) -> (old_val: T)
        requires
            self.inv(val),
        ensures
            self.inv(old_val),
    {
        proof {
            use_type_invariant(self);
        }
        let r;
        open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = self.pcell.replace(Tracked(&mut perm), val);
        });
        r
    }
}

impl<T: Copy> InvCell<T> {
    pub fn get(&self) -> (val: T)
        ensures
            self.inv(val),
    {
        proof {
            use_type_invariant(self);
        }
        let r;
        open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = *self.pcell.borrow(Tracked(&perm));
        });
        r
    }
}

} // verus!
