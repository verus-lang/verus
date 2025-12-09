#![allow(unused_imports)]

use super::super::prelude::*;
use super::pcell_maybe_uninit::*;
use super::CellId;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use verus as verus_;
verus_! {

/// `PCell<V>` (which stands for "permissioned call") is the most primitive Verus `Cell` type.
///
/// Technically, it is a wrapper around
/// `core::cell::UnsafeCell<V>`, and thus has the same runtime
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
/// `PCell` uses a _ghost permission token_ similar to [`simple_pptr::PPtr`](super::super::simple_pptr) -- see the [`simple_pptr::PPtr`](super::super::simple_pptr)
/// documentation for the basics.
/// For `PCell`, the associated type of the permission token is [`PointsTo`].
///
/// ### Differences from `PPtr`.
///
/// The key difference is that, whereas [`simple_pptr::PPtr`](super::super::simple_pptr) represents a fixed address in memory,
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
/// If you want a cell that can be optionally initialized, see [`PCellUn`].
///
/// ### Example (TODO)

#[verifier::external_body]
#[verifier::accept_recursive_types(V)]
pub struct PCell<V: ?Sized> {
    // Unlike UnsafeCell, a PCell's drop should NOT drop the contents (since we do not have
    // the permissions to access the contents). To prevent this, we need to use ManuallyDrop
    ucell: ManuallyDrop<UnsafeCell<V>>,
}

/// `PCell` is _always_ safe to `Send` or `Sync`. Rather, it is the [`PointsTo`] object where `Send` and `Sync` matter.
/// (It doesn't matter if you move the bytes to another thread if you can't access them.)
#[verifier::external]
unsafe impl<T: ?Sized> Sync for PCell<T> { }
#[verifier::external]
unsafe impl<T: ?Sized> Send for PCell<T> { }

/// Permission object associated with a [`PCell<V>`].
///
/// See the documentation of [`PCell<V>`] for more information.
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsTo<V: ?Sized> {
    // Through PhantomData we inherit the Send/Sync marker traits
    phantom: PhantomData<V>,
    no_copy: NoCopy,
}

impl<V: ?Sized> PointsTo<V> {
    /// The [`CellId`] of the [`PCell`] this permission is associated with.
    pub uninterp spec fn id(&self) -> CellId;

    // To support ?Sized, the `.value()` has to return a reference.
    // This restriction is enforced by rust even in spec code.

    /// The contents of the cell.
    pub uninterp spec fn value(&self) -> &V;
}

impl<V: ?Sized> PCell<V> {
    /// A unique ID for the cell.
    pub uninterp spec fn id(&self) -> CellId;

    /// Construct a new `PCell` with a fresh [`id`](Self::id).
    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        where V: Sized
        ensures
            pt.1@.id() == pt.0.id() && pt.1@.value() == v
        opens_invariants none
        no_unwind
    {
        let p = PCell { ucell: ManuallyDrop::new(UnsafeCell::new(v)) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm.id(),
        ensures
            v === perm.value(),
        opens_invariants none
        no_unwind
    {
        // SAFETY: We can take a shared reference since we have the shared PointsTo
        unsafe { &(*(*self.ucell).get()) }
    }

    // TODO: this should be replaced with borrow_mut
    #[inline(always)]
    #[verifier::external_body]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        where V: Sized
        requires
            self.id() === old(perm).id(),
        ensures
            perm.id() === old(perm).id(),
            *perm.value() === in_v,
            out_v === *old(perm).value(),
        opens_invariants none
        no_unwind
    {
        let mut m = in_v;
        // SAFETY: We can take a mutable reference since we have the mutable PointsTo
        unsafe {
            core::mem::swap(&mut m, &mut *(*self.ucell).get());
        }
        m
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        where V: Sized
        requires
            self.id() === perm.id(),
        ensures
            v === *perm.value(),
        opens_invariants none
        no_unwind
    {
        // Note that for an UnsafeCell, intro_inner is a safe operation, whereas for PCell,
        // we require the Tracked permission.
        ManuallyDrop::into_inner(self.ucell).into_inner()
    }

    ////// Trusted core ends here

    #[inline(always)]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        where V: Sized
        requires
            self.id() === old(perm).id()
        ensures
            perm.id() === old(perm).id(),
            *perm.value() === in_v,
        opens_invariants none
        no_unwind
    {
        let _out = self.replace(Tracked(&mut *perm), in_v);
    }

    #[inline(always)]
    pub fn read(&self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V)
        where V: Copy + Sized
        requires
            self.id() === perm.id()
        returns
            *perm.value()
        opens_invariants none
        no_unwind
    {
        *self.borrow(Tracked(perm))
    }
}

}
