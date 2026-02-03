#![allow(unused_imports)]

use super::super::prelude::*;
use super::CellId;
use super::pcell_maybe_uninit::*;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use verus as verus_;
verus_! {

/**
`PCell<T>` (which stands for "permissioned cell") is the most primitive Verus `Cell` type.
It can often be used as a replacement for Rust's [`UnsafeCell`], and it can serve
as a basis for verifying many other interior-mutable types
(e.g., [`InvCell`](super::invcell::InvCell),
[`RefCell`](https://github.com/verus-lang/verus/blob/main/examples/state_machines/tutorial/ref_cell.rs)).

`PCell` uses a _ghost permission token_ similar to [`simple_pptr::PPtr`](super::super::simple_pptr) -- see the [`simple_pptr::PPtr`](super::super::simple_pptr)
documentation for the basics.
For `PCell`, the associated type of the permission token is [`PointsTo`].

If you want a cell that can be optionally initialized, see [`pcell_maybe_uninit::PCell`](super::pcell_maybe_uninit::PCell).

### Differences from `PPtr`.

Whereas [`simple_pptr::PPtr`](super::super::simple_pptr) represents a fixed address in memory,
a `PCell` has _no_ fixed address because a `PCell` might be moved.
As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,
it is a unique identifier that is fixed for a given cell, even when it is moved.

The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`].
Despite the fact that it is, in some ways, "like a pointer", note that
`CellId` does not support any meangingful "pointer arithmetic,"
has no concept of a "null ID",
and has no runtime representation.

### Differences from [`UnsafeCell`](core::cell::UnsafeCell).

Though inspired by `UnsafeCell`, `PCell` is not quite the same thing.
The differences include:

 * `PCell<T>` **does not call the destructor of `T` when it goes out of scope**.
   Technically speaking, `PCell<T>` is actually implemented via
   `ManuallyDrop<UnsafeCell<T>>`. This is because dropping the contents is unsound
   if the `PointsTo<T>` is not also reclaimed. To drop a `PCell<T>` without leaking,
   call [`into_inner`](Self::into_inner) with the corresponding `PointsTo`.

 * `PCell<T>` _always_ implements `Send` and `Sync`, regardless of the type `T`.
   Instead, it is `PointsTo<T>` where the marker traits matter.
   (It doesn't matter if you move the bytes to another thread if you can't access them.)

### Example

```rust,ignore
use vstd::prelude::*;
use vstd::cell::pcell as pc;

verus! {

fn example_pcell() {
    let (cell, Tracked(mut points_to)) = pc::PCell::new(5);

    assert(points_to.id() == cell.id());
    assert(points_to.value() == 5);

    cell.write(Tracked(&mut points_to), 17);

    assert(points_to.id() == cell.id());
    assert(points_to.value() == 17);

    let x = cell.into_inner(Tracked(points_to));
    assert(x == 17);
}

} // verus!
```
*/

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct PCell<T: ?Sized> {
    // Unlike UnsafeCell, a PCell's drop should NOT drop the contents (since we do not have
    // the permissions to access the contents). To prevent this, we need to use ManuallyDrop
    ucell: ManuallyDrop<UnsafeCell<T>>,
}

/// `PCell` is _always_ safe to `Send` or `Sync`. Rather, it is the [`PointsTo`] object where `Send` and `Sync` matter.
/// (It doesn't matter if you move the bytes to another thread if you can't access them.)
#[verifier::external]
unsafe impl<T: ?Sized> Sync for PCell<T> { }
#[verifier::external]
unsafe impl<T: ?Sized> Send for PCell<T> { }

/// Permission object associated with a [`PCell<T>`].
///
/// See the documentation of [`PCell<T>`] for more information.
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub tracked struct PointsTo<T: ?Sized> {
    // Through PhantomData we inherit the Send/Sync marker traits
    phantom: PhantomData<T>,
    no_copy: NoCopy,
}

impl<T: ?Sized> PointsTo<T> {
    /// The [`CellId`] of the [`PCell`] this permission is associated with.
    pub uninterp spec fn id(&self) -> CellId;

    // To support ?Sized, the `.value()` has to return a reference.
    // This restriction is enforced by rust even in spec code.

    /// The contents of the cell.
    pub uninterp spec fn value(&self) -> &T;
}

impl<T: ?Sized> PCell<T> {
    /// A unique ID for the cell.
    pub uninterp spec fn id(&self) -> CellId;

    /// Construct a new `PCell` with a fresh [`id`](Self::id).
    #[inline(always)]
    #[verifier::external_body]
    pub const fn new(v: T) -> (pt: (PCell<T>, Tracked<PointsTo<T>>))
        where T: Sized
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
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsTo<T>>) -> (v: &'a T)
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
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<T>>, in_v: T) -> (out_v: T)
        where T: Sized
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
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<T>>) -> (v: T)
        where T: Sized
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
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<T>>, in_v: T)
        where T: Sized
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
    pub fn read(&self, Tracked(perm): Tracked<&PointsTo<T>>) -> (out_v: T)
        where T: Copy + Sized
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
