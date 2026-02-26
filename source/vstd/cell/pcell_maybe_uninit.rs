#![allow(unused_imports)]

use super::super::prelude::*;
use super::super::raw_ptr::MemContents;
use super::CellId;
use super::pcell as pc;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::mem::MaybeUninit;

use verus as verus_;
verus_! {

/**
Variant of [`pcell::PCell<V>`](super::pcell::PCell) for potentially uninitialized data.

See the [`pcell::PCell<V>`](super::pcell::PCell) docs for a high-level overview.

### Example

```rust,ignore
use vstd::prelude::*;
use vstd::cell::pcell_maybe_uninit as un;
use vstd::raw_ptr::MemContents;

verus! {

fn example_pcell_maybe_uninit() {
    let (cell, Tracked(mut points_to)) = un::PCell::new(5);

    assert(points_to.id() == cell.id());
    assert(points_to.mem_contents() === MemContents::Init(5));

    let x = cell.take(Tracked(&mut points_to));
    assert(x == 5);

    assert(points_to.id() == cell.id());
    assert(points_to.mem_contents() === MemContents::Uninit);

    cell.put(Tracked(&mut points_to), 17);

    assert(points_to.id() == cell.id());
    assert(points_to.mem_contents() === MemContents::Init(17));
}

} // verus!
*/

pub struct PCell<V>(pc::PCell<MaybeUninit<V>>);

/// Permission object associated with a [`PCell<V>`].
///
/// See the documentation of [`PCell<V>`] for more information.
pub tracked struct PointsTo<V>(pc::PointsTo<MaybeUninit<V>>);

impl<V> PointsTo<V> {
    /// The [`CellId`] of the [`PCell`] this permission is associated with.
    pub closed spec fn id(&self) -> CellId {
        self.0.id()
    }

    /// The contents of the cell.
    pub closed spec fn mem_contents(&self) -> MemContents<V> {
        self.0.value().mem_contents()
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
    pub closed spec fn id(&self) -> CellId {
        self.0.id()
    }

    /// Return an empty ("uninitialized") cell.
    #[inline(always)]
    pub const fn empty() -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@.id() == pt.0.id(),
            pt.1@.mem_contents() === MemContents::Uninit,
    {
        let (pcell, Tracked(pt)) = pc::PCell::new(MaybeUninit::uninit());
        (PCell(pcell), Tracked(PointsTo(pt)))
    }

    #[inline(always)]
    pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@.id() == pt.0.id(),
            pt.1@.mem_contents() == MemContents::Init(v),
    {
        let (pcell, Tracked(pt)) = pc::PCell::new(MaybeUninit::new(v));
        (PCell(pcell), Tracked(PointsTo(pt)))
    }

    #[inline(always)]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            old(perm).id() == self.id(),
            old(perm).mem_contents() === MemContents::Uninit,
        ensures
            perm.id() == self.id(),
            perm.mem_contents() === MemContents::Init(in_v),
        opens_invariants none
        no_unwind
    {
        self.0.replace(Tracked(&mut perm.0), MaybeUninit::new(in_v));
    }

    #[inline(always)]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (out_v: V)
        requires
            self.id() === old(perm).id(),
            old(perm).is_init(),
        ensures
            perm.id() === old(perm).id(),
            perm.mem_contents() === MemContents::Uninit,
            out_v === old(perm).value(),
        opens_invariants none
        no_unwind
    {
        unsafe {
            self.0.replace(Tracked(&mut perm.0), MaybeUninit::uninit()).assume_init()
        }
    }

    #[inline(always)]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm).id(),
            old(perm).is_init(),
        ensures
            perm.id() === old(perm).id(),
            perm.mem_contents() === MemContents::Init(in_v),
            out_v === old(perm).value(),
        opens_invariants none
        no_unwind
    {
        unsafe {
            self.0.replace(Tracked(&mut perm.0), MaybeUninit::new(in_v)).assume_init()
        }
    }

    #[inline(always)]
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm.id(),
            perm.is_init(),
        ensures
            *v === perm.value(),
        opens_invariants none
        no_unwind
    {
        unsafe {
            self.0.borrow(Tracked(&perm.0)).assume_init_ref()
        }
    }

    #[inline(always)]
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            self.id() === perm.id(),
            perm.is_init(),
        ensures
            v === perm.value(),
        opens_invariants none
        no_unwind
    {
        let tracked mut perm = perm;
        self.take(Tracked(&mut perm))
    }

    #[inline(always)]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            self.id() === old(perm).id(),
        ensures
            perm.id() === old(perm).id(),
            perm.mem_contents() === MemContents::Init(in_v),
        opens_invariants none
        no_unwind
    {
        self.0.replace(Tracked(&mut perm.0), MaybeUninit::new(in_v));
    }

    #[inline(always)]
    pub fn read(&self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V)
        where V: Copy
        requires
            self.id() === perm.id(),
            perm.is_init(),
        returns
            perm.value()
        opens_invariants none
        no_unwind
    {
        *self.borrow(Tracked(perm))
    }
}

}
