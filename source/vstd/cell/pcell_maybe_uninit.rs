#![allow(unused_imports)]

use super::super::prelude::*;
use super::super::raw_ptr::MemContents;
use super::pcell::*;
use super::CellId;
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::mem::MaybeUninit;

use verus as verus_;
verus_! {

/// Variant of [`PCell<V>`] for potentially uninitialized data.

pub struct PCellUn<V>(PCell<MaybeUninit<V>>);

/// Permission object associated with a [`PCellUn<V>`].
///
/// See the documentation of [`PCellUn<V>`] for more information.
pub tracked struct PointsToUn<V>(PointsTo<MaybeUninit<V>>);

impl<V> PointsToUn<V> {
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

impl<V> PCellUn<V> {
    /// A unique ID for the cell.
    pub closed spec fn id(&self) -> CellId {
        self.0.id()
    }

    /// Return an empty ("uninitialized") cell.
    #[inline(always)]
    pub const fn empty() -> (pt: (PCellUn<V>, Tracked<PointsToUn<V>>))
        ensures
            pt.1@.id() == pt.0.id(),
            pt.1@.mem_contents() === MemContents::Uninit,
    {
        let (pcell, Tracked(pt)) = PCell::new(MaybeUninit::uninit());
        (PCellUn(pcell), Tracked(PointsToUn(pt)))
    }

    #[inline(always)]
    pub const fn new(v: V) -> (pt: (PCellUn<V>, Tracked<PointsToUn<V>>))
        ensures
            pt.1@.id() == pt.0.id(),
            pt.1@.mem_contents() == MemContents::Init(v),
    {
        let (pcell, Tracked(pt)) = PCell::new(MaybeUninit::new(v));
        (PCellUn(pcell), Tracked(PointsToUn(pt)))
    }

    #[inline(always)]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsToUn<V>>, in_v: V)
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
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsToUn<V>>) -> (out_v: V)
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
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsToUn<V>>, in_v: V) -> (out_v: V)
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
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsToUn<V>>) -> (v: &'a V)
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
    pub fn into_inner(self, Tracked(perm): Tracked<PointsToUn<V>>) -> (v: V)
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
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsToUn<V>>, in_v: V)
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
    pub fn read(&self, Tracked(perm): Tracked<&PointsToUn<V>>) -> (out_v: V)
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
