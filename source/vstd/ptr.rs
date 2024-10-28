#![cfg_attr(
    not(verus_verify_core),
    deprecated = "The vstd::ptr version of PPtr is deprecated. Use either:\n -- `PPtr<T>` in vstd::simple_pptr (for simple use-cases, with fixed-size typed heap allocations)\n -- `*mut T` with vstd::raw_ptr (for more advanced use-cases)"
)]
#![allow(unused_imports)]
#![allow(deprecated)]

use alloc::alloc::Layout;
use core::{marker, mem, mem::MaybeUninit};

use super::layout::*;
use super::modes::*;
use super::pervasive::*;
use super::prelude::*;
use super::*;
use builtin::*;
use builtin_macros::*;

#[cfg(verus_keep_ghost)]
use super::set_lib::set_int_range;

verus! {

/// `PPtr<V>` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to `V` on the heap.
///
/// Technically, it is a wrapper around `*mut mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `PointsTo<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&PointsTo<V>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * `perm.pptr` is the pointer that the permission is associated to,
///     given by [`ptr.id()`](PPtr::id).
///  * `perm.value` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `T` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PointsTo` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Example (TODO)
// Notes about pointer provenance:
//
// "Pointer provenance" is this complicated subject which is a necessary
// evil if you want to understand the abstract machine semantics of a language
// with pointers and what is or is not UB with int-to-pointer casts.
//
// See this series of blog posts for some introduction:
// https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html
//
// Here in Verus, where code is forced to be verified, we want to tell
// a much simpler story, which is the following:
//
//   ***** VERUS POINTER MODEL *****
//    "Provenance" comes from the `tracked ghost` PointsTo object.
//   *******************************
//
// Pretty simple, right?
//
// Of course, this trusted pointer library still needs to actually run and
// be sound in the Rust backend.
// Rust's abstract pointer model is unchanged, and it doesn't know anything
// about Verus's special ghost `PointsTo` object, which gets erased, anyway.
//
// Maybe someday the ghost PointsTo model will become a real
// memory model. That isn't true today.
// So we still need to know something about actual, real memory models that
// are used right now in order to implement this API soundly.
//
// Our goal is to allow the *user of Verus* to think in terms of the
// VERUS POINTER MODEL where provenance is tracked via the `PointsTo` object.
// The rest of this is just details for the trusted implementation of PPtr
// that will be sound in the Rust backend.
//
// In the "PNVI-ae-udi" model:
//  * A ptr->int cast "exposes" a pointer (adding it some global list in the
//    abstract machine)
//  * An int->ptr cast acquires the provenance of that pointer only if it
//    was previously exposed.
//
// The "tower of weakenings", however,
// (see https://gankra.github.io/blah/tower-of-weakenings/)
// proposes a stricter model called "Strict Provenance".
// This basically forbids exposing and requires provenance to always be tracked.
//
// If possible, it would be nice to stick to this stricter model, but it isn't necessary.
//
// Unfortunately, it's not possible. The Strict Provenance requires "provenance" to be
// tracked through non-ghost pointers. We can't use our ghost objects to track provenance
// in general while staying consistent with Strict Provenance.
//
// We have two options:
//
//  1. Just forbid int->ptr conversions
//  2. Always "expose" every PPtr when it's created, in order to definitely be safe
//     under PNVI-ae-udi.
//
// However, int->ptr conversions ought to be allowed in the VERUS POINTER MODEL,
// so I'm going with (2) here.
//
// TODO reconsider: Is this plan actually good? Exposing all pointers has the potential
// to ruin optimizations. If the plan is bad, and we want to avoid the cost of
// "expose-everywhere", we may need to actually track provenance as part
// of the specification of PPtr.
//
// Perhaps what we could do is specify a low-level pointer library with
// strict provenance rules + exposed pointers,
// and then verify user libraries on top of that?
// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?
// TODO just replace this with `*mut V`
#[repr(C)]
#[verifier::accept_recursive_types(V)]
pub struct PPtr<V> {
    pub uptr: *mut V,
}

// PPtr is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.
#[verifier::external]
unsafe impl<T> Sync for PPtr<T> {

}

#[verifier::external]
unsafe impl<T> Send for PPtr<T> {

}

// TODO some of functionality could have V: ?Sized
/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsTo<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

/// Represents the meaning of a [`PointsTo`] object.
pub ghost struct PointsToData<V> {
    /// Indicates that this token is for a pointer `ptr: PPtr<V>`
    /// such that [`ptr.id()`](PPtr::id) equal to this value.
    pub pptr: int,
    /// Indicates that this token gives the ability to read a value `V` from memory.
    /// When `None`, it indicates that the memory is uninitialized.
    pub value: Option<V>,
}

// TODO add similiar height axioms for other ghost objects
pub broadcast proof fn points_to_height_axiom<V>(points_to: PointsTo<V>)
    ensures
        #[trigger] is_smaller_than(points_to@, points_to),
{
    admit();
}

pub broadcast group group_ptr_axioms {
    points_to_height_axiom,
}

/// Points to uninitialized memory.
#[verifier::external_body]
pub tracked struct PointsToRaw {
    no_copy: NoCopy,
}

#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct Dealloc<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct DeallocData {
    pub pptr: int,
}

#[verifier::external_body]
pub tracked struct DeallocRaw {
    no_copy: NoCopy,
}

pub ghost struct DeallocRawData {
    pub pptr: int,
    pub size: nat,
    pub align: nat,
}

impl<V> PointsTo<V> {
    pub spec fn view(self) -> PointsToData<V>;

    /// Any dereferenceable pointer must be non-null.
    /// (Note that null pointers _do_ exist and are representable by `PPtr`;
    /// however, it is not possible to obtain a `PointsTo` token for
    /// any such a pointer.)
    #[verifier::external_body]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn leak_contents(tracked &mut self)
        ensures
            self@.pptr == old(self)@.pptr && self@.value.is_None(),
    {
        unimplemented!();
    }
}

impl<V> PointsTo<V> {
    #[verifier::external_body]
    pub proof fn into_raw(tracked self) -> (tracked points_to_raw: PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw.is_range(self@.pptr, size_of::<V>() as int),
            is_sized::<V>(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn borrow_raw(tracked &self) -> (tracked points_to_raw: &PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw.is_range(self@.pptr, size_of::<V>() as int),
            is_sized::<V>(),
    {
        unimplemented!();
    }
}

impl PointsToRaw {
    pub spec fn view(self) -> Map<int, u8>;

    pub open spec fn contains_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len).subset_of(self@.dom())
    }

    pub open spec fn is_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self@.dom()
    }

    #[verifier::inline]
    pub open spec fn spec_index(self, i: int) -> u8 {
        self@[i]
    }

    #[verifier::external_body]
    pub proof fn is_nonnull(tracked &self)
        ensures
            !self@.dom().contains(0),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn is_in_bounds(tracked &self)
        ensures
            forall|i: int| self@.dom().contains(i) ==> 0 < i <= usize::MAX,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn empty() -> (tracked points_to_raw: Self)
        ensures
            points_to_raw@ == Map::<int, u8>::empty(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn into_typed<V>(tracked self, start: usize) -> (tracked points_to: PointsTo<V>)
        requires
            is_sized::<V>(),
            start as int % align_of::<V>() as int == 0,
            self.is_range(start as int, size_of::<V>() as int),
        ensures
            points_to@.pptr == start,
            points_to@.value === None,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn borrow_typed<V>(tracked &self, start: int) -> (tracked points_to: &PointsTo<V>)
        requires
            is_sized::<V>(),
            start % align_of::<V>() as int == 0,
            self.contains_range(start, size_of::<V>() as int),
        ensures
            points_to@.pptr === start,
            points_to@.value === None,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        ensures
            self@.dom().disjoint(other@.dom()),
            joined@ == self@.union_prefer_right(other@),
    {
        unimplemented!();
    }

    pub proof fn insert(tracked &mut self, tracked other: Self)
        ensures
            old(self)@.dom().disjoint(other@.dom()),
            self@ == old(self)@.union_prefer_right(other@),
    {
        let tracked mut tmp = Self::empty();
        tracked_swap(&mut tmp, self);
        tmp = tmp.join(other);
        tracked_swap(&mut tmp, self);
    }

    #[verifier::external_body]
    pub proof fn borrow_join<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked joined:
        &'a Self)
        ensures
            (forall|i|
                #![trigger self@.dom().contains(i), other@.dom().contains(i)]
                self@.dom().contains(i) && other@.dom().contains(i) ==> self@[i] == other@[i]),
            joined@ == self@.union_prefer_right(other@),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn split(tracked self, range: Set<int>) -> (tracked res: (Self, Self))
        requires
            range.subset_of(self@.dom()),
        ensures
            res.0@ == self@.restrict(range),
            res.1@ == self@.remove_keys(range),
    {
        unimplemented!();
    }

    pub proof fn take(tracked &mut self, range: Set<int>) -> (tracked res: Self)
        requires
            range.subset_of(old(self)@.dom()),
        ensures
            res@ == old(self)@.restrict(range),
            self@ == old(self)@.remove_keys(range),
    {
        let tracked mut tmp = Self::empty();
        tracked_swap(&mut tmp, self);
        let tracked (l, mut r) = tmp.split(range);
        tracked_swap(&mut r, self);
        l
    }

    #[verifier::external_body]
    pub proof fn borrow_subset(tracked &self, range: Set<int>) -> (tracked res: &Self)
        requires
            range.subset_of(self@.dom()),
        ensures
            res@ == self@.restrict(range),
    {
        unimplemented!();
    }
}

impl<V> Dealloc<V> {
    pub spec fn view(self) -> DeallocData;
}

impl<V> Dealloc<V> {
    #[verifier::external_body]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn into_raw(tracked self) -> (tracked dealloc_raw: DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
            is_sized::<V>(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn borrow_raw(tracked &self) -> (tracked dealloc_raw: &DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
            is_sized::<V>(),
    {
        unimplemented!();
    }
}

impl DeallocRaw {
    pub spec fn view(self) -> DeallocRawData;

    #[verifier::external_body]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn into_typed<V>(tracked self) -> (tracked dealloc: Dealloc<V>)
        requires
            is_sized::<V>(),
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn borrow_typed<V>(tracked &self) -> (tracked dealloc: &Dealloc<V>)
        requires
            is_sized::<V>(),
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }
}

impl<A> Clone for PPtr<A> {
    #[verifier::external_body]
    fn clone(&self) -> (s: Self)
        ensures
            s == *self,
    {
        PPtr { uptr: self.uptr }
    }
}

impl<A> Copy for PPtr<A> {

}

impl<V> PPtr<V> {
    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier::external_body]
    pub fn to_usize(&self) -> (u: usize)
        ensures
            u as int == self.id(),
    {
        self.uptr as usize
    }

    /// integer address of the pointer
    pub spec fn id(&self) -> int;

    /// Cast an integer to a pointer.
    ///
    /// Note that this does _not_ require or ensure that the pointer is valid.
    /// Of course, if the user creates an invalid pointer, they would still not be able to
    /// create a valid [`PointsTo`] token for it, and thus they would never
    /// be able to access the data behind the pointer.
    ///
    /// This is analogous to normal Rust, where casting to a pointer is always possible,
    /// but dereferencing a pointer is an `unsafe` operation.
    /// In Verus, casting to a pointer is likewise always possible,
    /// while dereferencing it is only allowed when the right preconditions are met.
    #[inline(always)]
    #[verifier::external_body]
    pub fn from_usize(u: usize) -> (p: Self)
        ensures
            p.id() == u as int,
    {
        let uptr = u as *mut V;
        PPtr { uptr }
    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.
    #[inline(always)]
    #[verifier::external_body]
    pub fn empty() -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            pt.1@@ === (PointsToData { pptr: pt.0.id(), value: None }),
            pt.2@@ === (DeallocData { pptr: pt.0.id() }),
        opens_invariants none
    {
        let layout = Layout::new::<V>();
        let size = layout.size();
        let align = layout.align();
        let (p, _, _) = PPtr::<V>::alloc(size, align);
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn alloc(size: usize, align: usize) -> (pt: (
        PPtr<V>,
        Tracked<PointsToRaw>,
        Tracked<DeallocRaw>,
    ))
        requires
            valid_layout(size, align),
        ensures
            pt.1@.is_range(pt.0.id(), size as int),
            pt.2@@ === (DeallocRawData { pptr: pt.0.id(), size: size as nat, align: align as nat }),
            pt.0.id() % align as int == 0,
        opens_invariants none
    {
        // Add padding (this is to prevent the user from being able to "combine" allocations)
        // Constructing the layout object might fail if the allocation becomes too big.
        // The 'add' can't overflow, since we already know (size, align) is a valid layout.
        let layout = Layout::from_size_align(size + align, align).unwrap();
        let p = PPtr { uptr: unsafe { ::alloc::alloc::alloc(layout) as *mut V } };
        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.
    #[inline(always)]
    #[verifier::external_body]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value === None,
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(v),
        opens_invariants none
        no_unwind
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe {
            // We use `write` here because it does not attempt to "drop" the memory at `*ptr`.
            core::ptr::write(ptr, v);
        }
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.
    #[inline(always)]
    #[verifier::external_body]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === None,
            v === old(perm)@.value.get_Some_0(),
        opens_invariants none
        no_unwind
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe { core::ptr::read(ptr) }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.
    #[inline(always)]
    #[verifier::external_body]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(in_v),
            out_v === old(perm)@.value.get_Some_0(),
        opens_invariants none
        no_unwind
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe {
            let mut m = in_v;
            mem::swap(&mut m, &mut *ptr);
            m
        }
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
    // Note that `self` is just a pointer, so it doesn't need to outlive
    // the returned borrow.
    #[inline(always)]
    #[verifier::external_body]
    pub fn borrow<'a>(&self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures
            *v === perm@.value.get_Some_0(),
        opens_invariants none
        no_unwind
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe { &*ptr }
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.
    #[inline(always)]
    #[verifier::external_body]
    pub fn dispose(
        &self,
        Tracked(perm): Tracked<PointsTo<V>>,
        Tracked(dealloc): Tracked<Dealloc<V>>,
    )
        requires
            self.id() === perm@.pptr,
            perm@.value === None,
            perm@.pptr == dealloc@.pptr,
        opens_invariants none
    {
        unsafe {
            let layout = alloc::alloc::Layout::for_value(&*self.uptr);
            let size = layout.size();
            let align = layout.align();
            // Add the padding to match what we did in 'alloc'
            let layout = Layout::from_size_align_unchecked(size + align, align);
            ::alloc::alloc::dealloc(self.uptr as *mut u8, layout);
        }
    }

    #[inline(always)]
    #[verifier::external_body]
    pub fn dealloc(
        &self,
        size: usize,
        align: usize,
        Tracked(perm): Tracked<PointsToRaw>,
        Tracked(dealloc): Tracked<DeallocRaw>,
    )
        requires
            perm.is_range(self.id(), size as int),
            dealloc@.pptr === self.id(),
            dealloc@.size === size as nat,
            dealloc@.align === align as nat,
        opens_invariants none
    {
        unsafe {
            // Since we have the Dealloc object, we know this is a valid layout
            // and that it's safe to call 'deallocate'
            // Remember to add the padding, like in `alloc`
            let layout = Layout::from_size_align_unchecked(size + align, align);
            ::alloc::alloc::dealloc(self.uptr as *mut u8, layout);
        }
    }

    //////////////////////////////////
    // Verified library functions below here
    /// Free the memory pointed to be `perm` and return the
    /// value that was previously there.
    /// Requires the memory to be initialized.
    /// This consumes the [`PointsTo`] token, since the user is giving up
    /// access to the memory by freeing it.
    #[inline(always)]
    pub fn into_inner(
        self,
        Tracked(perm): Tracked<PointsTo<V>>,
        Tracked(dealloc): Tracked<Dealloc<V>>,
    ) -> (v: V)
        requires
            self.id() === perm@.pptr,
            perm@.pptr == dealloc@.pptr,
            perm@.value.is_Some(),
        ensures
            v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        let v = self.take(Tracked(&mut perm));
        self.dispose(Tracked(perm), Tracked(dealloc));
        v
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.
    #[inline(always)]
    pub fn new(v: V) -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            (pt.1@@ === PointsToData { pptr: pt.0.id(), value: Some(v) }),
            (pt.2@@ === DeallocData { pptr: pt.0.id() }),
    {
        let (p, Tracked(mut t), Tracked(d)) = Self::empty();
        p.put(Tracked(&mut t), v);
        (p, Tracked(t), Tracked(d))
    }
}

impl<V: Copy> PPtr<V> {
    #[inline(always)]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            self.id() === old(perm)@.pptr,
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(in_v),
        opens_invariants none
        no_unwind
    {
        proof {
            perm.leak_contents();
        }
        self.put(Tracked(&mut *perm), in_v);
    }

    #[inline(always)]
    pub fn read(&self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures
            perm@.value === Some(out_v),
        opens_invariants none
        no_unwind
    {
        *self.borrow(Tracked(&*perm))
    }
}

// Manipulating the contents in a PointsToRaw
impl PPtr<u8> {
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))]
    #[verifier::external_body]
    fn copy_nonoverlapping(
        &self,
        dst: PPtr<u8>,
        count: usize,
        perm_src: &PointsToRaw,
        perm_dst: &mut PointsToRaw,
    )
        requires
            perm_src.contains_range(self.id(), count as int),
            old(perm_dst).contains_range(dst.id(), count as int),
        ensures
            perm_dst@ == old(perm_dst)@.union_prefer_right(
                perm_src@.restrict(set_int_range(self.id(), self.id() + count)),
            ),
    {
        unsafe { core::ptr::copy_nonoverlapping(self.uptr, dst.uptr, count) }
    }

    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))]
    #[verifier::external_body]
    fn write_bytes(&self, val: u8, count: usize, perm: &mut PointsToRaw)
        requires
            old(perm).contains_range(self.id(), count as int),
        ensures
            perm@ == old(perm)@.union_prefer_right(
                Map::new(
                    |addr| set_int_range(self.id(), self.id() + count).contains(addr),
                    |addr| val,
                ),
            ),
    {
        unsafe {
            core::ptr::write_bytes::<u8>(self.uptr, val, count);
        }
    }
}

} // verus!
