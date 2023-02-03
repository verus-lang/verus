#![allow(unused_imports)]

extern crate alloc;
use alloc::alloc::Layout;
use core::marker;
use core::mem;
use alloc::alloc::Allocator;

use builtin::*;
use builtin_macros::*;
use crate::pervasive::*;
use crate::pervasive::modes::*;
use crate::pervasive::option::*;

verus!{

// TODO
pub trait SizeOf {
    spec fn size_of() -> nat;
    spec fn align_of() -> nat;
}

pub open spec fn is_power_2(n: int) -> bool
  decreases n
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_power_2(n / 2)
    }
}

/// Matches the conditions here: https://doc.rust-lang.org/stable/std/alloc/struct.Layout.html
pub open spec fn valid_layout(size: usize, align: usize) -> bool {
    is_power_2(align as int)
      && size <= isize::MAX as int - (isize::MAX as int % align as int)
}

#[verifier(inline)]
pub open spec fn size_of<V: SizeOf>() -> nat {
    V::size_of()
}

#[verifier(inline)]
pub open spec fn align_of<V: SizeOf>() -> nat {
    V::size_of()
}

#[verifier(external_body)]
pub fn get_size_of<V: SizeOf>() -> (u: usize)
    ensures u as nat == size_of::<V>()
{
    core::mem::size_of::<V>()
}

#[verifier(external_body)]
pub fn get_align_of<V: SizeOf>() -> (u: usize)
    ensures u as nat == align_of::<V>()
{
    core::mem::align_of::<V>()
}

// TODO check that this is sound
#[verifier(external_body)]
pub proof fn layout_for_type_is_valid<V: SizeOf>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
{ unimplemented!() }

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
// TODO to be sound under the above plan, we need to acquire provenance from
// exposed pointers each time we do a pointer dereference?
//
// TODO reconsider: Is this plan actually good? Exposing all pointers has the potential
// to ruin optimizations. If the plan is bad, and we want to avoid the cost of
// "expose-everywhere", we may need to actually track provenance as part
// of the specification of PPtr.

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

// TODO just replace this with `*mut V`
#[verifier(external_body)]
pub struct PPtr<#[verifier(strictly_positive)] V> {
    uptr: *mut V,
}

// PPtr is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.

#[verifier(external)]
unsafe impl<T> Sync for PPtr<T> {}

#[verifier(external)]
unsafe impl<T> Send for PPtr<T> {}

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.

#[verifier(external_body)]
pub tracked struct PointsTo<#[verifier(strictly_positive)] V> {
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

    pub value: option::Option<V>,
}

/// Points to uninitialized memory.

#[verifier(external_body)]
pub tracked struct PointsToRaw {
    no_copy: NoCopy,
}

pub ghost struct PointsToRawData {
    pub pptr: int,
    pub size: nat,
}

#[verifier(external_body)]
pub tracked struct Dealloc<#[verifier(strictly_positive)] V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct DeallocData {
    pub pptr: int,
}

#[verifier(external_body)]
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

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn leak_contents(tracked &mut self)
        ensures self@.pptr == old(self)@.pptr && self@.value.is_None(),
    {
        unimplemented!();
    }
}

impl<V: SizeOf> PointsTo<V> {
    #[verifier(external_body)]
    pub proof fn into_raw(tracked self) -> (tracked points_to_raw: PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw@.pptr === self@.pptr,
            points_to_raw@.size === size_of::<V>(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_raw(tracked &self) -> (tracked points_to_raw: &PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw@.pptr === self@.pptr,
            points_to_raw@.size === size_of::<V>(),
    {
        unimplemented!();
    }
}

impl PointsToRaw {
    pub spec fn view(self) -> PointsToRawData;

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn empty() -> (tracked points_to_raw: Self)
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_typed<V: SizeOf>(tracked self) -> (tracked points_to: PointsTo<V>)
        requires
            self@.size === size_of::<V>(),
            self@.pptr % align_of::<V>() as int === 0,
        ensures
            points_to@.pptr === self@.pptr,
            points_to@.value === Option::None,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_typed<V: SizeOf>(tracked &self) -> (tracked points_to: &PointsTo<V>)
        requires
            self@.size === size_of::<V>(),
            self@.pptr % align_of::<V>() as int == 0,
        ensures
            points_to@.pptr === self@.pptr,
            points_to@.value === Option::None,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self@.pptr + self@.size == other@.pptr,
        ensures
            joined@.pptr == self@.pptr,
            joined@.size == self@.size + other@.size
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_join(tracked &self, tracked other: &Self) -> (tracked joined: &Self)
        requires
            self@.pptr + self@.size == other@.pptr,
        ensures
            joined@.pptr == self@.pptr,
            joined@.size == self@.size + other@.size
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn split(tracked self, len1: int) -> (tracked res: (Self, Self))
        requires
            len1 <= self@.size
        ensures
            res.0@.pptr == self@.pptr,
            res.0@.size == len1,
            res.1@.pptr == self@.pptr + len1,
            res.1@.size == self@.size - len1,
    {
        unimplemented!();
    }
            
    #[verifier(external_body)]
    pub proof fn borrow_split(tracked &self, len1: int) -> (tracked res: (&Self, &Self))
        requires
            len1 <= self@.size
        ensures
            res.0@.pptr == self@.pptr,
            res.0@.size == len1,
            res.1@.pptr == self@.pptr + len1,
            res.1@.size == self@.size - len1,
    {
        unimplemented!();
    }
}

impl<V> Dealloc<V> {
    pub spec fn view(self) -> DeallocData;
}

impl<V: SizeOf> Dealloc<V> {
    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_raw(tracked self) -> (tracked dealloc_raw: DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_raw(tracked &self) -> (tracked dealloc_raw: &DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
    {
        unimplemented!();
    }
}

impl DeallocRaw {
    pub spec fn view(self) -> DeallocRawData;

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_typed<V: SizeOf>(tracked self) -> (tracked dealloc: Dealloc<V>)
        requires
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_typed<V: SizeOf>(tracked &self) -> (tracked dealloc: &Dealloc<V>)
        requires
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }
}

impl<V> PPtr<V> {
    /// Cast a pointer to an integer.

    #[inline(always)]
    #[verifier(external_body)]
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
    #[verifier(external_body)]
    pub fn from_usize(u: usize) -> (p: Self)
        ensures p.id() == u as int,
    {
        let uptr = u as *mut V;
        PPtr { uptr }
    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            pt.1@@ === (PointsToData{ pptr: pt.0.id(), value: option::Option::None }),
            pt.2@@ === (DeallocData{ pptr: pt.0.id() }),
    {
        opens_invariants_none();

        // TODO abort on unwrap-failure
        let p = PPtr {
            uptr: alloc::alloc::Global.allocate(Layout::new::<V>()).unwrap().as_ptr() as *mut V,
        };

        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;

        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn alloc(size: usize, align: usize) -> (pt: (PPtr<V>, Tracked<PointsToRaw>, Tracked<DeallocRaw>))
        requires
            valid_layout(size, align),
        ensures
            pt.1@@ === (PointsToRawData{ pptr: pt.0.id(), size: size as nat }),
            pt.2@@ === (DeallocRawData{ pptr: pt.0.id(), size: size as nat, align: align as nat }),
            pt.0.id() % align as int == 0,
    {
        opens_invariants_none();

        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
        let p = PPtr {
            uptr: alloc::alloc::Global.allocate(layout).unwrap().as_ptr() as *mut V,
        };

        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;

        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    /// Clones the pointer.
    /// TODO implement the `Clone` and `Copy` traits

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> (pt: PPtr<V>)
        ensures pt.id() === self.id(),
    {
        opens_invariants_none();

        PPtr { uptr: self.uptr }
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, perm: &mut Tracked<PointsTo<V>>, v: V)
        requires
            self.id() === old(perm)@@.pptr,
            old(perm)@@.value === option::Option::None,
        ensures
            perm@@.pptr === old(perm)@@.pptr,
            perm@@.value === option::Option::Some(v),
    {
        opens_invariants_none();

        unsafe {
            *(self.uptr) = v;
        }
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm@.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, perm: &mut Tracked<PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
        ensures
            perm@@.pptr === old(perm)@@.pptr,
            perm@@.value === option::Option::None,
            v === old(perm)@@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            core::ptr::read(self.uptr)
        }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, perm: &mut Tracked<PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@@.pptr,
            old(perm)@@.value.is_Some(),
        ensures
            perm@@.pptr === old(perm)@@.pptr,
            perm@@.value === option::Option::Some(in_v),
            out_v === old(perm)@@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = in_v;
            mem::swap(&mut m, &mut *self.uptr);
            m
        }
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.

    // Note that `self` is just a pointer, so it doesn't need to outlive 
    // the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&self, perm: &'a Tracked<PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@@.pptr,
            perm@@.value.is_Some(),
        ensures *v === perm@@.value.get_Some_0(),
    {
        opens_invariants_none();
        
        unsafe {
            &*self.uptr
        }
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dispose(&self, perm: Tracked<PointsTo<V>>, dealloc: Tracked<Dealloc<V>>)
        requires
            self.id() === perm@@.pptr,
            perm@@.value === option::Option::None,
            perm@@.pptr == dealloc@@.pptr,
    {
        opens_invariants_none();

        unsafe {
            let nn = core::ptr::NonNull::new_unchecked(self.uptr as *mut u8);
            alloc::alloc::Global.deallocate(nn, alloc::alloc::Layout::for_value(&*self.uptr));
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dealloc(&self,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
        dealloc: Tracked<DeallocRaw>
    )
        requires
            perm@@.pptr === self.id(),
            perm@@.size === size as nat,
            dealloc@@.pptr === self.id(),
            dealloc@@.size === size as nat,
            dealloc@@.align === align as nat,
    {
        opens_invariants_none();

        unsafe {
            // Since we have the Dealloc object, we know this is a valid layout
            let layout = Layout::from_size_align_unchecked(size, align);
            let nn = core::ptr::NonNull::new_unchecked(self.uptr as *mut u8);
            alloc::alloc::Global.deallocate(nn, alloc::alloc::Layout::for_value(&*self.uptr));
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
    pub fn into_inner(self, perm: Tracked<PointsTo<V>>, dealloc: Tracked<Dealloc<V>>) -> (v: V)
        requires
            self.id() === perm@@.pptr,
            perm@@.pptr == dealloc@@.pptr,
            perm@@.value.is_Some(),
        ensures
            v === perm@@.value.get_Some_0(),
    {
        opens_invariants_none();

        let mut perm = perm;
        let v = self.take(&mut perm);
        self.dispose(perm, dealloc);
        v
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.

    #[inline(always)]
    pub fn new(v: V) -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            (pt.1@@ === PointsToData{ pptr: pt.0.id(), value: option::Option::Some(v) }),
            (pt.2@@ === DeallocData{ pptr: pt.0.id() }),
    {
        let (p, mut t, d) = Self::empty();
        p.put(&mut t, v);
        (p, t, d)
    }
}

}
