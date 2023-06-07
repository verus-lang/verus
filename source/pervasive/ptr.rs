use core::{marker, mem, mem::MaybeUninit};
extern crate alloc;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::modes::*;

verus!{

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

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct PPtr<V> {
    uptr: *mut MaybeUninit<V>,
}

// PPtr is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.

#[verifier(external)]
unsafe impl<T> Sync for PPtr<T> {}

#[verifier(external)]
unsafe impl<T> Send for PPtr<T> {}

// TODO split up the "deallocation" permission and the "access" permission?

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.

#[verifier(external_body)]
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

    pub value: option::Option<V>,
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
        let uptr = u as *mut MaybeUninit<V>;
        PPtr { uptr }
    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (pt: (PPtr<V>, Tracked<PointsTo<V>>))
        ensures pt.1@@ === (PointsToData{ pptr: pt.0.id(), value: option::Option::None }),
        opens_invariants none
    {
        let p = PPtr {
            uptr: alloc::boxed::Box::leak(alloc::boxed::Box::new(MaybeUninit::uninit())).as_mut_ptr(),
        };

        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;

        (p, Tracked::assume_new())
    }

    /// Clones the pointer.
    /// TODO implement the `Clone` and `Copy` traits

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> (pt: PPtr<V>)
        ensures pt.id() === self.id(),
        opens_invariants none
    {
        PPtr { uptr: self.uptr }
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value === option::Option::None,
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === option::Option::Some(v),
        opens_invariants none
    {
        unsafe {
            *(self.uptr) = MaybeUninit::new(v);
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
    #[verifier(external_body)]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === option::Option::None,
            v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe {
            let mut m = MaybeUninit::uninit();
            mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === option::Option::Some(in_v),
            out_v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe {
            let mut m = MaybeUninit::new(in_v);
            mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.

    // Note that `self` is just a pointer, so it doesn't need to outlive 
    // the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures *v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe {
            (*self.uptr).assume_init_ref()
        }
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dispose(&self, Tracked(perm): Tracked<PointsTo<V>>)
        requires
            self.id() === perm@.pptr,
            perm@.value === option::Option::None,
        opens_invariants none
    {
        unsafe {
            alloc::alloc::dealloc(self.uptr as *mut u8, alloc::alloc::Layout::for_value(&*self.uptr));
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
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures
            v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        let v = self.take(Tracked(&mut perm));
        self.dispose(Tracked(perm));
        v
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.

    #[inline(always)]
    pub fn new(v: V) -> (pt: (PPtr<V>, Tracked<PointsTo<V>>))
        ensures
            (pt.1@@ === PointsToData{ pptr: pt.0.id(), value: option::Option::Some(v) }),
    {
        let (p, Tracked(mut t)) = Self::empty();
        p.put(Tracked(&mut t), v);
        (p, Tracked(t))
    }
}

}
