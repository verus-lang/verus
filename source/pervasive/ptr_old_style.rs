use core::{marker, mem, mem::MaybeUninit};
extern crate alloc;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

verus!{

/// `PPtr<V>` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to `V` on the heap.
///
/// Technically, it is a wrapper around `*mut mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PermData<V>`](PermData). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PermData objects.
///
/// The [`PermData`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `PermData<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&PermData<V>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: PermData<V>` object tracks two pieces of data:
///  * `perm.pptr` is the pointer that the permission is associated to,
///     given by [`ptr.id()`](PPtr::id).
///  * `perm.value` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///
/// For those familiar with separation logic, the `PermData` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `T` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PermData` token represents not just the permission to read/write
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
//    "Provenance" comes from the `tracked ghost` PermData object.
//   *******************************
// 
// Pretty simple, right?
//
// Of course, this trusted pointer library still needs to actually run and
// be sound in the Rust backend.
// Rust's abstract pointer model is unchanged, and it doesn't know anything
// about Verus's special ghost `PermData` object, which gets erased, anyway.
//
// Maybe someday the ghost PermData model will become a real
// memory model. That isn't true today.
// So we still need to know something about actual, real memory models that
// are used right now in order to implement this API soundly.
//
// Our goal is to allow the *user of Verus* to think in terms of the
// VERUS POINTER MODEL where provenance is tracked via the `PermData` object.
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
pub struct PPtr<#[verifier(strictly_positive)] V> {
    uptr: *mut MaybeUninit<V>,
}

// PPtr is always safe to Send/Sync. It's the PermData object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.

#[verifier(external)]
unsafe impl<T> Sync for PPtr<T> {}

#[verifier(external)]
unsafe impl<T> Send for PPtr<T> {}

// TODO split up the "deallocation" permission and the "access" permission?

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PermData` object is given by the data in its
/// `View` object, [`PermDataData`].
///
/// See the [`PPtr`] documentation for more details.

#[verifier(external_body)]
pub tracked struct PermData<#[verifier(strictly_positive)] V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

/// Represents the meaning of a [`PermData`] object.

pub ghost struct PermDataData<V> {
    /// Indicates that this token is for a pointer `ptr: PPtr<V>`
    /// such that [`ptr.id()`](PPtr::id) equal to this value.

    pub pptr: int,

    /// Indicates that this token gives the ability to read a value `V` from memory.
    /// When `None`, it indicates that the memory is uninitialized.

    pub value: option::Option<V>,
}

#[doc(hidden)]
#[macro_export]
macro_rules! ptr_perm_internal {
    [$pcell:expr => $val:expr] => {
        $crate::pervasive::ptr_old_style::PermDataData {
            pptr: $pcell,
            value: $val,
        }
    };
}

#[macro_export]
macro_rules! ptr_perm {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::pervasive::ptr_old_style::ptr_perm_internal!($($tail)*)
        )
    }
}

pub use ptr_perm_internal;
pub use ptr_perm;

impl<V> PermData<V> {
    pub spec fn view(self) -> PermDataData<V>;

    /// Any dereferenceable pointer must be non-null.
    /// (Note that null pointers _do_ exist and are representable by `PPtr`;
    /// however, it is not possible to obtain a `PermData` token for
    /// any such a pointer.)

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures self.view().pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn leak_contents(tracked &mut self)
        ensures self.view().pptr == old(self).view().pptr && self.view().value.is_None(),
    {
        unimplemented!();
    }
}

}

impl<V> PPtr<V> {
    verus!{

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
    /// create a valid [`PermData`] token for it, and thus they would never
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

    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (PPtr<V>, Trk<PermData<V>>)
    {
        ensures(|pt: (PPtr<V>, Trk<PermData<V>>)|
            equal(pt.1.0.view(), PermDataData{ pptr: pt.0.id(), value: option::Option::None }));
        opens_invariants_none();

        let p = PPtr {
            uptr: alloc::boxed::Box::leak(alloc::boxed::Box::new(MaybeUninit::uninit())).as_mut_ptr(),
        };

        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;

        (p, Trk(proof_from_false()))
    }

    verus!{

    /// Clones the pointer.
    /// TODO implement the `Clone` and `Copy` traits

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> (pt: PPtr<V>)
        ensures pt === *self,
    {
        opens_invariants_none();

        PPtr { uptr: self.uptr }
    }

    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, #[proof] perm: &mut PermData<V>, v: V)
    {
        requires([
            self.id() == old(perm).view().pptr,
            equal(old(perm).view().value, option::Option::None),
        ]);
        ensures([
            equal(perm.view().pptr, old(perm).view().pptr),
            equal(perm.view().value, option::Option::Some(v)),
        ]);
        opens_invariants_none();

        unsafe {
            *(self.uptr) = MaybeUninit::new(v);
        }
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm.view().value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[proof] perm: &mut PermData<V>) -> V
    {
        requires([
            self.id() == old(perm).view().pptr,
            old(perm).view().value.is_Some(),
        ]);
        ensures(|v: V| [
            perm.view().pptr == old(perm).view().pptr,
            equal(perm.view().value, option::Option::None),
            equal(v, old(perm).view().value.get_Some_0()),
        ]);

        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    verus!{

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[proof] perm: &mut PermData<V>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm).view().pptr,
            old(perm).view().value.is_Some(),
        ensures
            perm.view().pptr === old(perm).view().pptr,
            perm.view().value === option::Option::Some(in_v),
            out_v === old(perm).view().value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    }

    /// Given a shared borrow of the `PermData<V>`, obtain a shared borrow of `V`.

    // Note that `self` is just a pointer, so it doesn't need to outlive 
    // the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&self, #[proof] perm: &'a PermData<V>) -> &'a V
    {
        requires([
            equal(self.id(), perm.view().pptr),
            perm.view().value.is_Some(),
        ]);
        ensures(|v: &V| equal(*v, perm.view().value.get_Some_0()));

        opens_invariants_none();
        
        unsafe {
            (*self.uptr).assume_init_ref()
        }
    }

    verus!{

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dispose(&self, #[proof] perm: PermData<V>)
        requires
            self.id() === perm.view().pptr,
            perm.view().value === option::Option::None,
    {
        opens_invariants_none();

        unsafe {
            alloc::alloc::dealloc(self.uptr as *mut u8, alloc::alloc::Layout::for_value(&*self.uptr));
        }
    }

    }

    //////////////////////////////////
    // Verified library functions below here

    /// Free the memory pointed to be `perm` and return the 
    /// value that was previously there.
    /// Requires the memory to be initialized.
    /// This consumes the [`PermData`] token, since the user is giving up
    /// access to the memory by freeing it.

    #[inline(always)]
    pub fn into_inner(self, #[proof] perm: PermData<V>) -> V
    {
        requires([
            equal(self.id(), perm.view().pptr),
            perm.view().value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(v, perm.view().value.get_Some_0()),
        ]);
        opens_invariants_none();

        #[proof] let mut perm = perm;
        let v = self.take(&mut perm);
        self.dispose(perm);
        v
    }

    verus!{

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.

    #[inline(always)]
    pub fn new(v: V) -> (pt: (PPtr<V>, Trk<PermData<V>>))
        ensures
            (pt.1.0.view() === PermDataData{ pptr: pt.0.id(), value: option::Option::Some(v) }),
    {
        let (p, Trk(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Trk(t))
    }

    }
}

impl<V: Copy> PPtr<V> {
    #[inline(always)]
    pub fn read(&self, #[proof] perm: &PermData<V>) -> V {
        requires([
            equal(self.id(), perm.view().pptr),
            perm.view().value.is_Some(),
        ]);
        ensures(|v: V| equal(option::Option::Some(v), perm.view().value));

        *self.borrow(perm)
    }

    #[inline(always)]
    #[exec] pub fn write(&self, #[proof] perm: &mut PermData<V>, v: V) {
        requires(equal(self.id(), old(perm).view().pptr));
        ensures([
            equal(perm.view().pptr, self.id()),
            equal(perm.view().value, option::Option::Some(v)),
        ]);

        perm.leak_contents();
        self.put(perm, v);
    }

    #[inline(always)]
    pub fn free(&self, #[proof] perm: PermData<V>) {
        requires(equal(self.id(), perm.view().pptr));

        #[proof] let mut perm = perm;
        perm.leak_contents();
        self.dispose(perm);
    }


}
