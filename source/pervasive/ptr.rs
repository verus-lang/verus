use std::mem::MaybeUninit;
use std::alloc::{Layout};
use std::alloc::{dealloc};

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

/// `PPtr<V>` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to `V` on the heap.
///
/// Technically, it is a wrapper around `*mut std::mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`Permission<V>`](Permission). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### Permission objects.
///
/// The [`Permission`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `Permission<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&Permission<V>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: Permission<V>` object tracks two pieces of data:
///  * `perm.pptr` is the pointer that the permission is associated to,
///     given by [`ptr.id()`](PPtr::id).
///  * `perm.value` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///
/// For those familiar with separation logic, the `Permission` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `T` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::Permission` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Example (TODO)

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

// TODO Identifier should be some opaque type, not necessarily an int
//type Identifier = int;

#[verifier(external_body)]
pub struct PPtr<#[verifier(strictly_positive)] V> {
    uptr: *mut MaybeUninit<V>,
}

// TODO split up the "deallocation" permission and the "access" permission?

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// See the [`PPtr`] documentation for more details.

#[proof]
#[verifier(unforgeable)]
pub struct Permission<V> {
    /// Indicates that this token is for a pointer `ptr: PPtr<V>`
    /// such that [`ptr.id()`](PPtr::id) equal to this value.

    #[spec] pub pptr: int,

    /// Indicates that this token gives the ability to read a value `V` from memory.
    /// When `None`, it indicates that the memory is uninitialized.

    #[spec] pub value: option::Option<V>,
}

impl<V> Permission<V> {
    /// Any dereferenceable pointer must be non-null.
    /// (Note that null pointers _do_ exist and are representable by `PPtr`;
    /// however, it is not possible to obtain a `Permission` token for
    /// any such a pointer.)

    #[proof]
    #[verifier(external_body)]
    pub fn is_nonnull(#[proof] &self) {
        ensures(self.pptr != 0);
        unimplemented!();
    }
}

impl<V> PPtr<V> {
    /// Cast a pointer to an integer.

    #[inline(always)]
    #[verifier(external_body)]
    #[exec]
    pub fn to_usize(&self) -> usize {
        ensures(|u: usize| u as int == self.id());
        self.uptr as usize
    }

    /// Cast an integer to a pointer.
    /// 
    /// Note that this does _not_ require or ensure that the pointer is valid.
    /// Of course, if the user creates an invalid pointer, they would still not be able to
    /// create a valid [`Permission`] token for it, and thus they would never
    /// be able to access the data behind the pointer.
    ///
    /// This is analogous to normal Rust, where casting to a pointer is always possible,
    /// but dereferencing a pointer is an `unsafe` operation.
    /// In Verus, casting to a pointer is likewise always possible,
    /// while dereferencing it is only allowed when the right preconditions are met.

    #[inline(always)]
    #[verifier(external_body)]
    #[exec]
    pub fn from_usize(u: usize) -> Self {
        ensures(|p: Self| p.id() == u as int);
        let uptr = u as *mut MaybeUninit<V>;
        PPtr { uptr }
    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (PPtr<V>, Proof<Permission<V>>) {
        ensures(|pt : (PPtr<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pptr: pt.0.id(), value: option::Option::None }))
        );
        opens_invariants_none();

        let p = PPtr {
            uptr: Box::leak(box MaybeUninit::uninit()).as_mut_ptr(),
        };
        let Proof(t) = exec_proof_from_false();
        (p, Proof(t))
    }

    // integer address of the pointer
    fndecl!(pub fn id(&self) -> int);

    /// Clones the pointer.
    /// TODO implement the `Clone` and `Copy` traits

    #[inline(always)]
    #[verifier(external_body)]
    pub fn clone(&self) -> PPtr<V> {
        ensures(|pt: PPtr<V>| equal(pt.id(), self.id()));
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
    pub fn put(&self, #[proof] perm: &mut Permission<V>, v: V) {
        requires([
            equal(self.id(), old(perm).pptr),
            equal(old(perm).value, option::Option::None),
        ]);
        ensures([
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::Some(v)),
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
    /// In the ghost perspective, this updates `perm.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[proof] perm: &mut Permission<V>) -> V {
        requires([
            equal(self.id(), old(perm).pptr),
            old(perm).value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::None),
            equal(v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            std::mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[proof] perm: &mut Permission<V>, in_v: V) -> V {
        requires([
            equal(self.id(), old(perm).pptr),
            old(perm).value.is_Some(),
        ]);
        ensures(|out_v: V| [
            equal(perm.pptr, old(perm).pptr),
            equal(perm.value, option::Option::Some(in_v)),
            equal(out_v, old(perm).value.get_Some_0()),
        ]);
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            std::mem::swap(&mut m, &mut *self.uptr);
            m.assume_init()
        }
    }

    /// Given a shared borrow of the `Permission<V>`, obtain a shared borrow of `V`.

    // Note that `self` is just a pointer, so it doesn't need to outlive 
    // the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&self, #[proof] perm: &'a Permission<V>) -> &'a V {
        requires([
            equal(self.id(), perm.pptr),
            perm.value.is_Some(),
        ]);
        ensures(|v: V|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();
        
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
    pub fn dispose(&self, #[proof] perm: Permission<V>) {
        requires([
            equal(self.id(), perm.pptr),
            equal(perm.value, option::Option::None),
        ]);
        opens_invariants_none();

        unsafe {
            dealloc(self.uptr as *mut u8, Layout::for_value(&*self.uptr));
        }
    }

    //////////////////////////////////
    // Verified library functions below here

    /// Free the memory pointed to be `perm` and return the 
    /// value that was previously there.
    /// Requires the memory to be initialized.
    /// This consumes the [`Permission`] token, since the user is giving up
    /// access to the memory by freeing it.

    #[inline(always)]
    pub fn into_inner(self, #[proof] perm: Permission<V>) -> V {
        requires([
            equal(self.id(), perm.pptr),
            perm.value.is_Some(),
        ]);
        ensures(|v|
            equal(v, perm.value.get_Some_0())
        );
        opens_invariants_none();

        #[proof] let mut perm = perm;
        let v = self.take(&mut perm);
        self.dispose(perm);
        v
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.

    #[inline(always)]
    pub fn new(v: V) -> (PPtr<V>, Proof<Permission<V>>) {
        ensures(|pt : (PPtr<V>, Proof<Permission<V>>)|
            equal(pt.1, Proof(Permission{ pptr: pt.0.id(), value: option::Option::Some(v) }))
        );

        let (p, Proof(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Proof(t))
    }
}
