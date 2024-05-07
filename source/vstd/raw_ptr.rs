#![allow(unused_imports)]

use crate::prelude::*;
use builtin::*;
use builtin_macros::*;

verus! {

//////////////////////////////////////
// Define a model of Ptrs and PointsTo
// Notes on mutability:
//
//  - Unique vs shared ownership in Verus is always determined
//    via the PointsTo ghost tracked object.
//
//  - Thus, there is effectively no difference between *mut T and *const T,
//    so we encode both of these in the same way.
//    (In VIR, we distinguish these via a decoration.)
//    Thus we can cast freely between them both in spec and exec code.
//
//  - This is consistent with Rust's operational semantics;
//    casting between *mut T and *const T has no operational meaning.
//
//  - When creating a pointer from a reference, the mutability
//    of the pointer *does* have an effect because it determines
//    what kind of "tag" the pointer gets, i.e., whether that
//    tag is readonly or not. In our model here, this tag is folded
//    into the provenance.
//
// Provenance:
//
//  - A full model of provenance is given by formalisms such as "Stacked Borrows"
//    or "Tree Borrows".
//
//  - None of these models are finalized, nor has Rust committed to then.
//    Rust's recent RFC on provenance simply details that there *is* some concept
//    of provenance.
//    https://rust-lang.github.io/rfcs/3559-rust-has-provenance.html
//
//  - Our model here, likewise, simply declares Provenance as an
//    abstract type.
#[verifier::external_body]
pub ghost struct Provenance {}

impl Provenance {
    /// The provenance of the null ptr
    pub spec fn null() -> Self;
}

// Metadata
//
// For thin pointers (i.e., when T: Sized), the metadata is ()
// For slices, str, and dyn types this is nontrivial
// See: https://doc.rust-lang.org/std/ptr/trait.Pointee.html
//
// TODO flesh out the metadata system for working with DSTs
// It may make sense to use <T as Pointee>::Metadata directly.
#[verifier::external_body]
pub ghost struct Metadata {}

impl Metadata {
    // Unit metadata used for thin pointers
    pub spec fn unit() -> Metadata;
}

pub ghost struct PtrData {
    pub addr: usize,
    pub provenance: Provenance,
    pub metadata: Metadata,
}

#[verifier(external_body)]
#[verifier::accept_recursive_types(T)]
pub tracked struct PointsTo<T> {
    phantom: core::marker::PhantomData<T>,
    no_copy: NoCopy,
}

// Don't use std Option here in order to avoid circular dependency issues
// with verifying the standard library.
// (Also, using our own enum here lets us have more meaningful
// variant names like Uninit/Init.)
#[verifier::accept_recursive_types(T)]
pub ghost enum MemContents<T> {
    Uninit,
    Init(T),
}

pub ghost struct PointsToData<T> {
    pub ptr: *mut T,
    pub opt_value: MemContents<T>,
}

impl<T> View for *mut T {
    type V = PtrData;

    spec fn view(&self) -> Self::V;
}

impl<T> View for *const T {
    type V = PtrData;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        (*self as *mut T).view()
    }
}

impl<T> View for PointsTo<T> {
    type V = PointsToData<T>;

    spec fn view(&self) -> Self::V;
}

impl<T> PointsTo<T> {
    #[verifier::inline]
    pub open spec fn ptr(&self) -> *mut T {
        self.view().ptr
    }

    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<T> {
        self.view().opt_value
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.opt_value().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.opt_value().is_uninit()
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> T {
        self.opt_value().value()
    }
}

impl<T> MemContents<T> {
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self is Init
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self is Uninit
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> T {
        self->0
    }
}

//////////////////////////////////////
// Inverse functions:
// Pointers are equivalent to their model
pub spec fn ptr_mut_from_data<T: ?Sized>(data: PtrData) -> *mut T;

#[verifier::inline]
pub open spec fn ptr_from_data<T: ?Sized>(data: PtrData) -> *const T {
    ptr_mut_from_data(data) as *const T
}

#[verifier::external_body]
pub broadcast proof fn axiom_ptr_mut_from_data<T>(data: PtrData)
    ensures
        (#[trigger] ptr_mut_from_data::<T>(data))@ == data,
{
}

// Equiv to ptr_mut_from_data, but named differently to avoid trigger issues
// Only use for ptrs_mut_eq
#[doc(hidden)]
pub spec fn view_reverse_for_eq<T: ?Sized>(data: PtrData) -> *mut T;

/// Implies that `a@ == b@ ==> a == b`.
#[verifier::external_body]
pub broadcast proof fn ptrs_mut_eq<T>(a: *mut T)
    ensures
        view_reverse_for_eq::<T>(#[trigger] a@) == a,
{
}

//////////////////////////////////////
// Null ptrs
#[verifier::inline]
pub open spec fn ptr_null<T: ?Sized + core::ptr::Thin>() -> *const T {
    ptr_from_data(PtrData { addr: 0, provenance: Provenance::null(), metadata: Metadata::unit() })
}

#[cfg(verus_keep_ghost)]
#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ptr_null)]
pub fn ex_ptr_null<T: ?Sized + core::ptr::Thin>() -> (res: *const T)
    ensures
        res == ptr_null::<T>(),
{
    core::ptr::null()
}

#[verifier::inline]
pub open spec fn ptr_null_mut<T: ?Sized + core::ptr::Thin>() -> *mut T {
    ptr_mut_from_data(
        PtrData { addr: 0, provenance: Provenance::null(), metadata: Metadata::unit() },
    )
}

#[cfg(verus_keep_ghost)]
#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ptr_null_mut)]
pub fn ex_ptr_null_mut<T: ?Sized + core::ptr::Thin>() -> (res: *mut T)
    ensures
        res == ptr_null_mut::<T>(),
{
    core::ptr::null_mut()
}

/// core::ptr::write
/// (This does _not_ drop the contents)
#[inline(always)]
#[verifier(external_body)]
pub fn ptr_mut_write<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>, v: T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_uninit(),
    ensures
        perm.ptr() == ptr,
        perm.opt_value() == MemContents::Init(v),
    opens_invariants none
{
    unsafe {
        core::ptr::write(ptr, v);
    }
}

/// core::ptr::read
/// (TODO this should work differently if T is Copy)
#[inline(always)]
#[verifier(external_body)]
pub fn ptr_mut_read<T>(ptr: *const T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init(),
    ensures
        perm.ptr() == ptr,
        perm.is_uninit(),
        v == old(perm).value(),
    opens_invariants none
{
    unsafe { core::ptr::read(ptr) }
}

/// equivalent to &*X
#[inline(always)]
#[verifier(external_body)]
pub fn ptr_ref<T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: &T)
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v == perm.value(),
{
    unsafe { &*ptr }
}

/* coming soon
/// equivalent to &mut *X
#[inline(always)]
#[verifier(external_body)]
pub fn ptr_mut_ref<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: &mut T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_init()
    ensures
        perm.ptr() == ptr,
        perm.is_init(),

        old(perm).value() == *old(v),
        new(perm).value() == *new(v),
    unsafe { &*ptr }
}
*/

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_raw_ptr_axioms {
    axiom_ptr_mut_from_data,
    ptrs_mut_eq,
}

} // verus!
