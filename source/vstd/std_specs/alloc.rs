use super::super::prelude::*;
use super::super::raw_ptr::MemContents;

verus! {

// this is a bit of a hack; verus treats Global specially already,
// but putting this here helps Verus pick up all the trait impls for Global
#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGlobal(alloc::alloc::Global);

// Rc/Arc's Clone impls are bounded by this std marker trait, so their
// assume_specifications must name it.
#[cfg(feature = "alloc")]
#[verifier::external_trait_specification]
pub unsafe trait ExAllocatorClone: core::alloc::Allocator + Clone {
    type ExternalTraitSpecificationFor: core::alloc::AllocatorClone;
}

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T, const N: usize>[ alloc::boxed::box_assume_init_into_vec_unsafe ](
    vals: alloc::boxed::Box<core::mem::MaybeUninit<[T; N]>>,
) -> (result: alloc::vec::Vec<T>)
    requires
        vals.mem_contents() is Init,
    ensures
        vals.mem_contents() matches MemContents::Init(array) && result@ == array@,
;

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T>[ alloc::intrinsics::write_box_via_move ](
    _0: alloc::boxed::Box<core::mem::MaybeUninit<T>>,
    v: T,
) -> (result: alloc::boxed::Box<core::mem::MaybeUninit<T>>)
    ensures
        result.mem_contents() == MemContents::Init(v),
;

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T>[ alloc::boxed::Box::<T>::new_uninit ]() -> alloc::boxed::Box<
    core::mem::MaybeUninit<T>,
>
;

} // verus!
