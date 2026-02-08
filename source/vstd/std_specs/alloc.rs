use verus_builtin_macros::verus;

verus! {

// this is a bit of a hack; verus treats Global specially already,
// but putting this here helps Verus pick up all the trait impls for Global
#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGlobal(alloc::alloc::Global);

#[cfg(feature = "alloc")]
#[feature(liballoc_internals)]
pub assume_specification<T>[ alloc::boxed::box_new ](x: T) -> (result: alloc::boxed::Box<T>)
    ensures
        *result == x,
;

} // verus!
