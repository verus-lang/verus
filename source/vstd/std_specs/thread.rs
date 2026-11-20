#![allow(unused_imports)]
/// Specifications for [`std::thread::scope`] and the scoped-thread types.
use super::super::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExScope<'scope, 'env>(std::thread::Scope<'scope, 'env>);

pub assume_specification<'env, F, T>[ std::thread::scope::<'env, F, T> ](f: F) -> (r: T) where
    F: for <'scope>FnOnce(&'scope std::thread::Scope<'scope, 'env>) -> T,

    requires
        forall|s: &std::thread::Scope<'_, 'env>| #[trigger] f.requires((s,)),
    ensures
        exists|s: &std::thread::Scope<'_, 'env>| #[trigger] f.ensures((s,), r),
;

} // verus!
