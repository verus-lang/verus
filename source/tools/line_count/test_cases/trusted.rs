use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn new_style() {}

#[verifier(external_body)]
fn old_style() {}

#[verifier::external_fn_specification]
pub fn ex_swap<T>(a: &mut T, b: &mut T) {
    core::mem::swap(a, b)
}

pub assume_specification<T>[ core::mem::replace::<T> ](dest: &mut T, src: T) -> T;

#[verifier(external)]
fn ignored() {}

proof fn assumptions(x: u64) {
    assume(x < 100);
    admit();
}

} // verus!
