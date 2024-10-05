#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, pervasive::*, prelude::*, seq::*};

verus! {
trait SpecT2<A> {
    spec fn req2(&self, a: A) -> bool;

    spec fn ens2(&self, a: A, r: A) -> bool;
}

impl SpecT2<bool> for B {
    spec fn req2(&self, a: bool) -> bool {
        a
    }

    spec fn ens2(&self, a: bool, r: bool) -> bool {
        r == (a && self.x)
    }
}
}

#[verus_verify]
trait T2<A>: SpecT2<A> {
    #[requires(self.req2(*a))]
    #[ensures(|ra: A| self.ens2(*a, r))]
    fn f2(&self, a: &A) -> A;
}

#[verus_verify]
impl T2<bool> for B {
    fn f2(&self, a: &bool) -> bool {
        *a && self.x
    }
}

verus! {

trait SpecT<A> {
    spec fn req(&self, a: A) -> bool;

    spec fn ens(&self, a: A, r: A) -> bool;
}

struct B {
    x: bool,
}

struct I {
    x: u64,
}

impl SpecT<bool> for B {
    spec fn req(&self, a: bool) -> bool {
        a
    }

    spec fn ens(&self, a: bool, r: bool) -> bool {
        r == (a && self.x)
    }
}
impl T<bool> for B {
    fn f(&self, a: &bool) -> bool {
        *a && self.x
    }
}


#[verifier::external_body]
fn main() {
}

} // verus!
