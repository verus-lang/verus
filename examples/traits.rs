#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, pervasive::*, prelude::*, seq::*};

verus! {

trait T<A> {
    spec fn req(&self, a: A) -> bool;

    spec fn ens(&self, a: A, r: A) -> bool;

    fn f(&self, a: &A) -> (ra: A)
        requires
            self.req(*a),
        ensures
            self.ens(*a, ra),
    ;
}

struct B {
    x: bool,
}

struct I {
    x: u64,
}

impl T<bool> for B {
    spec fn req(&self, a: bool) -> bool {
        a
    }

    spec fn ens(&self, a: bool, r: bool) -> bool {
        r == (a && self.x)
    }

    fn f(&self, a: &bool) -> bool {
        *a && self.x
    }
}

impl T<u64> for I {
    spec fn req(&self, a: u64) -> bool {
        self.x < a && a < 100
    }

    spec fn ens(&self, a: u64, r: u64) -> bool {
        self.x <= r && r < 100
    }

    fn f(&self, a: &u64) -> u64 {
        self.x / 2 + a / 2
    }
}

fn p<A, Z: T<A>>(a: &A, z: &Z) -> (rz: A)
    requires
        z.req(*a),
    ensures
        z.ens(*a, rz),
{
    z.f(a)
}

fn test() -> bool {
    let i = I { x: 30 };
    print_u64(p(&70, &i));
    let b = B { x: false };
    b.f(&true) && p(&true, &b)
}

#[verifier::external_body]
fn main() {
    println!("{}", test());
}

} // verus!
