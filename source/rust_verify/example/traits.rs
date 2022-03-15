#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::*;

trait T<A> {
    #[spec]
    fn req(&self, a: A) -> bool { no_method_body() }

    #[spec]
    fn ens(&self, a: A, r: A) -> bool { no_method_body() }

    fn f(&self, a: &A) -> A {
        requires(self.req(*a));
        ensures(|ra: A| self.ens(*a, ra));
        no_method_body()
    }
}

struct B {
    x: bool,
}

struct I {
    x: u64,
}

impl T<bool> for B {
    #[spec]
    fn req(&self, a: bool) -> bool {
        a
    }

    #[spec]
    fn ens(&self, a: bool, r: bool) -> bool {
        r == (a && self.x)
    }

    fn f(&self, a: &bool) -> bool {
        *a && self.x
    }
}

impl T<u64> for I {
    #[spec]
    fn req(&self, a: u64) -> bool {
        self.x < a && a < 100
    }

    #[spec]
    fn ens(&self, a: u64, r: u64) -> bool {
        self.x <= r && r < 100
    }

    fn f(&self, a: &u64) -> u64 {
        self.x / 2 + a / 2
    }
}

fn p<A, Z: T<A>>(a: &A, z: &Z) -> A {
    requires(z.req(*a));
    ensures(|rz: A| z.ens(*a, rz));
    z.f(a)
}

fn test() -> bool {
    let i = I { x: 30 };
    print_u64(p(&70, &i));

    let b = B { x: false };
    b.f(&true) && p(&true, &b)
}

#[verifier(external)]
fn main() {
    println!("{}", test());
}
