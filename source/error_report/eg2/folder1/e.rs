use vstd::prelude::*;

verus! {

// airthmetic operations are not in trigger selection
// z3 does not allow it
pub open spec fn divides (m:int, n:int) -> bool {
    n % m == 0
}

pub open spec fn e() -> bool {
    true
}

spec fn prime (n:int) -> bool {
    n >= 2 && forall|i: int| 2 <= i < n ==> !divides(i, n)
}

exec fn is_prime(n:u64) -> (res:bool)
    requires n >= 2
    ensures res <==> prime(n as int)
{
    let mut i = 2 as u64;

    while i < n
        invariant
            2 <= i <= n,
            forall|j: u64| 2 <= j < i ==> !divides(j as int, n as int)
    {
        if (n % i == 0) {
            assert(divides(i as int, n as int)); //OBSERVE
            return false;
        }
        i = i + 1;
    }
    true
}

// any documentation with the verus attributes?
// just grep the exampels dir
#[verifier(external_body)]
fn main() {
    // print_u64()
    println!("{}", is_prime(2));
}

}
