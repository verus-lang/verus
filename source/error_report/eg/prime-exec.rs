use vstd::prelude::*;

// use super::foo::*;
mod foo;
use crate::foo::*;
// since the contents are inside the module, 
// you need to import them with use to use them, or fully qualify their path names, like foo::divides

verus! {


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

#[verifier(external)]
fn main() {

}
}