#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;

#[allow(unused_imports)]
use seq::*;
#[allow(unused_imports)]
use vec::*;

#[spec]
fn divides(factor: nat, candidate: nat) -> bool
{
    // recommend(1 <= factor);  // TODO(chris) (long term) this is a spec file! Sure wish I could enforce this
    // for confidence's sake.
    candidate % factor == 0
}

#[spec]
fn is_prime(candidate: nat) -> bool
{
       true
    && 1 < candidate
    && forall(|factor: nat| 1 < factor && factor < candidate >>= !divides(factor, candidate))
}

fn test_prime(candidate: u64) -> bool
{
    requires(1 < candidate);
    ensures(|result: bool| result == is_prime(candidate));
    
    let mut factor:u64 = 2;
    while (factor < candidate)
    {
        invariant([
            1 <= factor,
            forall(|smallerfactor:nat| 1 < smallerfactor && smallerfactor < factor >>= !divides(smallerfactor, candidate))
        ]);
        if candidate % factor == 0 {
            assert(divides(factor, candidate));
            assume(!is_prime(candidate));   // TODO(chris): can't prove the !forall. (Dafny doesn't need this line, either.)
            return false;
        }
        factor = factor + 1;
    }
    true
}

fn main()
{
}
