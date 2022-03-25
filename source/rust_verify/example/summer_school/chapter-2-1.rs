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
    // recommend(1 <= factor);  // TODO(chris) this is a spec file! Sure wish I could enforce this
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

fn main()
{
    assert(!is_prime(0));
    assert(!is_prime(1));
    assert(is_prime(2));
    assert(is_prime(3));
    assert(divides(2, 6));
    assert(!is_prime(6));

    // TODO(chris): Dafny gets these positive assertions without proof; Verus won't try anything
    // past is_prime(3) (which only instantiates the forall once). I'm guessing the intuition is
    // that, if we have a literal sitting here, might as well do all the math by hand, because it's
    // not going to slow things down elsewhere in code that doesn't talk about literals?
    let candidate = 7;
    assert_forall_by(|factor: nat| {
        requires(1 < factor && factor < candidate);
        ensures (!divides(factor, candidate));
        assert(!divides(2, candidate));
        assert(!divides(3, candidate));
        assert(!divides(4, candidate));
        assert(!divides(5, candidate));
        assert(!divides(6, candidate)); // trigger
    });

    assert(is_prime(7));
    assert(divides(3, 9));
    assert(!is_prime(9));
}
