#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

#[verifier(external)]
fn main() {
}

#[proof]
fn assert(b: bool) {
    requires(b);
    ensures(b);
}

#[proof]
fn assume(b: bool) {
    ensures(b);
    admit();
}

verus! {

spec fn sf(x: int, y: int) -> bool {
    let b = x < y;
    &&& b
    &&& if false {
            &&& b ==> b
            &&& !b ==> !b
        } else {
            ||| b ==> b
            ||| !b
        }
    &&& false ==> true
}

spec fn sa<A>(_a1: A, _a2: A) -> bool {
    true
}

proof fn consume(tracked x: int) {
}

pub(crate) proof fn pf<A>(a: A, x: int, tracked t: int) {
    consume(tracked t);

    assert(false ==> true);
    assert(true && false ==> false && false);
    assert(!(true && (false ==> false) && false));

    assert(false ==> false ==> false);
    assert(false ==> (false ==> false));
    assert(!((false ==> false) ==> false));

    assert(false <== false <== false);
    assert(!(false <== (false <== false)));
    assert((false <== false) <== false);
    assert(2 + 2 !== 3);
    assert(a === a);

    assert(false <==> true && false);

    assert(sf(100, 200));
    assert(!sf(200, 100));
    assert(!sf(x, x));
    assert(sa(a, a));
}

} // verus!
