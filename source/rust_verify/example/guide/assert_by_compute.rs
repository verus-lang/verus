#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use pervasive::seq::*;

verus! {

// ANCHOR: pow_concrete
    // Naive definition of exponentiation
    spec fn pow(base: nat, exp: nat) -> nat
        decreases exp
    {
        if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
    }

    proof fn concrete_pow() {
        assert(pow(2, 8) == 256) by (compute); // Assertion 1
        assert(pow(2, 9) == 512); // Assertion 2
        assert(pow(2, 8) == 256) by (compute_only); // Assertion 3
    }
// ANCHOR_END: pow_concrete

/*
// ANCHOR: let_fails
    let x = 2;
    assert(pow(2, x) == 4) by (compute_only);
// ANCHOR_END: let_fails
*/

// ANCHOR: let_passes
    proof fn let_passes() {
        assert({
          let x = 2;
          pow(2, x) == 4
        }) by (compute_only);
    }
// ANCHOR_END: let_passes

// ANCHOR: seq_example
    proof fn seq_example {
        assert(seq![a, b, c, d].ext_equal(seq![a, b].add(seq![c, d]))) by (compute_only);
    }
// ANCHOR_END: seq_example
