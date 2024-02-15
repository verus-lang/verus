# Arithmetic Library

# Overview

This library was originally ported from the [Dafny standard library for
arithmetic](https://github.com/dafny-lang/dafny/tree/master/Source/DafnyStandardLibraries/src/Std/Arithmetic/).

The general philosophy of this library is as follows. Nonlinear arithmetic is
generally undecidable, so Z3 relies on heuristics to prove facts about it.
While wonderful when they work, these heuristics can lead to unstable proofs.
So, Verus turns nonlinear arithmetic reasoning off by default when it invokes
the SMT solver. One can override this by annotating functions with
`#[verifier::nonlinear]`, but users shouldn't have to take on this danger. So,
users can instead invoke the lemmas in this library to verify facts that would
normally require nonlinear arithmetic.

Furthermore, to keep the proofs in the library itself stable, the library only
sparingly uses SMT nonlinear-arithmetic reasoning. It uses nonlinear
arithmetic only in the `internals/*_nonlinear.rs` files, and those files only
contain simple, basic proofs that are unlikely to lead the SMT solver on a
wild search.

# Files

The files with proofs that Verus users may want to use are:

* `div_mod.rs`: Proofs about integer division (`/`) and remainder aka mod (`%`)
* `logarithm.rs`: Proofs about integer logarithm (and its definition as `log`)
* `mul.rs`: Proofs about integer multiplication (`*`)
* `power.rs`: Proofs about integer exponentiation (and its definition as `pow`)
* `power2.rs`: Proofs about powers of 2 (and its definition as `pow2`)

There are also internal files in `internals/*.rs`, but they aren't meant to be
invoked directly by Verus users.

# Usage

Here's an example use of the arithmetic standard library:

```
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_bound};
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_commutative, lemma_mul_is_distributive_sub_other_way};

verus! {
    pub proof fn lemma_div_relation_when_mods_have_same_order(d: int, x: int, y: int)
        requires
            d > 0,
            x < y,
            y - x <= d,
            x % d < y % d,
        ensures
            y / d == x / d,
    {
        lemma_fundamental_div_mod(x, d);
        lemma_fundamental_div_mod(y, d);
        lemma_mod_bound(x, d);
        lemma_mod_bound(y, d);

        lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
        lemma_mul_is_commutative(y / d, d);
        lemma_mul_is_commutative(x / d, d);

        if (y / d) > (x / d) {
            lemma_mul_inequality(1, (y / d) - (x / d), d);
            assert(((y / d) - (x / d)) * d >= 1 * d);
            assert((y / d) * d - (x / d) * d >= d);
            assert(false);
        }
        if (y / d) < (x / d) {
            lemma_mul_inequality((y / d) - (x / d), -1, d);
            assert(((y / d) - (x / d)) * d <= (-1) * d);
            lemma_mul_is_distributive_sub_other_way(d, y / d, x / d);
            assert(false);
        }
    }
}
