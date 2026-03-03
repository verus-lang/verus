use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::*;

verus! {

use vstd::std_specs::ops::AddSpec;
use vstd::float::FloatBitsProperties;

/*
Verus deliberately omits axioms about floating point from vstd,
because the desired set of useful and sound axioms may vary by project and platform.
(See https://github.com/rust-lang/rfcs/blob/master/text/3514-float-semantics.md for details
about why Rust floating point semantics are complex, may be non-deterministic, and may fall short
of desired behavior on some platforms.)
Therefore, projects that want to prove properties of about floating-point numbers may want
to define their own axioms, or even define different groups of axioms for different situations.

For example, one useful axiom is that it is always safe to add any two floats
(this assumes that the platform is correctly configured not to trap on a NaN result,
which should usually be true):
*/

pub broadcast axiom fn f64_can_add_anything(a: f64, b: f64)
    ensures
        #[trigger] a.add_req(b);

/*
The axiom above doesn't guarantee non-NaN results -- it's possible to add large positive numbers to
construct positive infinity, to add large negative numbers to construct negative infinity,
and then add negative infinity to positive infinity to construct a NaN.
As an example of verifying something slightly nontrivial,
the axioms below only permit addition of positive numbers,
and guarantee non-NaN results.
*/

pub broadcast axiom fn f64_add_positive_spec(a: f64, b: f64)
    requires
        !a.is_nan_spec(),
        !b.is_nan_spec(),
        !a.is_sign_negative_spec(),
        !b.is_sign_negative_spec(),
    ensures
        #![trigger a.add_spec(b)]
        !a.add_spec(b).is_nan_spec(),
        !a.add_spec(b).is_sign_negative_spec();

pub broadcast axiom fn f64_add_positive_exec(a: f64, b: f64)
    requires
        !a.is_nan_spec(),
        !b.is_nan_spec(),
        !a.is_sign_negative_spec(),
        !b.is_sign_negative_spec(),
    ensures
        #[trigger] a.add_req(b);

use vstd::std_specs::ops::add_ensures;

pub broadcast axiom fn f64_add_positive_ensures(a: f64, b: f64, o: f64)
    requires
        !a.is_nan_spec(),
        !b.is_nan_spec(),
        !a.is_sign_negative_spec(),
        !b.is_sign_negative_spec(),
    ensures
        #[trigger] add_ensures::<f64>(a, b, o) ==> o == a.add_spec(b);

pub broadcast group f64_add_positive {
    f64_add_positive_spec,
    f64_add_positive_exec,
    f64_add_positive_ensures,
}

fn main() {
    broadcast use f64_add_positive;
    let a: f64 = 3.1;
    let b: f64 = 2.8;
    let c = a + b;
    let d = b + c;
    let e = c + d;

    // This would fail the !b.is_sign_negative_spec() precondition:
    // let f = e + (-0.7);

    // But if we use the more permissive axiom, then we can add a negative number
    // (albeit with no guarantee about the result):
    broadcast use f64_can_add_anything;
    let f = e + (-0.7);
}

} // verus!
