#[allow(unused_imports)]
use super::prelude::*;

// TODO: get rid of fun_ext*

verus! {

/// General properties of spec functions.
///
/// For now, this just contains an axiom of function extensionality for
/// spec_fn.
/// DEPRECATED: use f1 =~= f2 or f1 =~~= f2 instead.
/// Axiom of function extensionality: two functions are equal if they are
/// equal on all inputs.
#[verifier::external_body]
#[cfg_attr(not(verus_verify_core), deprecated = "use f1 =~= f2 or f1 =~~= f2 instead")]
pub proof fn fun_ext<A, B>(f1: spec_fn(A) -> B, f2: spec_fn(A) -> B)
    requires
        forall|x: A| #![trigger f1(x)] f1(x) == f2(x),
    ensures
        f1 == f2,
{
}

} // verus!
/// A macro to conveniently generate similar functional extensionality axioms for functions that
/// take `n` arguments.
#[doc(hidden)]
macro_rules! gen_fun_ext_n {
    ($fun_ext:ident, $O:ident, $($x:ident : $I:ident),*) => {
        verus! {
          /// DEPRECATED: use f1 =~= f2 or f1 =~~= f2 instead.
          /// See [`fun_ext`]
          #[verifier::external_body]
          #[cfg_attr(not(verus_verify_core), deprecated = "use f1 =~= f2 or f1 =~~= f2 instead")]
          pub proof fn $fun_ext<$($I),*, $O>(f1: spec_fn($($I),*,) -> $O, f2: spec_fn($($I),*,) -> $O)
            requires forall |$($x: $I),*| #![trigger f1($($x),*)] f1($($x),*) == f2($($x),*)
            ensures f1 == f2
          {}
        }
    };
}

// Note: We start at 1 just for consistency; it is exactly equivalent to `fun_ext`
gen_fun_ext_n! { fun_ext_1, B, x1: A1 }
gen_fun_ext_n! { fun_ext_2, B, x1: A1, x2: A2 }
gen_fun_ext_n! { fun_ext_3, B, x1: A1, x2: A2, x3: A3 }
gen_fun_ext_n! { fun_ext_4, B, x1: A1, x2: A2, x3: A3, x4: A4 }
