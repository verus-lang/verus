#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

// TODO: get rid of fun_ext*

verus! {

  /// General properties of spec functions.
  ///
  /// For now, this just contains an axiom of function extensionality for
  /// FnSpec.

  /// DEPRECATED: use builtin::ext_equal(f1, f2) or builtin::ext_equal_deep(f1, f2) instead.
  /// Axiom of function extensionality: two functions are equal if they are
  /// equal on all inputs.
  #[verifier(external_body)]
  #[deprecated = "use builtin::ext_equal(f1, f2) or builtin::ext_equal_deep(f1, f2) instead"]
  pub proof fn fun_ext<A, B>(f1: FnSpec(A) -> B, f2: FnSpec(A) -> B)
    requires forall |x: A| #![trigger f1(x)] f1(x) == f2(x)
    ensures f1 == f2
  {}
}

/// A macro to conveniently generate similar functional extensionality axioms for functions that
/// take `n` arguments.
#[doc(hidden)]
macro_rules! gen_fun_ext_n {
  ($fun_ext:ident, $O:ident, $($x:ident : $I:ident),*) => {

    verus! {
      /// DEPRECATED: use builtin::ext_equal(f1, f2) or builtin::ext_equal_deep(f1, f2) instead.
      /// See [`fun_ext`]
      #[verifier(external_body)]
      #[deprecated = "use builtin::ext_equal(f1, f2) or builtin::ext_equal_deep(f1, f2) instead"]
      pub proof fn $fun_ext<$($I),*, $O>(f1: FnSpec($($I),*,) -> $O, f2: FnSpec($($I),*,) -> $O)
        requires forall |$($x: $I),*| #![trigger f1($($x),*)] f1($($x),*) == f2($($x),*)
        ensures f1 == f2
      {}
    }
  }

}

// Note: We start at 1 just for consistency; it is exactly equivalent to `fun_ext`
gen_fun_ext_n! { fun_ext_1, B, x1: A1 }
gen_fun_ext_n! { fun_ext_2, B, x1: A1, x2: A2 }
gen_fun_ext_n! { fun_ext_3, B, x1: A1, x2: A2, x3: A3 }
gen_fun_ext_n! { fun_ext_4, B, x1: A1, x2: A2, x3: A3, x4: A4 }
