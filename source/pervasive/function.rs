#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

  /// General properties of spec functions.
  ///
  /// For now, this just contains an axiom of function extensionality for
  /// FnSpec.

  /// A dummy expression used only to give `fun_ext` a trigger. See the comment
  /// below.
  pub closed spec fn dummy_trigger<A>(x: A);

  /// Axiom of function extensionality: two functions are equal if they are
  /// equal on all inputs.
  #[verifier(external_body)]
  pub proof fn fun_ext<A, B>(f1: FnSpec(A) -> B, f2: FnSpec(A) -> B)
    // NOTE: this dummy trigger is needed since Verus requires some trigger
    // (even for external_body definitions), and f1(x) is not accepted. It is
    // never used by the caller.
    requires forall |x: A| #![trigger dummy_trigger(x)] f1(x) == f2(x)
    ensures f1 == f2
  {}
}

/// A macro to conveniently generate similar functional extensionality axioms for functions that
/// take `n` arguments.
#[doc(hidden)]
macro_rules! gen_fun_ext_n {
  ($fun_ext:ident, $dummy_trigger:ident, $O:ident, $($x:ident : $I:ident),*) => {

    verus! {
      /// See [`dummy_trigger`]
      pub closed spec fn $dummy_trigger < $($I),* >($($x : $I),*);

      /// See [`fun_ext`]
      #[verifier(external_body)]
      pub proof fn $fun_ext<$($I),*, $O>(f1: FnSpec($($I),*,) -> $O, f2: FnSpec($($I),*,) -> $O)
        requires forall |$($x: $I),*| #![trigger $dummy_trigger($($x),*)] f1($($x),*) == f2($($x),*)
        ensures f1 == f2
      {}
    }
  }

}

// Note: We start at 1 just for consistency; it is exactly equivalent to `fun_ext`
gen_fun_ext_n! { fun_ext_1, dummy_trigger_1, B, x1: A1 }
gen_fun_ext_n! { fun_ext_2, dummy_trigger_2, B, x1: A1, x2: A2 }
gen_fun_ext_n! { fun_ext_3, dummy_trigger_3, B, x1: A1, x2: A2, x3: A3 }
gen_fun_ext_n! { fun_ext_4, dummy_trigger_4, B, x1: A1, x2: A2, x3: A3, x4: A4 }
