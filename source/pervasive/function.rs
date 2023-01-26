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
