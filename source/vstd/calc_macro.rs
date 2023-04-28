//! The [`calc`] macro provides support for reasoning about a structured proof calculation.

#![allow(unused_imports)]
use crate::pervasive::*;
use builtin::*;
use builtin_macros::*;

verus! {

#[doc(hidden)]
#[macro_export]
macro_rules! calc_internal {
    // Getting the last of a series of expressions
    (__internal get_last $end:expr ;) => { $end };
    (__internal get_last $init:expr ; $($tail:expr);* ;) => {
        $crate::calc_macro::calc_internal!(__internal get_last $($tail ;)*)
    };

    // Getting the first non-empty tt
    (__internal first ($tt:tt)) => { $tt };
    (__internal first () $(($rest:tt))*) => { $crate::calc_macro::calc_internal!(__internal first $(($rest))*) };
    (__internal first ($tt:tt) $(($rest:tt))*) => { $tt };

    // Translation from a relation to the relevant expression
    (__internal expr (==) ($a:expr) ($b:expr)) => { ::builtin::equal($a, $b) };
    (__internal expr (<) ($a:expr) ($b:expr)) => { ($a < $b) };
    (__internal expr (<=) ($a:expr) ($b:expr)) => { ($a <= $b) };
    (__internal expr (>) ($a:expr) ($b:expr)) => { ($a > $b) };
    (__internal expr (>=) ($a:expr) ($b:expr)) => { ($a >= $b) };
    (__internal expr ($reln:tt) ($a:expr) ($b:expr)) => {
        compile_error!(concat!("INTERNAL ERROR\nUnexpected ", stringify!(($reln, $a, $b)))); }; // Fallthrough

    // Any of the relation steps occuring in the middle of the chain
    (__internal mid [$topreln:tt] $start:expr ; () $b:block $end:expr ; ) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($topreln) ($start) ($end)), { $b });
    }};
    (__internal mid [$topreln:tt] $start:expr ; ($reln:tt) $b:block $end:expr ; ) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($reln) ($start) ($end)), { $b });
    }};
    (__internal mid [$topreln:tt] $start:expr ; () $b:block $mid:expr ; $(($($tailreln:tt)?) $tailb:block $taile:expr);* ;) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($topreln) ($start) ($mid)), { $b });
        $crate::calc_macro::calc_internal!(__internal mid [$topreln] $mid ; $(($($tailreln)?) $tailb $taile);* ;);
    }};
    (__internal mid [$topreln:tt] $start:expr ; ($reln:tt) $b:block $mid:expr ; $(($($tailreln:tt)?) $tailb:block $taile:expr);* ;) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($reln) ($start) ($mid)), { $b });
        $crate::calc_macro::calc_internal!(__internal mid [$topreln] $mid ; $(($($tailreln)?) $tailb $taile);* ;);
    }};

    // Main entry point to this macro; this is still an internal macro, but this is where the main
    // `calc!` macro will invoke this.
    (($reln:tt) $start:expr ; $(($($midreln:tt)?) $b:block ; $mid:expr);* $(;)?) => {{
        ::builtin::assert_by(
            calc_internal!(__internal expr ($reln) ($start) ($crate::calc_macro::calc_internal!(__internal get_last $($mid ;)*))),
            { $crate::calc_macro::calc_internal!(__internal mid [$reln] $start ; $(($($midreln)?) $b $mid);* ;); }
        );
    }};

    // Fallback, if something _truly_ unexpected happens, explode and provide an error report.
    ($($tt:tt)*) => {
        compile_error!(concat!(
            "INTERNAL ERROR IN `calc!`.\n",
            "If you ever see this, please report your original `calc!` invocation to the Verus issue tracker.\n",
            "\n",
            "Internal state:",
            $("\n  `", stringify!($tt), "`",)*
        ));
    }
}

#[doc(hidden)]
#[macro_export]
// Auxiliary methods, that we do not want to invoke via the verus macro transformation (and thus
// should not go into `calc_internal`) but we don't want to clutter up the main `calc` macro either
// (mostly for documentation readability purposes).
//
// All these are internal and are not expected to be invoked directly from outside of this file.
macro_rules! calc_aux {
    // Confirming that only relations from an allow-set are allowed to be used in `calc!`.
    (confirm_allowed_relation (==)) => { }; // Allowed
    (confirm_allowed_relation (<)) => { }; // Allowed
    (confirm_allowed_relation (<=)) => { }; // Allowed
    (confirm_allowed_relation (>)) => { }; // Allowed
    (confirm_allowed_relation (>=)) => { }; // Allowed
    (confirm_allowed_relation ($t:tt)) => { compile_error!(concat!("Currently unsupported relation `", stringify!($t), "` in calc")); }; // Fallthrough

    // Confirm that an middle relation is consistent with the main relation
    (confirm_middle_relation (==) (==)) => { }; // Equality is only consistent with itself
    (confirm_middle_relation (<=) (<=)) => { }; // Less-than-or-equal can be proven via any combination of <, ==, and <=
    (confirm_middle_relation (<=) (==)) => { }; //
    (confirm_middle_relation (<=) (<)) => { }; //
    (confirm_middle_relation (<) (<)) => { }; // Strictly-less-than is allowed to use <= and == as intermediates, as long as at least one < shows up at some point
    (confirm_middle_relation (<) (<=)) => { }; //
    (confirm_middle_relation (<) (==)) => { }; //
    (confirm_middle_relation (>=) (>=)) => { }; // Greater-than-or-equal, similar to less-than-or-equal
    (confirm_middle_relation (>=) (==)) => { }; //
    (confirm_middle_relation (>=) (>)) => { }; //
    (confirm_middle_relation (>) (>)) => { }; // Strictly-greater-than, similar to less-than-or-equal
    (confirm_middle_relation (>) (>=)) => { }; //
    (confirm_middle_relation (>) (==)) => { }; //
    (confirm_middle_relation ($main:tt) ($middle:tt)) => {
        compile_error!(concat!("Potentially inconsistent relation `", stringify!($middle), "` with `", stringify!($main), "`")); }; // Fallthrough
}

/// The `calc!` macro supports structured proofs through calculations.
///
/// In particular, one can show `a_1 R a_n` for some transitive relation `R` by performing a series
/// of steps `a_1 R a_2`, `a_2 R a_3`, ... `a_{n-1} R a_n`. The calc macro provides both convenient
/// syntax sugar to perform such a proof conveniently, without repeating oneself too often, or
/// exposing the internal steps to the outside context.
///
/// The expected usage looks like:
///
/// ```
/// calc! {
///   (R)
///   a_1; { /* proof that a_1 R a_2 */ }
///   a_2; { /* proof that a_2 R a_3 */ }
///    ...
///   a_n;
/// }
/// ```
///
/// Currently, the `calc!` macro supports common transitive relations for `R`, and this set of
/// relations may be extended in the future.
///
/// Note that `calc!` also supports stating intermediate relations, as long as they are consistent
/// with the main relation `R`. If consistency cannot be immediately shown, Verus will give a
/// helpful message about this. Intermediate relations can be specified by placing them right before
/// the proof block of that step.
///
/// A simple example of using intermediate relations looks like:
///
/// ```
/// let x: int = 2;
/// let y: int = 5;
/// calc! {
///   (<=)
///   x; (==) {}
///   5 - 3; (<) {}
///   5; {} // Notice that no intermediate relation is specified here, so `calc!` will consider the top-level relation `R`; here `<=`.
///   y;
/// }
/// ```

#[allow(unused_macros)]
#[macro_export]
macro_rules! calc {
    // The main entry point to this macro.
    (($reln:tt) $start:expr ; $($(($middlereln:tt))? $b:block $mid:expr);* $(;)?) => {
        $crate::calc_macro::calc_aux!(confirm_allowed_relation ($reln));
        $($(
            $crate::calc_macro::calc_aux!(confirm_allowed_relation ($middlereln));
            $crate::calc_macro::calc_aux!(confirm_middle_relation ($reln) ($middlereln));
        )?)*
        ::builtin_macros::verus_proof_macro_explicit_exprs!(
            $crate::calc_macro::calc_internal!(
                ($reln) @@$start ; $(($($middlereln)?) @@$b ; @@$mid);* ;
            )
        )
    };

    // Fallback, if we see something that is entirely unexpected, we tell the user what the usage should look like.
    ($($tt:tt)*) => {
        compile_error!(concat!(
            "Unexpected invocation of `calc!`. Expected usage looks like \n",
            "  calc! { (==)\n",
            "     a;\n",
            "     (==) { ... }\n",
            "     b + c;\n",
            "     (==) { ... }\n",
            "     d;\n",
            "  }\n",
            "\n",
            "Received:\n  calc! { ",
            $(stringify!($tt), " "),*,
            "}",
        ))
    }
}

#[doc(hidden)]
pub use calc_internal;
#[doc(hidden)]
pub use calc_aux;
pub use calc;

} // verus!
