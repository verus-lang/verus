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
        $crate::pervasive::calc::calc_internal!(__internal get_last $($tail ;)*)
    };
    // Any of the internal relation steps
    (__internal mid $start:expr ; (==) $b:block $end:expr ; ) => {{
        ::builtin::assert_by(::builtin::equal($start, $end), { $b });
    }};
    (__internal mid $start:expr ; (==) $b:block $mid:expr ; $((==) $tailb:block $taile:expr);* ;) => {{
        ::builtin::assert_by(::builtin::equal($start, $mid), { $b });
        $crate::pervasive::calc::calc_internal!(__internal mid $mid ; $((==) $tailb $taile);* ;);
    }};
    // Main entry point to this macro
    ((==) $start:expr ; $((==) $b:block ; $mid:expr);* $(;)?) => {{
        ::builtin::assert_by(::builtin::equal($start, $crate::pervasive::calc::calc_internal!(__internal get_last $($mid ;)*)), {
            $crate::pervasive::calc::calc_internal!(__internal mid $start ; $((==) $b $mid);* ;);
        });
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
/// Currently, the `calc!` macro only supports equality (i.e., currently `R` can only be `==`), but
/// support for other transitive relations is planned. Thus, the full accepted grammar supports
/// mentioning `R` again just before the block proving an internal relation. This will be extended
/// in the future to support internal transition steps with compatible relations (e.g., to prove `a
/// <= z`, an internal step might look like `x == y`, which is compatible with the overall
/// relation).

#[allow(unused_macros)]
#[macro_export]
macro_rules! calc {
    ((==) $start:expr ; $((==) $b:block $mid:expr);* $(;)?) => {
        ::builtin_macros::verus_proof_macro_explicit_exprs!(
            $crate::pervasive::calc::calc_internal!(
                (==) @@$start ; $((==) @@$b ; @@$mid);* ;
            )
        )
    };
    ((==) $start:expr ; $($((==))? $b:block $mid:expr);* $(;)?) => {
        ::builtin_macros::verus_proof_macro_explicit_exprs!(
            $crate::pervasive::calc::calc_internal!(
                (==) @@$start ; $((==) @@$b ; @@$mid);* ;
            )
        )
    };
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
pub use calc;

} // verus!
