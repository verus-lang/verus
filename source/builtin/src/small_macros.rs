/// Use #[verifier::verify] and those verus-specific macros enables developers
/// to annotate Rust code in standard Rust code, eliminating the need to wrap
/// exec code inside `verus! {}`.
///
/// Limitations:
/// - This macro does not support all `verus` syntax, particularly those
///   constructs not accepted by `rustc`.
/// - For defining complex `verus` specifications or proof functions, developers
///   should still use `verus! {}`.
///
/// Usage:
/// - To apply `requires`, `ensures`, `invariant`, or `proof` in `exec`
///   functions annotated with `#[verifier::verify]`, developers should call the
///   corresponding macros at the beginning of the function or loop.
///
/// Rationale:
/// - This approach avoids introducing new syntax into existing Rust executable
///   code, allowing verification and non-verification developers collaborate
///   without affecting others.
///   For developers who do not understand verification, they can easily ignore
///   verus code via feature selection and use standard rust tools like
///   `rustfmt` and `rust-analyzer`.
///
/// Example:
/// - Refer to the `test_my_funs_with_verus_verify` in `example/syntax.rs`.

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! verus_proof_macro_exprs_args {
    ($($x:tt)*) => {
        ($($x)*)
    };
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! requires {
    ($($x:tt)*) => {
        #[cfg(verus_keep_ghost_body)]
        ::builtin::requires(::builtin_macros::verus_proof_macro_exprs!(
            ::builtin::verus_proof_macro_exprs_args!([$($x)*])
        ));
    };
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! ensures {
    ($($x:tt)*) => {
        #[cfg(verus_keep_ghost_body)]
        ::builtin::ensures(::builtin_macros::verus_proof_macro_exprs!(
            ::builtin::verus_proof_macro_exprs_args!($($x)*)
        ));
    };
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! proof {
    ($($x:tt)*) => {
        #[cfg(verus_keep_ghost_body)]
        ::builtin_macros::verus_proof_macro_exprs!{
            ::builtin::verus_proof_macro_exprs_args!{
            #[verifier::proof_block]
            {$($x)*}
            }
        }
    };
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! invariant {
    ($($x:tt)*) => {
        #[cfg(verus_keep_ghost_body)]
        ::builtin::invariant(::builtin_macros::verus_proof_macro_exprs!(
            ::builtin::verus_proof_macro_exprs_args!([$($x)*])
        ));
    };
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! verus_var {
    ($($x:tt)*) => {
        #[verus::internal(proof)]
        ::builtin::invariant(::builtin_macros::verus_proof_macro_exprs!(
            ::builtin::verus_proof_macro_exprs_args!(
                $($x:tt)*
            )
        ));
    };
}