/// Macros defined in this module enables developers to annotate Rust code in
/// standard Rust code with #[verus_verify], eliminating the need to wrap exec
/// code inside `verus! {}`.
/// Refer to builtin_macros::attr_rewrite.

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! verus_proof_macro_exprs_args {
    ($($x:tt)*) => {
        ($($x)*)
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
