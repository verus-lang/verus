// Branch-condition (MC/DC) coverage tests: Rust to VIR lowering (rust_verify/src/rust_to_vir_*.rs, fn_call_to_vir.rs, erase.rs, attributes.rs).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for rust_verify/src/rust_to_vir_func.rs:1774 atom 1 `ret_mode != Mode::Exec`
test_verify_one_file! {
    #[test] assoc_const_mode_attrs verus_code! {
        use vstd::prelude::*;

        pub trait Tr { const C: u8; }
        pub struct S1;
        pub struct S2;
        pub struct S3;
        impl Tr for S1 {
            #[verus::internal(spec)]
            const C: u8 = 1;
        }
        impl Tr for S2 {
            #[verus::internal(returns(spec))]
            const C: u8 = 2;
        }
        impl Tr for S3 {
            #[verifier::returns(spec)]
            const C: u8 = 3;
        }
    } => Err(err) => assert_vir_error_msgs(err, &["The verifier does not yet support the following Rust feature: non-default mode on associated const", "The verifier does not yet support the following Rust feature: non-default mode on associated const", "The verifier does not yet support the following Rust feature: non-default mode on associated const"])
}

// Independence pair for rust_verify/src/rust_to_vir_func.rs:801 atom 2 `compare_external_ty(tcx, verus_it...`; rust_verify/src/rust_to_vir_func.rs:808 atom 0 `(*adt_def1 == *adt_def2)`
test_verify_one_file! {
    #[test] assume_mismatch_adtdef code! {
        use vstd::prelude::*;
        pub fn ext(x: &Vec<u8>) -> usize { x.len() }
        verus! {
        pub assume_specification[ext](x: &Box<Vec<u8>>) -> usize;
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match `test_crate::ext` exactly ")
}

// Independence pair for rust_verify/src/attributes.rs:529 atom 0 `arg == "maybe_negative"`
test_verify_one_file! {
    #[test] attr_deprecated_recursive_types verus_code! {
        use vstd::prelude::*;

        #[verifier::maybe_negative]
        struct R<A> { a: A }
        #[verifier::strictly_positive]
        struct S<A> { a: A }
        spec fn get(r: R<u8>, s: S<u8>) -> u8 { (r.a + s.a) as u8 }
    } => Ok(())
}

// Independence pair for rust_verify/src/attributes.rs:786 atom 1 `arg == "checked"`; rust_verify/src/attributes.rs:853 atom 1 `name == "exec"`
test_verify_one_file! {
    #[test] attr_internal_near_miss verus_code! {
        use vstd::prelude::*;

        #[verus::internal(spec(unchecked))]
        fn b1() {}
        #[verus::internal(returns(ghost))]
        fn b2() {}
    } => Err(err) => assert_vir_error_msgs(err, &["unrecognized internal attribute", "unrecognized internal attribute"])
}

// Independence pair for rust_verify/src/attributes.rs:853 atom 0 `arg == "returns"`, atom 1 `name == "exec"`
test_verify_one_file! {
    #[test] attr_internal_returns verus_code! {
        use vstd::prelude::*;

        pub tracked struct Tok {}
        proof fn mk(tracked t: Tok) -> (tracked r: Tok) { t }
        #[verus::internal(returns(exec))]
        fn e() -> u8 { 1 }
        #[verus::internal(returns(spec))]
        #[verus::internal(spec)]
        fn s() -> u8 { 1 }
    } => Ok(())
}

// Independence pair for rust_verify/src/attributes.rs:462 atom 1; rust_verify/src/attributes.rs:602 atom 1; rust_verify/src/attributes.rs:630 atom 1; rust_verify/src/attributes.rs:728 atoms 0, 1; rust_verify/src/attributes.rs:763 atom 1; rust_verify/src/attributes.rs:768 atom 1
test_verify_one_file! {
    #[test] attr_near_miss_args verus_code! {
        use vstd::prelude::*;

        #[verifier::spec(unchecked)]
        fn a1() {}
        #[verifier::returns(ghost)]
        fn a2() {}
        #[verifier::deprecated_postcondition_mut_ref_style(maybe)]
        fn a3(x: &mut u8) {}
        #[verifier::assume(something_else)]
        fn a4() {}
        #[verifier::deny(something_else)]
        fn a5() {}
        #[verifier::external_trait_extension(A by B)]
        fn a6() {}
        #[verifier::not_an_attr(A via B)]
        fn a7() {}
    } => Err(err) => assert_vir_error_msgs(err, &["unrecognized verifier attribute", "unrecognized verifier attribute", "unrecognized verifier attribute", "unrecognized verifier attribute", "unrecognized verifier attribute", "unrecognized verifier attribute"])
}

// Independence pair for rust_verify/src/attributes.rs:620 atom 1 `r == "false"`
test_verify_one_file! {
    #[test] attr_unrecognized_args verus_code! {
        use vstd::prelude::*;

        #[verifier::loop_isolation(maybe)]
        #[verifier::assume(something_else)]
        #[verifier::deny(something_else)]
        fn f() {}
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

// Independence pair for rust_verify/src/attributes.rs:462 atoms 0, 1; rust_verify/src/attributes.rs:630 atoms 0, 1; rust_verify/src/external.rs:575 atoms 0, 1
test_verify_one_file! {
    #[test] attr_verifier_modes code! {
        use vstd::prelude::*;

        #[verifier::spec(checked)]
        fn sc(x: u8) -> bool { x < 10 }

        #[verifier::returns(proof)]
        #[verifier::proof]
        fn rp() {}

        #[verifier::returns(exec)]
        fn re() {}

        #[verifier::loop_isolation(false)]
        fn li() {}

        #[verifier::deprecated_postcondition_mut_ref_style(true)]
        fn dt(x: &mut u8) {}

        #[verifier::deprecated_postcondition_mut_ref_style(false)]
        fn df(x: &mut u8) {}

        #[verifier::reject_recursive_types]
        struct R<A> { a: A }

        #[verifier::accept_recursive_types]
        struct Acc<A> { a: A }

        struct MN<#[verifier::maybe_negative] A> { a: A }
        struct SP<#[verifier::strictly_positive] A> { a: A }
    } => Ok(_) => ()
}

// Independence pair for rust_verify/src/rust_to_vir_expr.rs:4348 atom 1 `ensure.0.len() > 0`
test_verify_one_file! {
    #[test] e4306_specfn_handwritten_ensures verus_code! {
        use vstd::prelude::*;

        spec fn f() -> spec_fn(int) -> int {
            |x: int| { ::verus_builtin::ensures(|r: int| r == x); x }
        }
    } => Err(err) => assert_vir_error_msg(err, "SpecFn should not have `requires` clause or `ensures` clause")
}

// Independence pair for rust_verify/src/rust_to_vir_expr.rs:4348 atom 0 `require.len() > 0`
test_verify_one_file! {
    #[test] e4306_specfn_handwritten_requires verus_code! {
        use vstd::prelude::*;

        spec fn f() -> spec_fn(int) -> int {
            |x: int| { ::verus_builtin::requires(x > 0); x }
        }
    } => Err(err) => assert_vir_error_msg(err, "SpecFn should not have `requires` clause or `ensures` clause")
}

// Independence pair for rust_verify/src/rust_to_vir_base.rs:910 atom 0 `t_args.iter().find(|x| x.as_type(...`
test_verify_one_file! {
    #[test] ext_impl_assoc_projection_const code! {
        use vstd::prelude::*;
        verus! {
        pub trait Tr<const N: usize> { type X; }
        impl Tr<3> for u8 { type X = u16; }
        pub trait Tr2 { type X; }
        }
        impl Tr2 for u16 { type X = <u8 as Tr<3>>::X; }
    } => Ok(())
}

// Independence pair for rust_verify/src/rust_to_vir_func.rs:2831 atom 1 `ignore[0] == krate_to_string_igno...`
test_verify_one_file! {
    #[test] ext_private_bound_wrong_crate verus_code! {
        use vstd::prelude::*;

        pub trait U {}
        #[verifier::external]
        pub trait T: U {}
        #[verifier::external_trait_specification]
        #[verifier::external_trait_private_bound(othercrate::U)]
        pub trait ExT {
            type ExternalTraitSpecificationFor: T;
        }
    } => Err(err) => assert_vir_error_msg(err, "external_trait_private_bound [\"othercrate\", \"U\"] is not a private non-local bound for this trait")
}

// Independence pair for rust_verify/src/rust_to_vir_trait.rs:309 atoms 0, 1; rust_verify/src/rust_to_vir_trait.rs:378 atoms 0, 1
test_verify_one_file! {
    #[test] ext_trait_items_misc code! {
        use vstd::prelude::*;
        pub trait T1 { fn f(&self) -> u8; }
        pub trait T2 { fn f(&self) -> u8; }
        pub trait T3 { fn f(&self) -> u8; }
        pub trait T4 { fn f(&self) -> u8; }
        pub trait T5 { const C: u8; }
        pub trait T6 { const C: u8; }
        verus! {
        #[verifier::external_trait_specification]
        pub trait ExT1 { type ExternalTraitSpecificationFor: T1; spec fn s(&self) -> bool; fn f(&self) -> u8; }
        #[verifier::external_trait_specification]
        pub trait ExT2 { type ExternalTraitSpecificationFor: T2; spec fn f(&self) -> u8; }
        #[verifier::external_trait_specification]
        pub trait ExT3 { type ExternalTraitSpecificationFor: T3; fn f(&self) -> u8 { 3 } }
        #[verifier::external_trait_specification]
        pub trait ExT4 { type ExternalTraitSpecificationFor: T4; fn f(&self) -> (r: u8) ensures r == 4 { 4 } }
        #[verifier::external_trait_specification]
        pub trait ExT5 { type ExternalTraitSpecificationFor: T5; const C: u8 = 5; }
        #[verifier::external_trait_specification]
        #[allow(non_upper_case_globals)]
        pub trait ExT6 { type ExternalTraitSpecificationFor: T6; const VERUS_SPEC__C: u8 = 6; const C: u8; }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["external spec extensions only allowed in `external_trait_extension` traits", "an `assume_specification` declaration cannot be marked `spec`", "`external_trait_specification` functions cannot have bodies", "`external_trait_specification` functions cannot have bodies", "`external_trait_specification` functions cannot have bodies", "trait method declaration body must start with call to no_method_body()"])
}

// Independence pair for rust_verify/src/external.rs:564 atom 1 `!general_item.is_module()`
test_verify_one_file! {
    #[test] external_ignored_attrs code! {
        use vstd::prelude::*;
        verus! {
        #[verifier::external]
        #[verifier::loop_isolation(false)]
        fn ext_f() {}

        #[verifier::external]
        #[verifier::loop_isolation(false)]
        mod ext_m { pub fn g() {} }

        #[verifier::loop_isolation(false)]
        fn verified_f() { let mut i: u8 = 0; while i < 3 invariant i <= 3 decreases 3 - i { i += 1; } }
        }
        #[verifier::loop_isolation(false)]
        mod ignored_m { pub fn h() {} }
    } => Ok(_) => ()
}

// Independence pair for rust_verify/src/rust_to_vir_func.rs:1951 atom 0 `mode != Mode::Exec`, atom 1 `vattrs.external_fn_specification`
test_verify_one_file! {
    #[test] f1954_extfnspec_spec_builtin verus_code! {
        use vstd::prelude::*;
        use verus_builtin::ProofFnReqEnsDef;

        #[verifier::external_trait_specification]
        pub trait MyExProofFn<Args, Output> {
            type ExternalTraitSpecificationFor: ProofFnReqEnsDef<Args, Output>;

            #[verifier::external_fn_specification]
            spec fn req(_args: Args) -> bool;

            spec fn ens(_args: Args, _output: Output) -> bool;
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification should be 'exec'")
}

// Independence pair for rust_verify/src/rust_to_vir_func.rs:777 atom 0 `const1 == const2`
test_verify_one_file! {
    #[test] f780_array_len_uneval code! {
        use vstd::prelude::*;
        verus! {
        #[verifier::external]
        pub fn real() -> [u8; 2 + 2] { [1, 2, 3, 4] }

        pub assume_specification[ real ]() -> (r: [u8; 4])
            ensures r[0] == 1;

        fn use_it() -> (x: u8) ensures x == 1 {
            let a = real();
            a[0]
        }
        }
        fn main() { assert!(use_it() == 1); }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match `test_crate::real` exactly ")
}

// Independence pair for rust_verify/src/rust_to_vir_impl.rs:502 atom 0 `impl_item.generics.predicates.len...`
test_verify_one_file! {
    #[test] impl_assoc_type_bounds verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X<T: Copy>; }
        impl Tr for u8 { type X<T: Copy> = T; }
    } => Err(err) => assert_vir_error_msgs(err, &["The verifier does not yet support the following Rust feature: trait generics", "The verifier does not yet support the following Rust feature: unsupported generics on associated"])
}

// Independence pair for rust_verify/src/fn_call_to_vir.rs:576 atom 0 `s.chars().all(|c| c.is_ascii_digi...`; rust_verify/src/fn_call_to_vir.rs:576 atom 0 `c.is_ascii_digit()`, atom 1 `c == '.'`
test_verify_one_file! {
    #[test] real_lit_bad_e5 verus_code! {
        use vstd::prelude::*;

        spec fn r() -> real { verus_builtin::spec_literal_decimal::<real>("1e5") }
    } => Err(err) => assert_vir_error_msg(err, "real literal must be digits, followed by a decimal point, followed by digits")
}

// Independence pair for rust_verify/src/reveal_hide.rs:26 atom 0 `block.stmts.len() != 1`
test_verify_one_file! {
    #[test] reveal_hide_handwritten verus_code! {
        use vstd::prelude::*;

        fn a() {}
        proof fn p() {
            ::verus_builtin::reveal_hide_({ fn b() {} fn c() {} a }, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: invalid reveal")
}

// Independence pair for rust_verify/src/reveal_hide.rs:26 atom 1 `!matches!(block.stmts[0].kind, ru...`
test_verify_one_file! {
    #[test] reveal_hide_handwritten_stmt verus_code! {
        use vstd::prelude::*;

        fn a() {}
        proof fn p() {
            ::verus_builtin::reveal_hide_({ let _x = 1u8; a }, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: invalid reveal")
}

// Independence pair for rust_verify/src/rust_to_vir_expr.rs:4414 atom 0 `verus_items::get_rust_item(tcx, a...`, atom 2 `verus_items::get_rust_item(tcx, a...`, atom 4 `verus_items::get_rust_item(tcx, a...`
test_verify_one_file! {
    #[test] t_022_struct_tail_unsize verus_code! {
        use vstd::prelude::*;

        struct S<T: ?Sized> { x: u8, t: T }
        fn f(s: &S<[u8; 3]>) { let r: &S<[u8]> = s; }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: unsizing operation from `&S<[u8; 3]>`")
}

// Independence pair for rust_verify/src/rust_to_vir_expr.rs:1179 atom 1 `body.expr.is_some()`
test_verify_one_file! {
    #[test] t_024_inv_block_tail_expr verus_code! {
        use vstd::prelude::*;

        fn f() -> u8 { #[verifier::invariant_block] { let a = 1u8; let b = 2u8; let c = 3u8; let d = 4u8; d } }
    } => Err(err) => assert_vir_error_msg(err, "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead")
}
