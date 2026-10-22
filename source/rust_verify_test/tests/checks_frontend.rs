// Tests for rust to VIR lowering (rust_verify/src/rust_to_vir_*.rs, fn_call_to_vir.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers rust_to_vir_expr.rs:1945
test_verify_one_file! {
    #[test] expr_016_enum_isize_discriminant_range verus_code! {
        use vstd::prelude::*;

        #[repr(isize)]
        #[derive(Clone, Copy)]
        enum E { A = -3000000000, B = 0 }
        fn f(e: E) -> isize { e as isize }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: discriminant does not fit in 32-bits")
}

// Covers rust_to_vir_expr.rs:932, 933
test_verify_one_file! {
    #[test] expr_019_slice_pattern_rest verus_code! {
        use vstd::prelude::*;

        fn f(s: &[u8]) -> u8 { match s { [a, ..] => *a, [] => 0 } }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: slice patterns with '..'")
}

// Covers rust_to_vir_expr.rs:3965, 3966
test_verify_one_file! {
    #[test] expr_020_let_infer_mode_prophetic verus_code! {
        use vstd::prelude::*;

        fn e() {
            #[verus::internal(infer_mode)] #[verifier::prophetic] let x = 1u8;
        }
    } => Err(err) => assert_vir_error_msg(err, "verus internal error: decl is marked infer_mode and prophetic")
}

// Covers rust_to_vir_expr.rs:1179
test_verify_one_file! {
    #[test] expr_023_inv_block_stmt_count verus_code! {
        use vstd::prelude::*;

        fn f() { #[verifier::invariant_block] { let a = 1u8; } }
    } => Err(err) => assert_vir_error_msg(err, "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead")
}

// Covers rust_to_vir_expr.rs:1208
test_verify_one_file! {
    #[test] expr_025_inv_block_guard_mismatch verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        pub struct P;
        impl InvariantPredicate<(), u8> for P { open spec fn inv(k: (), v: u8) -> bool { true } }
        fn f(Tracked(i): Tracked<&AtomicInvariant<(), u8, P>>, Tracked(guard2): Tracked<InvariantBlockGuard<'static>>) {
            let credit = create_open_invariant_credit();
            #[verifier::invariant_block] {
                vstd::invariant::spend_open_invariant_credit(credit);
                #[allow(unused_mut)] let (guard, mut inner) = vstd::invariant::open_atomic_invariant_begin(i);
                { }
                vstd::invariant::open_invariant_end(guard2, inner);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead")
}

// Covers rust_to_vir_expr.rs:1208
test_verify_one_file! {
    #[test] expr_026_inv_block_inner_mismatch verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        pub struct P;
        impl InvariantPredicate<(), u8> for P { open spec fn inv(k: (), v: u8) -> bool { true } }
        fn f(Tracked(i): Tracked<&AtomicInvariant<(), u8, P>>, Tracked(inner2): Tracked<u8>) {
            let credit = create_open_invariant_credit();
            #[verifier::invariant_block] {
                vstd::invariant::spend_open_invariant_credit(credit);
                #[allow(unused_mut)] let (guard, mut inner) = vstd::invariant::open_atomic_invariant_begin(i);
                { }
                vstd::invariant::open_invariant_end(guard, inner2);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "malformed invariant block; use `open_atomic_invariant!` or `open_local_invariant!` macro instead")
}

// Covers rust_to_vir_expr.rs:1477
test_verify_one_file! {
    #[test] expr_027_au_block_res_mismatch verus_code! {
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub tracked struct Token { state: u16 }
        fn generic_atomic<F>(_callback: F, other: Tracked<Commit<Token>>)
            atomically (atomic_update) {
                (old: Token) -> (new: Commit<Token>),
                ensures new@ == old,
            },
        {
            #[verifier::open_au_block] {
                let guard = vstd::atomic::try_open_atomic_update_begin(atomic_update);
                let token = vstd::atomic::bind_lifetime_internal(&guard);
                let res = { Tracked(Commit(token)) };
                match res {
                    res => vstd::atomic::try_open_atomic_update_end(guard, other),
                }
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "malformed atomic update block; use `try_open_atomic_update!` macro instead")
}

// Covers rust_to_vir_expr.rs:1477
test_verify_one_file! {
    #[test] expr_028_au_block_guard_mismatch verus_code! {
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub tracked struct Token { state: u16 }
        fn g<P: UpdatePredicate<Token, Commit<Token>>>(
            Tracked(au): Tracked<AtomicUpdate<Token, Commit<Token>, P>>,
            Tracked(guard2): Tracked<BlockGuard<AtomicUpdate<Token, Commit<Token>, P>>>,
        ) {
            #[verifier::open_au_block] {
                let guard = vstd::atomic::try_open_atomic_update_begin(au);
                let token = vstd::atomic::bind_lifetime_internal(&guard);
                let res = { Tracked(Commit(token)) };
                match res {
                    res => vstd::atomic::try_open_atomic_update_end(guard2, res),
                }
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "malformed atomic update block; use `try_open_atomic_update!` macro instead")
}

// Covers rust_to_vir_expr.rs:4451, 4466, 4534; sst_to_air.rs:237; syntax.rs:6166
test_verify_one_file! {
    #[test] expr_032_ghost_slice_ptr_casts verus_code! {
        use vstd::prelude::*;

        spec fn f(p: *const [u8]) -> *const [u16] { p as *const [u16] }
        spec fn g(p: *const [u8]) -> *const str { p as *const str }
        spec fn h(p: *const str) -> *const [u8] { p as *const [u8] }
        proof fn t(p: *const [u8]) { assert(f(p)@.metadata == p@.metadata); assert(f(p)@.addr == p@.addr); }
    } => Ok(())
}

// Covers rust_to_vir_expr.rs:3695
test_verify_one_file! {
    #[test] expr_035_float_eq_foreign_rhs verus_code! {
        use vstd::prelude::*;

        pub struct L;
        impl PartialEq<L> for f64 {
            fn eq(&self, other: &L) -> (r: bool) ensures r { true }
        }
        fn t(x: f64) { let r = x == L; assert(r); }
    } => Err(err) => assert_vir_error_msgs(err, &["postcondition not satisfied"])
}

// Covers rust_to_vir_expr.rs:2796
test_verify_one_file! {
    #[test] expr_050_float_rem verus_code! {
        use vstd::prelude::*;

        fn f(a: f64, b: f64) -> f64 { a % b }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: applying binary operator Rem to types")
}

// Covers rust_to_vir_func.rs:1399
test_verify_one_file! {
    #[test] final_msg524_a1_nested_groups verus_code! {
        use vstd::prelude::*;

        mod m {
        use vstd::prelude::*;
        #[verifier::opaque] pub open spec fn f(i: int) -> bool { false }
        broadcast use G1;
        pub broadcast group G1 { G2 }
        pub broadcast group G2 { p }
        pub broadcast proof fn p(i: int) ensures #[trigger] f(i) { assert(f(i)); }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

// Covers rust_to_vir_func.rs:808
test_verify_one_file! {
    #[test] funcs_assume_mismatch_adtargs code! {
        use vstd::prelude::*;
        pub fn ext(x: Box<[u8]>) -> usize { x.len() }
        verus! {
        pub assume_specification[ext](x: Box<[u8; 2]>) -> usize;
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match `test_crate::ext` exactly ")
}

// Covers rust_to_vir_func.rs:794
test_verify_one_file! {
    #[test] funcs_assume_mismatch_rawptr code! {
        use vstd::prelude::*;
        pub fn ext(x: *const u8) -> u8 { 0 }
        verus! {
        pub assume_specification[ext](x: *mut u8) -> u8;
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match `test_crate::ext` exactly ")
}

// Covers rust_to_vir_func.rs:3578
test_verify_one_file! {
    #[test] funcs_fn_opaque_both verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        #[verifier::opaque_outside_module]
        spec fn f() -> int { 1 }
    } => Err(err) => assert_vir_error_msg(err, "function is marked both 'opaque' and 'opaque_outside_module'")
}

// Covers rust_to_vir_func.rs:3562
test_verify_one_file! {
    #[test] funcs_fn_opaque_outside_nobody verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque_outside_module]
        uninterp spec fn f() -> int;
    } => Err(err) => assert_vir_error_msg(err, "opaque has no effect on a function without a body")
}

// Covers rust_to_vir_func.rs:3555
test_verify_one_file! {
    #[test] funcs_fn_opaque_outside_proof verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque_outside_module]
        proof fn p() {}
    } => Err(err) => assert_vir_error_msg(err, "function is marked `opaque` but it is not a `spec` function")
}

// Covers rust_to_vir_func.rs:3555
test_verify_one_file! {
    #[test] funcs_fn_opaque_proof verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        proof fn p() {}
    } => Err(err) => assert_vir_error_msg(err, "function is marked `opaque` but it is not a `spec` function")
}

// Covers rust_to_vir_func.rs:2352
test_verify_one_file! {
    #[test] funcs_fn_proof_atomic verus_code! {
        use vstd::prelude::*;

        proof fn p(x: int)
            atomically (au) {
                (y: int) -> (z: int),
            },
        {}
    } => Err(err) => assert_vir_error_msg(err, "non-exec function cannot have atomic specification")
}

// Covers rust_to_vir_func.rs:2349
test_verify_one_file! {
    #[test] funcs_fn_proof_recommends verus_code! {
        use vstd::prelude::*;

        proof fn p(x: int) recommends x > 0 {}
    } => Err(err) => assert_vir_error_msg(err, "non-spec functions cannot have recommends")
}

// Covers rust_to_vir_base.rs:615, 2137, 2139, 2141, 2158; well_formed.rs:81, 2180
test_verify_one_file! {
    #[test] funcs_generic_param_attrs verus_code! {
        use vstd::prelude::*;

        pub struct R<#[verifier::reject_recursive_types] A> { a: A }
        pub struct G<#[verifier::reject_recursive_types_in_ground_variants] A> { a: A }
        pub struct Acc<#[verifier::accept_recursive_types] A> { a: A } // FAILS
        fn p<T: ?Sized + core::ptr::Pointee>(x: &T) {}
        fn main() { let r = R { a: 1u8 }; let g = G { a: 1u8 }; let c = Acc { a: 1u8 }; p(&3u8); }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["datatype must have at least one non-recursive variant".to_string()]);
        assert_fails(err.clone(), 1);
    }
}

// Covers fn_call_to_vir.rs:578
test_verify_one_file! {
    #[test] funcs_real_lit_bad_lead verus_code! {
        use vstd::prelude::*;

        spec fn r() -> real { verus_builtin::spec_literal_decimal::<real>(".5") }
    } => Err(err) => assert_vir_error_msg(err, "real literal must be digits, followed by a decimal point, followed by digits")
}

// Covers fn_call_to_vir.rs:577
test_verify_one_file! {
    #[test] funcs_real_lit_bad_nodot verus_code! {
        use vstd::prelude::*;

        spec fn r() -> real { verus_builtin::spec_literal_decimal::<real>("15") }
    } => Err(err) => assert_vir_error_msg(err, "real literal must be digits, followed by a decimal point, followed by digits")
}

// Covers fn_call_to_vir.rs:579
test_verify_one_file! {
    #[test] funcs_real_lit_bad_trail verus_code! {
        use vstd::prelude::*;

        spec fn r() -> real { verus_builtin::spec_literal_decimal::<real>("5.") }
    } => Err(err) => assert_vir_error_msg(err, "real literal must be digits, followed by a decimal point, followed by digits")
}

// Covers fn_call_to_vir.rs:682
test_verify_one_file! {
    #[test] funcs_returns_two verus_code! {
        use vstd::prelude::*;

        fn f() -> u8 {
            ::verus_builtin::returns([1u8, 1u8]);
            1
        }
    } => Err(err) => assert_vir_error_msg(err, "`returns` clause should have exactly 1 expression")
}

// Covers fn_call_to_vir.rs:605
test_verify_one_file! {
    #[test] funcs_spec_lit_int_empty verus_code! {
        use vstd::prelude::*;

        spec fn r() -> int { verus_builtin::spec_literal_int("") }
    } => Err(err) => assert_vir_error_msg(err, "spec_literal_* requires a string literal")
}

// Covers fn_call_to_vir.rs:605
test_verify_one_file! {
    #[test] funcs_spec_lit_int_neg verus_code! {
        use vstd::prelude::*;

        spec fn r() -> int { verus_builtin::spec_literal_int("-5") }
    } => Err(err) => assert_vir_error_msg(err, "spec_literal_* requires a string literal")
}

// Covers rust_to_vir_func.rs:2056
test_verify_one_file! {
    #[test] funcs_trait_assoc_const_impl verus_code! {
        use vstd::prelude::*;

        pub trait T { const C: u8; fn f(&self) -> u8; }
        pub struct S;
        impl T for S { const C: u8 = 3; fn f(&self) -> u8 { Self::C } }
        fn main() { let s = S; let x = s.f(); }
    } => Ok(())
}

// Covers external.rs:319, 320, 321, 323
test_verify_one_file! {
    #[test] funcs_trait_item_external verus_code! {
        use vstd::prelude::*;

        pub trait T {
            fn a(&self) -> u8;
            #[verifier::external]
            fn b(&self) -> u8;
        }
    } => Err(err) => assert_vir_error_msgs(err, &["An individual item of a trait cannot be marked external. Perhaps you meant to mark the entire trait", "An individual item of a trait cannot be marked external. Perhaps you meant to mark the entire trait"])
}

// Covers rust_to_vir_func.rs:2352
test_verify_one_file! {
    #[test] propose_1_11718 verus_code! {
        use vstd::prelude::*;

        pub tracked struct Token { state: u16 }
        impl Token {
            pub open spec fn is_valid(self) -> bool { true }
        }
        pub fn atomic_function(x: u8, y: i32)
            atomically (atomic_update) {
                (old: Token) -> (new: Token),
                ensures new == old,
            },
        {
            assert(atomic_update.pred().args(x, y));
            assume(false);
        }
    } => Ok(())
}

// Covers rust_to_vir_expr.rs:2771
test_verify_one_file! {
    #[test] propose_1_12783 verus_code! {
        use vstd::prelude::*;

        fn f(a: i8, b: i8) requires b != 0, !(a == -128 && b == -1) { let c = a / b; assert(-128 <= c && c <= 127); }
    } => Ok(())
}

// Covers rust_to_vir_expr.rs:2847
test_verify_one_file! {
    #[test] propose_2_12808_ghost_copy_mut_borrow verus_code! {
        use vstd::prelude::*;

        fn snap() {
            let mut x: u64 = 0;
            let r = &mut x;
            let ghost s = x;
            *r = 20;
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `(Verus spec x)` as immutable because it is also borrowed as mutable")
}

// Covers fn_call_to_vir.rs:2144, 2145, 2146
test_verify_one_file! {
    #[test] r2_modes_f_add_typaram_integer verus_code! {
        use vstd::prelude::*;

        spec fn f<T: verus_builtin::Integer>(x: T, y: T) -> T { verus_builtin::add(x, y) }
    } => Err(err) => assert_vir_error_msg(err, "types are not compatible with this operator (got T/#0 and T/#0)")
}

// Covers fn_call_to_vir.rs:2506
test_verify_one_file! {
    #[test] r2_modes_f_after_borrow_index_field verus_code! {
        use vstd::prelude::*;

        fn f() {
            let mut a = [(1u8, 2u8), (3u8, 4u8)];
            proof { assert(after_borrow(a[0].0) == 1); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`after_borrow` expects a local variable, possibly with dereferences or field accesses")
}

// Covers fn_call_to_vir.rs:2506
test_verify_one_file! {
    #[test] r2_modes_f_after_borrow_union_field verus_code! {
        use vstd::prelude::*;

        union U { a: u8, b: u16 }
        fn f() {
            let mut u = U { a: 1 };
            proof { assert(after_borrow(u.a) == 1); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`after_borrow` expects a local variable, possibly with dereferences or field accesses")
}

// Covers fn_call_to_vir.rs:1719
test_verify_one_file! {
    #[test] r2_modes_f_cast_typaram_no_integer verus_code! {
        use vstd::prelude::*;

        spec fn f<T: Copy>(x: T) -> int { x as int }
    } => Err(err) => assert_vir_error_msg(err, "Verus currently only supports casts from integer types, floats, bool, enum (unit-only or")
}

// Covers fn_call_to_vir.rs:2594, 2600
test_verify_one_file_with_options! {
    #[test] r2_modes_f_ensures_zero_param_closure ["--output-json"] => code! {
        use vstd::prelude::*;
        #[verifier::verify]
        fn g(x: u8) {
            ::verus_builtin::ensures(|| [x == 1]); // FAILS
        }
        #[verifier::verify]
        fn h() {
            g(2);
            ::verus_builtin::assert_(false);
        }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["postcondition not satisfied".to_string()]);
        assert_fails(err.clone(), 1);
        assert_eq!(err.json_output.as_ref().unwrap()["verification-results"]["verified"], 1);
    }
}

// Covers fn_call_to_vir.rs:2036, 2037, 2045, 2046, 2047
test_verify_one_file! {
    #[test] r2_modes_f_spec_eq_mut_ref verus_code! {
        use vstd::prelude::*;

        fn f(x: &mut u8)
            requires *old(x) == 5,
        {
            proof { assert(x == 5u8); }
        }
    } => Err(err) => assert_vir_error_msg(err, "mismatched types; types must be compatible to use == or !=")
}

// Covers rust_to_vir_func.rs:622, 626, 641, 720, 743, 750, 777, 778, 795
test_verify_one_file! {
    #[test] r2_traits_assume_spec_opaque_mismatch code! {
        use vstd::prelude::*;
        pub trait Two { type A; type B; }
        impl Two for u8 { type A = u8; type B = u8; }
        pub fn r1() -> impl Clone + Sync { 0u8 }
        pub fn r2() -> [impl Clone + Sync; 1] { [0u8] }
        pub fn r3() -> *const (impl Clone + Sync) { core::ptr::null::<u8>() }
        pub fn r4() -> impl Two<A = u8, B = u8> { 0u8 }
        pub fn r5<T: Iterator>(mut t: T) -> T::Item { t.next().unwrap() }
        pub fn r6() -> [impl Clone + Sync; 1] { [0u8] }
        verus! {
        pub assume_specification [ r1 ]() -> impl Clone + Send;
        pub assume_specification [ r2 ]() -> [impl Clone + Send; 1];
        pub assume_specification [ r3 ]() -> *const (impl Clone + Send);
        pub assume_specification [ r4 ]() -> impl Two<B = u8, A = u8>;
        pub assume_specification<T: Iterator> [ r5::<T> ](t: T) -> impl Sized;
        pub assume_specification [ r6 ]() -> [impl Clone + Sync; 1];
        }
    } => Err(err) => assert_vir_error_msgs(err, &["assume_specification requires function type signature to match `test_crate::r1` exactly ", "assume_specification requires function type signature to match `test_crate::r2` exactly ", "assume_specification requires function type signature to match `test_crate::r3` exactly ", "assume_specification requires function type signature to match `test_crate::r4` exactly ", "assume_specification requires function type signature to match `test_crate::r5` exactly ", "The verifier does not yet support the following Rust feature: this type of bound"])
}

// Covers rust_to_vir_func.rs:784, 785
test_verify_one_file_with_options! {
    #[test] r2_traits_assume_spec_pattern_type ["no-auto-import-verus_builtin", "vstd"] => code! {
        #![feature(pattern_types, pattern_type_macro)]
        use vstd::prelude::*;
        use std::pat::pattern_type;
        pub type P = pattern_type!(u32 is 1..);
        pub fn r(x: pattern_type!(u32 is 1..)) -> u32 { 1 }
        pub fn r2(x: P) -> u32 { 1 }
        verus! {
        pub assume_specification [ r ](x: pattern_type!(u32 is 1..)) -> u32;
        pub assume_specification [ r2 ](x: P) -> u32;
        }
    } => Err(err) => assert_vir_error_msgs(err, &["assume_specification requires function type signature to match `test_crate::r` exactly ", "The verifier does not yet support the following Rust feature: pattern types"])
}

// Covers rust_to_vir_func.rs:505, 536, 537, 538
test_verify_one_file! {
    #[test] r2_traits_ext_spec_mismatch_kinds code! {
        use vstd::prelude::*;
        pub trait A1 { fn f(&self, x: (u8, u8)); }
        pub trait A2 { fn f(&self, x: (u8, u8)); }
        pub trait B1 { fn f(&self, x: *const u8); }
        pub trait B2 { fn f(&self, x: *const u8); }
        pub trait C1 { fn f(&self, x: [u8; 2]); }
        pub trait C2 { fn f(&self, x: [u8; 2]); }
        pub trait D1 { fn f(&self, x: Option<u8>); }
        pub trait D2 { fn f(&self, x: Option<u8>); }
        pub trait E { fn f(&self, x: *const u8, y: [u8; 2]); }
        verus! {
        #[verifier::external_trait_specification]
        pub trait ExA1 { type ExternalTraitSpecificationFor: A1; fn f(&self, x: (u8,)); }
        #[verifier::external_trait_specification]
        pub trait ExA2 { type ExternalTraitSpecificationFor: A2; fn f(&self, x: (u8, u16)); }
        #[verifier::external_trait_specification]
        pub trait ExB1 { type ExternalTraitSpecificationFor: B1; fn f(&self, x: *mut u8); }
        #[verifier::external_trait_specification]
        pub trait ExB2 { type ExternalTraitSpecificationFor: B2; fn f(&self, x: *const u16); }
        #[verifier::external_trait_specification]
        pub trait ExC1 { type ExternalTraitSpecificationFor: C1; fn f(&self, x: [u8; 3]); }
        #[verifier::external_trait_specification]
        pub trait ExC2 { type ExternalTraitSpecificationFor: C2; fn f(&self, x: [u16; 2]); }
        #[verifier::external_trait_specification]
        pub trait ExD1 { type ExternalTraitSpecificationFor: D1; fn f(&self, x: Result<u8, u8>); }
        #[verifier::external_trait_specification]
        pub trait ExD2 { type ExternalTraitSpecificationFor: D2; fn f(&self, x: Option<u16>); }
        #[verifier::external_trait_specification]
        pub trait ExE { type ExternalTraitSpecificationFor: E; fn f(&self, x: *const u8, y: [u8; 2]); }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["assume_specification requires function type signature to match `test_crate::A1::f` exactly ", "assume_specification requires function type signature to match `test_crate::A2::f` exactly ", "assume_specification requires function type signature to match `test_crate::B1::f` exactly ", "assume_specification requires function type signature to match `test_crate::B2::f` exactly ", "assume_specification requires function type signature to match `test_crate::C1::f` exactly ", "assume_specification requires function type signature to match `test_crate::C2::f` exactly ", "assume_specification requires function type signature to match `test_crate::D1::f` exactly ", "assume_specification requires function type signature to match `test_crate::D2::f` exactly "])
}

// Covers rust_to_vir_func.rs:533
test_verify_one_file! {
    #[test] r2_traits_ext_spec_mismatch_multi code! {
        use vstd::prelude::*;
        pub trait T1 { fn f(&self, x: &u8) -> u8; }
        pub trait T2 { fn f(&self, x: &u8) -> u8; }
        verus! {
        #[verifier::external_trait_specification]
        pub trait ExT1 {
            type ExternalTraitSpecificationFor: T1;
            fn f(&self, x: &mut u8) -> u8;
        }
        #[verifier::external_trait_specification]
        pub trait ExT2 {
            type ExternalTraitSpecificationFor: T2;
            fn f(&self, x: &u16) -> u8;
        }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["assume_specification requires function type signature to match `test_crate::T1::f` exactly ", "assume_specification requires function type signature to match `test_crate::T2::f` exactly "])
}

// Covers rust_to_vir_func.rs:3541
test_verify_one_file! {
    #[test] r2_traits_fn_attr_combos verus_code! {
        use vstd::prelude::*;

        #[verifier::nonlinear]
        #[verifier::spinoff_prover]
        proof fn nl_spin(x: int) ensures x * x >= 0 {} // FAILS

        #[verifier::nonlinear]
        proof fn nl_only(x: int, y: int) requires x > 0, y > 0 ensures x * y > 0 {}

        pub mod m {
            use vstd::prelude::*;
            pub open(crate) spec fn g() -> int { 1 }
            pub closed spec fn h() -> int { // FAILS
                #[verus::internal(open_visibility_qualifier)]
                pub(in crate) use crate as _;
                2
            }
        }

        #[verifier::nonlinear]
        #[verifier::spinoff_prover]
        pub const NL_SPIN: u8 = 1; // FAILS
        #[verifier::nonlinear]
        pub const NL_ONLY: u8 = 2;
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["#[verifier::spinoff_prover] is implied for assert by nonlinear_arith".to_string(), "#[verifier::spinoff_prover] is implied for assert by nonlinear_arith".to_string(), "verus internal error: found 'open_visibility_qualifier' declaration but no 'publish' attribute".to_string()]);
        assert_fails(err.clone(), 3);
    }
}

// Covers rust_to_vir_func.rs:1758
test_verify_one_file_with_options! {
    #[test] t1_ctl_t1_ctl_4 ["no-auto-import-verus_builtin", "vstd"] => code! {
        #![feature(type_alias_impl_trait)]
        use vstd::prelude::*;
        pub type Op = impl Copy;
        #[define_opaque(Op)]
        pub fn mk_op() -> Op { 0u8 }
        verus! {
        pub trait Marker {}
        impl Marker for u64 {}

        pub fn f(n: u64) -> u64
        {
            decreases_by(f_dec);
            0u64
        }

        proof fn f_dec(n: u64) -> Op
            decreases n,
        {
            arbitrary()
        }

        } // verus!
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: opaque type")
}

// Covers rust_to_vir_func.rs:2342
test_verify_one_file! {
    #[test] t1h_ctl_t1_ctl_30 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::assume_termination]
        fn f(n: u64) -> u64
            decreases n
        {
            decreases_by(f_dec);
            if n > 0 { f(n - 1); }
            0u64
        }

        spec fn f_dec(n: u64) -> u64
            requires n < 100,
            ensures true,
            decreases n,
        {
            0u64
        }
    } => Err(err) => assert_vir_error_msg(err, "spec functions cannot have requires/ensures")
}

// Covers external.rs:342
test_verify_one_file! {
    #[test] w_refutable_proof_rs verus_code! {
        use vstd::prelude::*;

        proof fn p(tracked o: Option<int>) { let tracked Some(x) = o; }
    } => Err(err) => assert_rust_error_msg(err, "refutable pattern in local binding")
}
