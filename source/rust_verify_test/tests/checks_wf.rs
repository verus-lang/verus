// Tests for well-formedness, termination, trait and Safe API checks.
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers traits.rs:166
test_verify_one_file! {
    #[test] expr_072_ghost_rawptr_lt_macro code! {
        use vstd::prelude::*;
        macro_rules! bin { ($a:expr, $op:tt, $b:expr) => { ($a $op $b) } }
        macro_rules! cast { ($e:expr, $t:ty) => { ($e as $t) } }
        verus! {
        spec fn f(p: *const u8, q: *const u8) -> bool { bin!(p, <, q) }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `core::cmp::PartialOrd::lt` with mode exec")
}

// Covers well_formed.rs:695, 696, 698
test_verify_one_file! {
    #[test] final_all_t2_t2_all_44 code! {
        use vstd::prelude::*;
        verus! {
        fn g(x: &mut u8) {}
        fn h0(y: u8) -> u8 { y }
        const fn gc(x: &mut [u8; 0]) {}
        const fn hc(y: u8) -> u8 { y }
        const fn mk0() -> &'static mut [u8; 0] { &mut [] }
        pub uninterp spec fn spec_mk() -> &'static mut [u8; 0];
        #[verifier::when_used_as_spec(spec_mk)]
        pub const fn mk() -> &'static mut [u8; 0] { &mut [] }

        spec const C: u8 = {
            proof { let r: &mut [u8; 0] = mk(); }
            0
        };
        } // verus!
        fn main() { println!("ok"); }
    } => Err(err) => assert_vir_error_msg(err, "proof blocks inside spec code is currently supported only for spec functions with decreases")
}

// Covers well_formed.rs:766
test_verify_one_file! {
    #[test] final_all_t3_t3_all_14 verus_code! {
        use vstd::prelude::*;

        spec fn s(x: &mut u8) -> bool { *old(x) == 0u8 }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless in spec functions")
}

// Covers well_formed.rs:749, 2180
test_verify_one_file! {
    #[test] final_all_t4_t4_all_90 verus_code! {
        use vstd::prelude::*;

        spec fn s(r: &mut Option<u8>, c: bool) -> bool {
            match r { ref mut y @ Some(_) if c => true, _ => false }
        }
    } => Err(err) => assert_vir_error_msg(err, "Not supported: match arm containing both a match-guard and a binding by mutable reference")
}

// Covers well_formed.rs:706
test_verify_one_file! {
    #[test] final_all_t5_t5_all_9 verus_code! {
        use vstd::prelude::*;

        spec const C: u64 = { ::verus_builtin::ensures(|r: u64| [r == 5]); 5 };
    } => Err(err) => assert_vir_error_msg(err, "This verus_builtin header should go at the beginning of the function body or a loop body (this is")
}

// Covers well_formed.rs:660, 661
test_verify_one_file! {
    #[test] final_all_t6_t6_all_12 verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        spec fn f(n: nat) -> nat {
            n + 1
        }

        proof fn p() {
            reveal_with_fuel(f, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal_with_fuel statements require a spec function with a decreases clause")
}

// Covers well_formed.rs:652
test_verify_one_file! {
    #[test] final_all_t6_t6_all_14 verus_code! {
        use vstd::prelude::*;

        fn f(n: u64) {
        }

        proof fn p() {
            reveal_with_fuel(f, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function, got exec-mode function")
}

// Covers well_formed.rs:645
test_verify_one_file! {
    #[test] final_all_t6_t6_all_18 verus_code! {
        use vstd::prelude::*;

        proof fn f(n: nat) {
        }

        proof fn p() {
            broadcast use f;
        }
    } => Err(err) => assert_vir_error_msg(err, "`broadcast use` statements require a broadcast proof fn")
}

// Covers well_formed.rs:194, 225
test_verify_one_file! {
    #[test] final_b859_alloc_rc_lifetime_only_control code! {
        use vstd::prelude::*;
        pub mod rc { pub struct Rc<'a> { pub v: &'a u8 } }
        verus! {
        fn get<'a>(r: rc::Rc<'a>) -> (x: u8) ensures x == *r.v { *r.v }
        }
        fn main() { let b = 7u8; let r = rc::Rc { v: &b }; assert!(get(r) == 7); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type `test_crate::rc::Rc` which is ignored because it is either declared outside the")
}

// Covers traits.rs:750, 757
test_verify_one_file! {
    #[test] funcs_trait_default_calls_impl verus_code! {
        use vstd::prelude::*;

        pub trait U { fn u(&self) -> u8; }
        pub trait T {
            fn a(&self) -> (r: u8) ensures r < 10;
            fn c<V: T + U>(&self, v: &V) -> (r: u8) ensures r < 10;
            fn b(&self) -> (r: u8) ensures r < 10 { let x = self.c(&S); x }
        }
        pub struct S;
        impl U for S { fn u(&self) -> u8 { 3 } }
        impl T for S {
            fn a(&self) -> (r: u8) { 1 }
            fn c<V: T + U>(&self, v: &V) -> (r: u8) { v.a() }
        }
        fn test() { let s = S; let x = s.b(); assert(x < 10); }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

// Covers traits.rs:49
test_verify_one_file! {
    #[test] funcs_trait_ext_spec_missing_method code! {
        use vstd::prelude::*;
        pub trait Ext { fn req(&self) -> u8; fn dflt(&self) -> u8 { 7 } fn other(&self) -> u8 { 9 } }
        verus! {
        pub struct S;
        }
        impl Ext for S { fn req(&self) -> u8 { 1 } }
        verus! {
        #[verifier::external_trait_specification]
        pub trait ExExt {
            type ExternalTraitSpecificationFor: Ext;
            fn req(&self) -> u8;
            fn dflt(&self) -> (r: u8) ensures r == 7;
        }
        fn test(s: &S) {
            let x = s.dflt();
            assert(x == 7);
            let y = s.req(); let z = s.other();
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "`test_crate::impl&%0%default%other` is not supported (note: you may be able to add a Verus")
}

// Covers well_formed.rs:1066, 1067
test_verify_one_file! {
    #[test] lean_pilot_g48_t1 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        pub proof fn f(n: nat) -> nat
        {
            decreases_by(f_dec);
            0nat
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat)
            decreases n,
        {
        }
    } => Err(err) => assert_vir_error_msgs(err, &["only spec functions can use decreases_by/recommends_by", "decreases_by/recommends_by function cannot have its own decreases clause"])
}

// Covers well_formed.rs:1737
test_verify_one_file! {
    #[test] lean_pilot_g78_t1miss verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        pub fn f(n: u64) -> impl Marker
        {
            decreases_by(f_dec);
            0u64
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: u64)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Covers recursion.rs:364, 365, 455
test_verify_one_file! {
    #[test] lean_pilot_programs_v2_h162_t3 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        fn f(n: u64) -> u64
        {
            if n > 0 { f(n - 1); }
            0u64
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

// Covers well_formed.rs:1720, 1721
test_verify_one_file! {
    #[test] macros_encoding_sig_bound_const verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f<const N: u8>(g: [u8; 2], n: nat) -> int
            decreases n
        {
            decreases_by(f_dec::<3>);
            if n == 0 { 0 } else { f::<N>(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec<const N: u16>(g: [u8; 2], n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same type bounds")
}

// Covers well_formed.rs:503, 506
test_verify_one_file! {
    #[test] modes_wf_broadcast_zero_args_call verus_code! {
        use vstd::prelude::*;

        spec fn q() -> bool { true }
        broadcast proof fn b() ensures #[trigger] q() {}
        proof fn c() { b(); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call a broadcast_forall function with 0 arguments directly")
}

// Covers well_formed.rs:1185
test_verify_one_file! {
    #[test] modes_wf_bv_integer_ring verus_code! {
        use vstd::prelude::*;

        #[verifier::bit_vector]
        #[verifier::integer_ring]
        proof fn f(x: int) ensures x == x {}
    } => Err(err) => assert_vir_error_msg(err, "Select at most one verifier attribute: integer_ring, non_linear, bit_vector")
}

// Covers well_formed.rs:1184, 1185
test_verify_one_file! {
    #[test] modes_wf_bv_nonlinear verus_code! {
        use vstd::prelude::*;

        #[verifier::bit_vector]
        #[verifier::nonlinear]
        proof fn f(x: u8) ensures x & 0 == 0 {}
    } => Err(err) => assert_vir_error_msg(err, "Select at most one verifier attribute: integer_ring, non_linear, bit_vector")
}

// Covers well_formed.rs:715, 1386
test_verify_one_file! {
    #[test] modes_wf_final_not_deref_proof verus_code! {
        use vstd::prelude::*;

        proof fn p_final(tracked x: &mut u8) ensures final(x) == old(x) {}
    } => Err(err) => assert_vir_error_msg(err, "The result of `final` must be dereferenced (either explicitly, as in `*final(x)`, or implicitly, as")
}

// Covers well_formed.rs:1231, 1232
test_verify_one_file! {
    #[test] modes_wf_integer_ring_no_singular verus_code! {
        use vstd::prelude::*;

        #[verifier::integer_ring]
        proof fn f(x: int) ensures x == x {}
    } => Err(err) => assert_vir_error_msg(err, "Please cargo build with `--features singular` to use integer_ring attribute")
}

// Covers verifier.rs:3349; well_formed.rs:1231
test_verify_one_file_with_options! {
    #[test] modes_wf_integer_ring_no_verify ["--no-verify"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::integer_ring]
        proof fn f(x: int) ensures x == x {}
    } => Ok(err) => {

    }
}

// Covers well_formed.rs:725, 757, 758
test_verify_one_file! {
    #[test] modes_wf_match_last_arm_guard verus_code! {
        use vstd::prelude::*;

        spec fn f(x: u8) -> u8 { match x { 0 => 1, y if y > 3 => 2 } }
    } => Err(err) => assert_vir_error_msg(err, "Not supported: match where the last arm has a match guard (this would necessarily mean the entire")
}

// Covers well_formed.rs:598
test_verify_one_file_with_options! {
    #[test] modes_wf_no_cheating_assert ["--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        proof fn c() { assert(true); }
    } => Ok(())
}

// Covers well_formed.rs:1186, 1187, 1188
test_verify_one_file! {
    #[test] modes_wf_nonlinear_integer_ring verus_code! {
        use vstd::prelude::*;

        #[verifier::nonlinear]
        #[verifier::integer_ring]
        proof fn f(x: int) ensures x == x {}
    } => Err(err) => assert_vir_error_msg(err, "Select at most one verifier attribute: integer_ring, non_linear, bit_vector")
}

// Covers well_formed.rs:634
test_verify_one_file! {
    #[test] modes_wf_reveal_group_fuel2 verus_code! {
        use vstd::prelude::*;

        spec fn f(x: int) -> int decreases x when x >= 0 { if x == 0 { 0 } else { f(x - 1) } }
        pub broadcast group g { lemma_f }
        broadcast proof fn lemma_f(x: int) ensures #[trigger] f(x) == f(x) {}
        proof fn c() { reveal_with_fuel(g, 2); }
    } => Err(err) => assert_vir_error_msg(err, "`test_crate::g` is not supported (note: you may be able to add a Verus specification to this")
}

// Covers well_formed.rs:2178
test_verify_one_file_with_options! {
    #[test] no_cheating_assume ["--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        proof fn p() ensures false { assume(false); }
    } => Err(err) => assert_vir_error_msg(err, "assume/admit not allowed with --no-cheating")
}

// Covers recursive_types.rs:326
test_verify_one_file! {
    #[test] r2_driver_strictly_positive_negative_use verus_code! {
        use vstd::prelude::*;

        #[verifier::strictly_positive]
        pub struct S<A> { pub f: spec_fn(A) -> bool }
        pub struct Bad { pub s: S<Bad> }
    } => Err(err) => assert_vir_error_msg(err, "Type parameter A of test_crate::S must be declared #[verifier::reject_recursive_types] to be used")
}

// Covers well_formed.rs:567, 575, 587
test_verify_one_file! {
    #[test] r2_modes_wf_assert_query_choose_var verus_code! {
        use vstd::prelude::*;

        spec fn id(w: int) -> int { w }
        proof fn p(x: int, y: int) {
            assert(x * y == y * x) by (nonlinear_arith)
                requires x == x
            {
                let z = choose|w: int| #[trigger] id(w) == x;
                let t = choose|a: int, b: int| #[trigger] id(a) == x && #[trigger] id(b) == y;
            }
        }
    } => Ok(())
}

// Covers well_formed.rs:1221
test_verify_one_file! {
    #[test] r2_modes_wf_bitvector_fn_param_dt verus_code! {
        use vstd::prelude::*;

        pub struct S { v: u8 }
        #[verifier::bit_vector]
        proof fn f(s: S)
            ensures s.v & 0 == 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "bit-vector function mode cannot have a datatype other than Integer/Boolean")
}

// Covers well_formed.rs:1204, 1208
test_verify_one_file! {
    #[test] r2_modes_wf_bitvector_fn_shapes verus_code! {
        use vstd::prelude::*;

        #[verifier::bit_vector]
        proof fn f(x: u8)
            ensures x & 0 == 0
        {
            assert(true);
        }
    } => Err(err) => assert_vir_error_msg(err, "bit-vector function mode cannot have a body")
}

// Covers well_formed.rs:386
test_verify_one_file! {
    #[test] r2_modes_wf_open_spec_nonvisible_dt_crate verus_code! {
        use vstd::prelude::*;

        mod a {
            use vstd::prelude::*;
            struct P { pub v: u8 }
            pub(crate) open spec fn f(p: P) -> u8 { p.v }
        }
    } => Err(err) => assert_vir_error_msg(err, "disallowed: field expression for a non-visible datatype")
}

// Covers well_formed.rs:1112, 1113
test_verify_one_file! {
    #[test] r2_modes_wf_param_named_as_ret_async code! {
        use vstd::prelude::*;
        #[verifier::verify]
        async fn f(r: u8) -> u8 {
            ::verus_builtin::ensures(|r: u8| [r == 1u8]);
            r
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter name cannot be the same as the return value name")
}

// Covers well_formed.rs:108, 1110
test_verify_one_file! {
    #[test] r2_traits_dyn_spec_other_receiver_call verus_code! {
        use vstd::prelude::*;

        pub trait Tr2 { spec fn g<Q: ?Sized>(q: &Q) -> bool; }
        impl Tr2 for u8 { open spec fn g<Q: ?Sized>(q: &Q) -> bool { true } }
        pub trait D<T: Tr2> {
            fn m(&self) requires T::g::<Self>(self);
        }
        fn use_dyn(x: &dyn D<u8>) {}
    } => Err(err) => assert_vir_error_msg(err, "Trait is not Verus dyn-compatible: specification of function test_crate::D::m uses Self outside of")
}

// Covers traits.rs:1491
test_verify_one_file! {
    #[test] r2_traits_ext_extension_swapped_params verus_code! {
        use vstd::prelude::*;

        #[verifier::external]
        pub trait T<P> { fn f(&self) -> u8; }

        #[verifier::external_trait_specification]
        #[verifier::external_trait_extension(TSpec via TSpecImpl)]
        pub trait ExT<P> {
            type ExternalTraitSpecificationFor: T<P>;
            fn f(&self) -> u8;
            spec fn s(&self) -> bool;
        }

        pub struct S;
        impl<A, B> T<(A, B)> for S { fn f(&self) -> u8 { 1 } }
        impl<A, B> TSpecImpl<(B, A)> for S { open spec fn s(&self) -> bool { true } }
    } => Err(err) => assert_vir_error_msg(err, "impl for test_crate::TSpec must have a matching impl for test_crate::T, with the same type")
}

// Covers recursion.rs:564
test_verify_one_file! {
    #[test] r2_traits_ext_spec_where_typeq code! {
        use vstd::prelude::*;
        pub trait Other { type X; }
        pub trait T {
            type X;
            type Y;
            fn f(&self);
            fn g(&self);
            fn h<B: T>(&self);
            fn k(&self);
        }
        verus! {
        #[verifier::external_trait_specification]
        pub trait ExOther {
            type ExternalTraitSpecificationFor: Other;
            type X;
        }
        #[verifier::external_trait_specification]
        pub trait ExT {
            type ExternalTraitSpecificationFor: T;
            type X;
            type Y;
            fn f(&self) where Self: T<X = u8>;
            fn g(&self) where Self: T<X = <Self as ExT>::Y>;
            fn h<B: T + ExT>(&self) where Self: T<X = <B as ExT>::X>;
            fn k(&self) where Self: T<X = <Self as Other>::X>, Self: Other;
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

// Covers traits.rs:1202
test_verify_one_file! {
    #[test] r2_traits_impl_trigger_typeq_chain verus_code! {
        use vstd::prelude::*;

        pub trait It { type Item; }
        pub trait Tr<X, Y> {
            spec fn f<M>(&self) -> bool where Y: It<Item = M>;
        }
        pub struct S;
        impl<A, B, C> Tr<A, C> for S where A: It<Item = B>, B: It<Item = C> {
            open spec fn f<M>(&self) -> bool where C: It<Item = M> { true }
        }
        proof fn test() {}
    } => Ok(())
}

// Covers recursion.rs:515, 635, 636, 652; recursive_types.rs:605
test_verify_one_file! {
    #[test] r3_vir_b_rtypes_fndef_cycle_through_trait_impl verus_code! {
        use vstd::prelude::*;

        pub trait Tr { spec fn q() -> bool; }
        pub struct S;
        impl Tr for S {
            open spec fn q() -> bool { !call_requires(test, (0u8,)) }
        }
        pub open spec fn g<T: Tr>() -> bool { T::q() }
        pub fn test(x: u8)
            requires g::<S>(),
        {}
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

// Covers safe_api.rs:54, 155
test_verify_one_file_with_options! {
    #[test] r3_vir_b_safe_api_trait_impl_shapes ["--output-json", "-V check-api-safety"] => code! {
        use vstd::prelude::*;
        verus! {
        pub trait PubT {
            spec fn sp(&self) -> int;
            proof fn pf(&self);
            fn pubm(&self) -> (r: u8);
        }
        trait PrivT {
            fn privm(&self, x: u8) -> (r: u8) requires x > 0 ensures r == x;
        }
        pub struct S;
        impl PubT for S {
            open spec fn sp(&self) -> int { 1 }
            proof fn pf(&self) {}
            fn pubm(&self) -> (r: u8) { 1 }
        }
        impl PrivT for S {
            fn privm(&self, x: u8) -> (r: u8) { x }
        }
        }
        fn main() {
            let a = S.pubm();
            let b = S.privm(3);
            assert!(a == 1 && b == 3);
            println!("S.pubm()={} S.privm(3)={}", a, b);
        }
    } => Ok(err) => {
        assert_eq!(err.json_output.as_ref().unwrap()["verification-results"]["verified"], 5);
    }
}

// Covers well_formed.rs:1078, 1079
test_verify_one_file! {
    #[test] t1_reach_t1_reach_68 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::assume_termination]
        pub proof fn f(n: nat) -> nat
        {
            decreases_by(f_dec);
            0nat
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat) -> nat
            ensures true,
        {
            0nat
        }
    } => Err(err) => assert_vir_error_msgs(err, &["only spec functions can use decreases_by/recommends_by", "decreases_by/recommends_by function cannot have ensures clauses"])
}

// Covers well_formed.rs:1057, 1058, 1060
test_verify_one_file_with_options! {
    #[test] t1_reach_t1_reach_74 ["no-auto-import-verus_builtin", "vstd"] => code! {
        #![feature(impl_trait_in_assoc_type)]
        use vstd::prelude::*;
        pub trait Tr { type O; fn mk() -> Self::O; }
        pub struct S;
        impl Tr for S { type O = impl Copy; fn mk() -> Self::O { 0u8 } }
        verus! {
        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        spec fn f(n: nat) -> nat
            decreases n
        {
            decreases_by(f_dec);
            0nat
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat) -> <S as Tr>::O
            decreases n,
        {
            arbitrary()
        }

        } // verus!
    } => Err(err) => assert_vir_error_msg(err, "Opaque type is not supported in proof mode")
}

// Covers well_formed.rs:1090, 1091
test_verify_one_file! {
    #[test] t1_reach_t1_reach_95 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::assume_termination]
        pub proof fn f(n: nat) -> u64
        {
            decreases_by(f_dec);
            0u64
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat) -> nat
        {
            0nat
        }
    } => Err(err) => assert_vir_error_msgs(err, &["only spec functions can use decreases_by/recommends_by", "decreases_by/recommends_by function cannot have a return value"])
}

// Covers well_formed.rs:1072, 1073
test_verify_one_file! {
    #[test] t1_reach_t1_reach_97 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        #[verifier::exec_allows_no_decreases_clause]
        spec fn f(n: nat)
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { () } else { f((n - 1) as nat) }
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat) -> nat
            requires n < 100,
        {
            0nat
        }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function cannot have requires clauses (use decreases_when in the spec")
}

// Covers well_formed.rs:1925
test_verify_one_file! {
    #[test] t1h_ctl_t1_ctl_70 verus_code! {
        use vstd::prelude::*;

        pub trait Marker {}
        impl Marker for u64 {}

        fn f(n: u64) -> impl Marker
            decreases n
        {
            decreases_by(f_dec);
            0u64
        }

        fn f_dec(n: u64) -> u64
            decreases n,
        {
            0u64
        }
    } => Err(err) => assert_vir_error_msg(err, "proof function must be marked #[verifier::decreases_by] or #[verifier::recommends_by] to be used as")
}

// Covers recursion.rs:94
test_verify_one_file! {
    #[test] w_m_height_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f(x: int) { let b = is_smaller_than(x, if pf() { x } else { x }); }
    } => Ok(())
}

// Covers well_formed.rs:1372, 1546, 1548
test_verify_one_file! {
    #[test] w_private_in_requires_rs verus_code! {
        use vstd::prelude::*;

        mod m {
            use vstd::prelude::*;
            spec fn q() -> bool { true }
            pub fn g() requires q() {}
            pub open spec fn h() -> bool { q() }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["in 'requires' clause of public function, cannot refer to private function", "in pub open spec function, cannot refer to private function"])
}

// Covers recursion.rs:79, 129, 398
test_verify_one_file_with_options! {
    #[test] w_rec_equal_rs ["--output-json"] => verus_code! {
        use vstd::prelude::*;

        spec fn e(n: nat) -> nat decreases n { if n == 0 { 0 } else { e(n) } } // FAILS
        /* FAILS */ spec fn e2(n: nat, m: nat) -> nat decreases n, m { if n == 0 { 0 } else { e2(n, m) } }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["could not prove termination".to_string(), "could not prove termination".to_string()]);
        assert_fails(err.clone(), 2);
        assert_eq!(err.json_output.as_ref().unwrap()["verification-results"]["verified"], 0);
    }
}

// Covers safe_api.rs:35
test_verify_one_file_with_options! {
    #[test] w_sa_requires_rs ["-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;

        pub fn f(x: u32) requires x > 0 {}
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial for function `test_crate::f`. Unverified, safe")
}

// Covers safe_api.rs:154
test_verify_one_file_with_options! {
    #[test] w_sa_trait_ens_rs ["-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;

        /* FAILS */ pub trait T2 { fn m2(&self) -> (r: u32) ensures r > 0; }
    } => Err(err) => assert_one_fails(err)
}

// Covers safe_api.rs:51, 54
test_verify_one_file_with_options! {
    #[test] w_sa_trait_impl_req_rs ["-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;

        pub trait T { fn m(&self, x: u32) requires x > 0; }
        pub struct S;
        impl T for S { fn m(&self, x: u32) {} }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial for function `test_crate::S::m`. Unverified,")
}

// Covers safe_api.rs:82
test_verify_one_file_with_options! {
    #[test] w_sa_trait_inv_rs ["-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;

        pub trait T4 { fn m4(&self) opens_invariants none; }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'invariant' clause is nontrivial for trait function `test_crate::T4::m4`.")
}

// Covers safe_api.rs:71
test_verify_one_file_with_options! {
    #[test] w_sa_trait_unwind_rs ["-V check-api-safety"] => verus_code! {
        use vstd::prelude::*;

        pub trait T3 { fn m3(&self) no_unwind; }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'unwind' clause is nontrivial for trait function `test_crate::T3::m3`.")
}
