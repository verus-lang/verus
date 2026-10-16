// Tests for the verus! macro (builtin_macros/src/syntax.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers syntax.rs:499
test_verify_one_file! {
    #[test] macros_encoding_syn_args_tuple_struct verus_code! {
        use vstd::prelude::*;

        pub struct W(pub u8);
        impl View for W {
            type V = int;
            closed spec fn view(&self) -> int { 99 }
        }
        pub struct P(pub u8, pub u8);
        fn f(W(x): W) -> (r: u8)
            ensures r == 1
        {
            1
        }
        proof fn g(W(x): W)
            ensures x == 99
        {
        }
        fn h(P(a, b): P) -> (r: u8) ensures r == a { a } // FAILS
        fn k(Ghost(x): Ghost<int>, Tracked(t): Tracked<int>) {}
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["verus! macro error: input of the function is not an Ident".to_string()]);
        assert_fails(err.clone(), 1);
    }
}

// Covers syntax.rs:1332, 1333
test_verify_one_file! {
    #[test] macros_encoding_syn_axiom_in_trait verus_code! {
        use vstd::prelude::*;

        trait T {
            axiom fn ax(x: int) ensures x == x;
            proof fn lem(x: int) ensures x == x;
        }
        axiom fn top_ax(x: int) ensures x + 0 == x;
    } => Err(err) => assert_vir_error_msg(err, "`axiom` keyword unexpected in trait declarations")
}

// Covers syntax.rs:1309, 1312
test_verify_one_file! {
    #[test] macros_encoding_syn_broadcast_exec verus_code! {
        use vstd::prelude::*;

        broadcast spec fn f(x: int) -> bool { x > 0 }
    } => Err(err) => assert_vir_error_msg(err, "only `proof` functions can be marked `broadcast`")
}

// Covers syntax.rs:2588, 2590, 3593, 3595
test_verify_one_file! {
    #[test] macros_encoding_syn_closure_req_ens verus_code! {
        use vstd::prelude::*;

        spec fn g1() -> spec_fn(int) -> int { |x: int| requires x > 0 { x } }
        spec fn g2() -> spec_fn(int) -> int { |x: int| ensures true { x } }
        spec fn q1() -> bool { forall|x: int| requires x > 0 { x > 0 } }
        spec fn q2() -> bool { forall|x: int| ensures true { x == x } }
        spec fn ok() -> spec_fn(int) -> int { |x: int| x }
    } => Err(err) => assert_vir_error_msgs(err, &["ghost closures cannot have requires/ensures", "ghost closures cannot have requires/ensures", "quantifiers cannot have requires/ensures", "quantifiers cannot have requires/ensures"])
}

// Covers syntax.rs:5206, 5210
test_verify_one_file! {
    #[test] macros_encoding_syn_explicit_exprs code! {
        use vstd::prelude::*;
        macro_rules! m {
            (@ $a:expr, $b:expr) => { ::verus_builtin::assert_(::verus_builtin::equal($a, $b)) };
            ($a:expr, $b:expr) => { ::verus_builtin::assert_(::verus_builtin::equal($a, $b)) };
        }
        verus! {
        proof fn p(x: int) {
            verus_proof_macro_explicit_exprs!(m!(@@ x + 1, @@ 1 + x));
            verus_proof_macro_explicit_exprs!(m!(@ (x), @@ x));
        }
        }
    } => Ok(_) => ()
}

// Covers syntax.rs:3222
test_verify_one_file! {
    #[test] macros_encoding_syn_float_lit_type verus_code! {
        use vstd::prelude::*;

        spec fn g(a: [u8; 2.5f64 as usize]) -> int { 1 }
        spec fn h(a: [u8; 2.5 as usize]) -> int { 1 }
    } => Ok(())
}

// Covers syntax.rs:4463
test_verify_one_file! {
    #[test] macros_encoding_syn_for_in_type verus_code! {
        use vstd::prelude::*;

        fn f() {
            let a: [u8; { for i in 0..1usize {} 3 }] = [0u8; 3];
        }
    } => Err(err) => assert_rust_error_msg(err, "calling non-const function `std::iter::range::<impl std::iter::Iterator for")
}

// Covers syntax.rs:2000
test_verify_one_file! {
    #[test] macros_encoding_syn_global_attrs_names verus_code! {
        use vstd::prelude::*;

        struct my_t(u8);
        struct Q<A>(A);
        #[verifier::external_body]
        #[verus::internal(x)]
        #[allow(dead_code)]
        global size_of my_t == 1;
        global size_of Q<u16> == 2;
        global size_of [u8; 4] == 4;
    } => Err(err) => assert_vir_error_msg(err, "this type name is not supported (it must only include A-Za-z0-9<>)")
}

// Covers ast_to_sst.rs:1162, 2731; modes.rs:1084, 1366, 3886; sst_to_air.rs:1927, 2494, 2785; syntax.rs:3921, 3925, 3930, 4047, 4048, 4049, 4057, 4058, 4059, 4060
test_verify_one_file_with_options! {
    #[test] macros_encoding_syn_loop_attrs ["--output-json"] => verus_code! {
        use vstd::prelude::*;

        fn f() {
            let mut s: u32 = 0;
            #[rustfmt::skip]
            #[verifier::loop_isolation(true)]
            #[allow(unused_variables)]
            #[verifier::no_auto_loop_invariant]
            for i in 0..10u32
                invariant s <= i * 10, i <= 10,
            {
                s = s + i;
            }
            #[verifier::no_loop_invariant] // FAILS
            for j in 0..3u32 {
            }
            let mut k: u32 = 0;
            while k < 5
                invariant k <= 5,
                invariant_ensures k <= 5,
                ensures k == 5,
                decreases 5 - k,
            {
                k = k + 1;
            }
            let mut m: u32 = 0;
            while m < 5
                invariant
                invariant_ensures m <= 5,
                ensures m == 5,
                decreases 5 - m,
            {
                m = m + 1;
            }
        }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["precondition not satisfied".to_string()]);
        assert_fails(err.clone(), 1);
        assert_eq!(err.json_output.as_ref().unwrap()["verification-results"]["verified"], 4);
    }
}

// Covers syntax.rs:1581, 1639
test_verify_one_file! {
    #[test] macros_encoding_syn_pat_ref_subpat verus_code! {
        use vstd::prelude::*;

        fn e1(t: Tracked<int>, g: Ghost<int>) {
            let Tracked(ref a) = t;
            let Ghost(b @ _) = g;
            let ghost ref c = 5int;
            let tracked d @ _ = 6int;
        }
    } => Err(err) => assert_rust_error_msgs(err, &["expected tuple struct or tuple variant, found struct `Tracked`", "expected tuple struct or tuple variant, found struct `Ghost`"])
}

// Covers syntax.rs:414, 415, 416, 417, 3601, 3604, 3611, 3612, 3636, 3637, 3714
test_verify_one_file! {
    #[test] macros_encoding_syn_proof_fn_modes verus_code! {
        use vstd::prelude::*;

        struct S;
        fn e1() {
            let f = proof_fn|x: u8| -> u8 { x }; // FAILS
        }
        fn e2() {
            let f = |x: u8| -> (tracked r: u8) { x }; // FAILS
        }
        proof fn p1() {
            let tracked f = proof_fn[ReqEns<S>]|x: u8| -> u8 requires x > 0 { x }; // FAILS
        }
        proof fn p2() {
            let tracked f = proof_fn[ReqEns<S>]|x: u8| -> (r: u8) ensures r == x { x }; // FAILS
        }
        proof fn p3() {
            let tracked f = proof_fn[ReqEns<S>]|x: u8| -> u8 { x };
            let tracked g = proof_fn|x: u8| -> u8 requires x > 0 { x };
        }
    } => Err(err) => {
        let mut msgs: Vec<String> = err.errors.iter().map(|e| e.message.clone()).collect();
        msgs.sort();
        assert_eq!(msgs, vec!["'tracked' not supported here".to_string(), "ReqEns and requires/ensures cannot be used together".to_string(), "ReqEns and requires/ensures cannot be used together".to_string(), "proof_fn closures are only allowed in proof mode".to_string()]);
        assert_fails(err.clone(), 4);
    }
}

// Covers syntax.rs:416, 417
test_verify_one_file! {
    #[test] macros_encoding_syn_reqens_opts verus_code! {
        use vstd::prelude::*;

        struct S;
        proof fn p1() {
            let tracked a = proof_fn[ReqEns<S>, ReqEns<S>]|x: u8| -> u8 { x };
        }
        proof fn p2() {
            let tracked b = proof_fn[ReqEns::<S>]|x: u8| -> u8 { x };
        }
        proof fn p3() {
            let tracked c = proof_fn[ReqEns<S, S>]|x: u8| -> u8 { x };
        }
        proof fn p4() {
            let tracked d = proof_fn[ReqEns<'static>]|x: u8| -> u8 { x };
        }
    } => Err(err) => assert_vir_error_msgs(err, &["unexpected option ReqEns", "unexpected option ReqEns", "unexpected option ReqEns", "unexpected option ReqEns"])
}

// Covers syntax.rs:3442
test_verify_one_file! {
    #[test] macros_encoding_syn_reveal_self verus_code! {
        use vstd::prelude::*;

        struct S;
        impl S {
            closed spec fn f() -> int { 1 }
            proof fn p() ensures Self::f() == 1 { reveal(Self::f); }
        }
    } => Err(err) => assert_vir_error_msg(err, "Self is not supported in reveal/hide, use the type name instead, or <T as X> for functions in trait")
}

// Covers syntax.rs:1733
test_verify_one_file! {
    #[test] propose_1_17638 verus_code! {
        use vstd::prelude::*;

        proof fn p() {
            let Ghost(y) = Ghost(5int);
            assert(y == 5);
        }
    } => Ok(())
}

// Covers syntax.rs:3636
test_verify_one_file! {
    #[test] propose_1_18505 verus_code! {
        use vstd::prelude::*;

        struct S;
        impl ProofFnReqEnsDef<(u8,), u8> for S {
            open spec fn req(a: (u8,)) -> bool { true }
            open spec fn ens(a: (u8,), o: u8) -> bool { true }
        }
        proof fn p() {
            let tracked f = proof_fn[ReqEns<S>]|x: u8| -> u8 { x };
        }
    } => Ok(())
}

// Covers syntax.rs:1708
test_verify_one_file! {
    #[test] propose_2_17612_ghost_let_unvisited verus_code! {
        use vstd::prelude::*;

        fn f() {
            let ghost x: int = 5;
            assert(x == 5);
        }
    } => Ok(())
}

// Covers syntax.rs:5708
test_verify_one_file! {
    #[test] propose_2_19468_generic_args_dropped verus_code! {
        use vstd::prelude::*;

        fn g<T: Default>(x: u8) -> (r: u8)
            ensures r == x
        {
            x
        }
    } => Ok(())
}

// Covers syntax.rs:1544
test_verify_one_file! {
    #[test] r2_traits_p_trait_impl_spec_const verus_code! {
        use vstd::prelude::*;

        pub trait Tr { const C: u8; }
        pub struct S1;

        impl Tr for S1 { spec const C: u8 = 1; }
        fn test() -> (r: u8) ensures r == 1 { S1::C }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: non-default mode on associated const")
}
