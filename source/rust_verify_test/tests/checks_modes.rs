// Tests for mode checking (vir/src/modes.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers modes.rs:483
test_verify_one_file! {
    #[test] expr_003_ghost_mut_array_unsize verus_code! {
        use vstd::prelude::*;

        proof fn q(tracked s: &mut [u8]) {}
        proof fn p(tracked a: &mut [u8; 3]) { q(a); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `vstd::array::ref_mut_array_unsizing_coercion` with mode exec")
}

// Covers modes.rs:2826
test_verify_one_file! {
    #[test] expr_011_ghost_while_let verus_code! {
        use vstd::prelude::*;

        proof fn p(o: Option<nat>) {
            let mut x = o;
            while let Some(n) = x
                decreases (if x is Some { 1int } else { 0int }),
            {
                x = None;
            }
            assert(x is None);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof or spec mode")
}

// Covers modes.rs:2990, 3474
test_verify_one_file! {
    #[test] expr_014_await_in_proof_block verus_code! {
        use vstd::prelude::*;

        async fn g() -> u8 { 3 }
        async fn f() {
            let x = g().await;
            proof { let tracked y = g().await; }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot await in non-exec code")
}

// Covers modes.rs:631, 635, 742, 3015
test_verify_one_file! {
    #[test] expr_036_macro_ops_in_requires_invariant_const code! {
        use vstd::prelude::*;
        macro_rules! cast { ($e:expr, $t:ty) => { ($e as $t) } }
        macro_rules! bin { ($a:expr, $op:tt, $b:expr) => { ($a $op $b) } }
        verus! {
        fn first_item() {}
        #[derive(Clone, Copy)]
        #[repr(u8)]
        pub enum E { A = 3, B = 200 }
        spec const SC: u8 = cast!(E::B, u8);
        fn f(x: u16, e: E, b: bool) -> (r: u8)
            requires bin!(x, <, 256u16), bin!(b, &, true),
            ensures bin!(r, ==, cast!(x, u8)), cast!(e, u8) == cast!(e, u8),
        {
            let ghost g: u8 = cast!(e, u8);
            let mut i: u8 = 0;
            while i < 3
                invariant bin!(i, <=, 3u8), bin!(cast!(b, u8), ==, 1u8),
                decreases 3 - i,
            {
                i = i + 1;
            }
            assert(bin!(SC, ==, 200u8)) by { assert(cast!(E::B, u8) == 200); }
            let t: Ghost<u8> = Ghost((x as u8));
            proof { let h: u8 = bin!(t.view(), ^, 0u8); }
            x as u8
        }
        }
    } => Ok(_) => ()
}

// Covers modes.rs:3306
test_verify_one_file! {
    #[test] final_all_t2_t2_all_35 code! {
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

        exec const C: &'static mut [u8; 0] = {
            #[verifier::ghost_block_wrapped] { mk() }
        };
        } // verus!
        fn main() { println!("{}", C.len()); }
    } => Err(err) => assert_vir_error_msg(err, "cannot take mutable borrow of ghost-mode place")
}

// Covers modes.rs:1266, 1268, 3466
test_verify_one_file! {
    #[test] final_all_t3_t3_all_5 code! {
        use vstd::prelude::*;
        verus! {
        fn f(x: &mut u8, y: u64) {
            let b = *old(x) == 0u8 || true;
        }
        } // verus!
        fn main() { let mut a = 0u8; f(&mut a, 3); println!("{}", a); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use spec-mode expression in executable context")
}

// Covers modes.rs:913, 947
test_verify_one_file! {
    #[test] final_all_t4_t4_all_6 verus_code! {
        use vstd::prelude::*;

        spec fn s(r: &mut Option<u8>, c: bool) -> bool {
            match r { Some(y) => true, _ => false }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is not allowed in spec mode")
}

// Covers modes.rs:921
test_verify_one_file! {
    #[test] final_all_t4_t4_all_60 verus_code! {
        use vstd::prelude::*;

        spec fn s(r: &mut Option<u8>, c: bool) -> bool {
            match r { ref mut y @ Some(_) if true => true, _ => false }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is not allowed in spec mode")
}

// Covers modes.rs:2636, 2637
test_verify_one_file! {
    #[test] modes_e_assert_bv_exec verus_code! {
        use vstd::prelude::*;

        fn e(x: u8) { assert_bitvector_by({ ensures(x & 0 == 0); }); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use assert in exec mode")
}

// Covers modes.rs:2592, 2593
test_verify_one_file! {
    #[test] modes_e_assert_by_exec verus_code! {
        use vstd::prelude::*;

        fn e() { assert_by(true, {}); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use 'assert ... by' in exec mode")
}

// Covers modes.rs:2678, 2679
test_verify_one_file! {
    #[test] modes_e_assert_compute_exec verus_code! {
        use vstd::prelude::*;

        fn e() { assert_by_compute(1 + 1 == 2); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use assert in exec mode")
}

// Covers modes.rs:2584, 2585
test_verify_one_file! {
    #[test] modes_e_assume_exec verus_code! {
        use vstd::prelude::*;

        fn e() { assume_(false); }
    } => Err(err) => assert_vir_error_msg(err, "cannot use assert or assume in exec mode")
}

// Covers modes.rs:1976, 1977
test_verify_one_file! {
    #[test] modes_e_assume_external_in_proof verus_code! {
        use vstd::prelude::*;

        #[verifier::external]
        fn f0() {}
        #[verifier::assume(externals_available_without_declaration)]
        fn g0() {
            proof { f0(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call external function from non-exec mode")
}

// Covers modes.rs:2417, 2418
test_verify_one_file! {
    #[test] modes_e_choose_exec verus_code! {
        use vstd::prelude::*;

        fn e() -> u8 { choose|i: u8| i == 3 }
    } => Err(err) => assert_vir_error_msg(err, "cannot use choose in exec mode")
}

// Covers modes.rs:3864, 3870, 3871
test_verify_one_file! {
    #[test] modes_e_exec_external_body_tracked_ret verus_code! {
        use vstd::prelude::*;

        #[verifier::external_body]
        fn mk() -> (tracked r: bool) { true }
    } => Err(err) => assert_vir_error_msg(err, "because function has no body, return type cannot have mode proof")
}

// Covers modes.rs:2692, 2693, 2694, 2696, 3864, 4091
test_verify_one_file! {
    #[test] modes_e_if_tracked_cond verus_code! {
        use vstd::prelude::*;

        fn mk() -> (tracked r: bool) { true }
        fn e_if() { if mk() { } }
    } => Err(err) => assert_vir_error_msg(err, "condition must have mode exec")
}

// Covers modes.rs:1434, 1435, 1436, 1438
test_verify_one_file! {
    #[test] modes_e_index_tracked_idx verus_code! {
        use vstd::prelude::*;

        fn mk() -> (tracked r: usize) { 0 }
        fn e_index(a: [u8; 2]) -> u8 { a[mk()] }
    } => Err(err) => assert_vir_error_msg(err, "cannot use proof-mode expression in executable context")
}

// Covers modes.rs:2191, 2192
test_verify_one_file! {
    #[test] modes_e_is_variant_exec verus_code! {
        use vstd::prelude::*;

        fn e(o: Option<u8>) -> bool { o is Some }
    } => Err(err) => assert_vir_error_msg(err, "cannot test variant in exec mode")
}

// Covers modes.rs:2743, 2744, 2745, 2747
test_verify_one_file! {
    #[test] modes_e_match_tracked_unit_scrut verus_code! {
        use vstd::prelude::*;

        fn mk() -> (tracked r: ()) { () }
        fn e_match() -> u8 { match mk() { () => 1 } }
    } => Err(err) => assert_vir_error_msg(err, "exec code cannot match on non-exec value")
}

// Covers modes.rs:645, 3354
test_verify_one_file! {
    #[test] modes_e_mut_borrow_proof_in_spec verus_code! {
        use vstd::prelude::*;

        spec fn s(x: nat) -> nat decreases x { proof { let ghost mut a: u8 = 1; let ghost r = &mut a; } x }
    } => Err(err) => assert_vir_error_msg(err, "mutable borrow is not allowed in spec context")
}

// Covers modes.rs:2285, 2286
test_verify_one_file! {
    #[test] modes_e_quant_exec verus_code! {
        use vstd::prelude::*;

        fn e() -> bool { forall|i: int| i == i }
    } => Err(err) => assert_vir_error_msg(err, "cannot use forall/exists in exec mode")
}

// Covers modes.rs:3858
test_verify_one_file! {
    #[test] modes_e_returns_exec_proof_fn verus_code! {
        use vstd::prelude::*;

        #[verifier::returns(exec)]
        proof fn f() -> u8 { 0 }
    } => Err(err) => assert_vir_error_msg(err, "return type cannot have mode exec")
}

// Covers modes.rs:3605, 3606, 3607, 3608, 3610
test_verify_one_file! {
    #[test] modes_e_spec_decl_exec verus_code! {
        use vstd::prelude::*;

        fn f() { #[verifier::spec] let x: u8 = 5; }
    } => Err(err) => assert_vir_error_msg(err, "exec code cannot initialize non-exec variables")
}

// Covers modes.rs:1990
test_verify_one_file! {
    #[test] modes_legacy_assume_external code! {
        use vstd::prelude::*;
        fn f1() -> u8 { 3 }
        #[verifier::verify]
        #[verifier::assume(externals_available_without_declaration)]
        fn g1() -> u8 {
            f1()
        }
    } => Ok(())
}

// Covers modes.rs:1930
test_verify_one_file! {
    #[test] modes_legacy_fnspec_call code! {
        use vstd::prelude::*;
        #[verifier::verify]
        fn f(x: u8, g: Ghost<FnSpec<(u8,), u8>>) {
            assert_((g.view())(x) == (g.view())(x));
        }
    } => Ok(())
}

// Covers modes.rs:2191, 2206, 2285, 2290, 2417, 2584, 2592, 2636, 2678
test_verify_one_file! {
    #[test] modes_legacy_ghost_constructs code! {
        use vstd::prelude::*;
        verus! {
        #[derive(Clone, Copy)]
        pub enum E { A(u8), B }
        pub open spec fn p(i: u8) -> bool { true }
        }
        #[verifier::verify]
        fn l_all(o: E, x: u8) {
            assume_(true);
            assert_(true);
            assert_by(true, {});
            assert_by_compute(true);
            assert_bitvector_by({ ensures(x & 0 == 0); });
            assert_(forall(|i: u8| p(i)));
            assert_(p(0));
            assert_(exists(|i: u8| p(i)));
            assert_(p(choose(|i: u8| p(i))));
            assert_(is_variant(o, "A") || is_variant(o, "B"));
            assert_(imply(is_variant(o, "A"), get_variant_field::<E, u8>(o, "A", "0") == get_variant_field::<E, u8>(o, "A", "0")));
        }
    } => Ok(())
}

// Covers modes.rs:3297
test_verify_one_file! {
    #[test] modes_legacy_return_ok code! {
        use vstd::prelude::*;
        verus! {
        pub spec const C: bool = true;
        }
        #[verifier::verify]
        fn r_exec_exec(b: bool) -> u8 { if b { return 1; } 0 }
        #[verifier::proof]
        fn r_proof(b: bool) -> u8 { if b { return 1; } 0 }
    } => Ok(())
}

// Covers modes.rs:2892
test_verify_one_file! {
    #[test] modes_legacy_return_spec_branch code! {
        use vstd::prelude::*;
        verus! {
        pub spec const C: bool = true;
        }
        #[verifier::verify]
        fn r_exec_proof() -> u8 { if C { return 1; } 0 }
    } => Err(err) => assert_vir_error_msg(err, "cannot return from non-exec code in exec function")
}

// Covers modes.rs:3886, 4092
test_verify_one_file! {
    #[test] modes_legacy_return_spec_fn code! {
        use vstd::prelude::*;
        verus! {
        pub spec const C: bool = true;
        }
        #[verifier::spec]
        fn r_spec(b: bool) -> u8 { if b { return 1; } 0 }
    } => Err(err) => assert_vir_error_msg(err, "return is not allowed in pure context")
}

// Covers modes.rs:2344, 2345
test_verify_one_file! {
    #[test] modes_legacy_spec_cond_exec_closure code! {
        use vstd::prelude::*;
        verus! {
        pub spec const C: bool = true;
        }
        #[verifier::verify]
        fn f() {
            if C { |y: u8| y; }
        }
    } => Err(err) => assert_vir_error_msg(err, "closure in ghost code must be marked as a spec_fn by wrapping it in `closure_to_fn_spec` (this")
}

// Covers ast_to_sst.rs:3083; modes.rs:3128, 3428; prune.rs:523; verifier.rs:958
test_verify_one_file! {
    #[test] modes_proof_fn_open_atomic_update verus_code! {
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub tracked struct Token { state: u16 }
        proof fn p<Pred: UpdatePredicate<Token, Commit<Token>>>(tracked au: AtomicUpdate<Token, Commit<Token>, Pred>) {
            try_open_atomic_update!(au, token => { Tracked(Commit(token)) });
        }
    } => Err(err) => assert_vir_error_msgs(err, &["cannot show atomic postcondition hold at end of block", "atomic update may open invariants that caller cannot"])
}

// Covers modes.rs:296
test_verify_one_file! {
    #[test] propose_1_10 verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        fn t() {
            loop {
                proof { if proph() { break; } }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "break cannot occur in prophecy-conditional context")
}

// Covers modes.rs:298
test_verify_one_file! {
    #[test] propose_1_12 verus_code! {
        use vstd::prelude::*;

        use vstd::atomic::*;
        pub tracked struct Token { state: u16 }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        proof fn p<Pred: UpdatePredicate<Token, Commit<Token>>>(tracked au: AtomicUpdate<Token, Commit<Token>, Pred>) {
            if proph() {
                try_open_atomic_update!(au, token => { Tracked(Commit(token)) });
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "opening an atomic update cannot occur in prophecy-conditional context")
}

// Covers modes.rs:859
test_verify_one_file! {
    #[test] propose_1_130 verus_code! {
        use vstd::prelude::*;

        use vstd::invariant::*;
        #[verifier(atomic)]
        #[verifier(external_body)]
        fn atomic_op() opens_invariants none no_unwind {}
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(i.borrow() => inner => {
                atomic_op();
            });
        }
    } => Ok(())
}

// Covers modes.rs:859
test_verify_one_file! {
    #[test] propose_1_133 verus_code! {
        use vstd::prelude::*;

        use vstd::invariant::*;
        #[verifier(atomic)]
        #[verifier(external_body)]
        fn atomic_op() opens_invariants none no_unwind {}
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(i.borrow() => inner => {
                atomic_op();
            });
        }
    } => Ok(())
}

// Covers modes.rs:300
test_verify_one_file! {
    #[test] propose_1_14 verus_code! {
        use vstd::prelude::*;

        tracked struct Y { ghost y: int }
        tracked struct X { ghost g: int, tracked y: Y }
        uninterp spec fn arbitrary<A>() -> A;
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        proof fn test(tracked y: &Y) {
            if proph() {
                let tracked x = shr_ref_struct_wrap(y, &X { g: 0, y: arbitrary() }, "X", "y");
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`shr_ref_struct_wrap` operator cannot occur in prophecy-conditional context")
}

// Covers modes.rs:945
test_verify_one_file! {
    #[test] propose_1_160 verus_code! {
        use vstd::prelude::*;

        fn f() -> (r: u8) {
            let (a, b) = (1u8, 2u8);
            let c = a + b;
            c
        }
    } => Ok(())
}

// Covers modes.rs:365
test_verify_one_file! {
    #[test] propose_1_25 verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        fn e() {}
        fn t() {
            proof { if proph() { e(); } }
        }
    } => Err(err) => assert_vir_error_msg(err, "call to exec-mode function cannot occur in prophecy-conditional context")
}

// Covers modes.rs:369
test_verify_one_file! {
    #[test] propose_1_31 verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        proof fn q(x: u8) {}
        proof fn p() {
            if proph() { q(3); }
        }
    } => Ok(())
}

// Covers modes.rs:375
test_verify_one_file! {
    #[test] propose_1_38 verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        proof fn q() -> (r: u8) ensures r == 3 { 3 }
        proof fn p() {
            if proph() { let r = q(); }
        }
    } => Ok(())
}

// Covers modes.rs:441
test_verify_one_file! {
    #[test] propose_1_52 verus_code! {
        use vstd::prelude::*;

        proof fn p() {
            let tracked mut x: u8 = 0;
            let g = Ghost(3u8);
            x = 5;
            assert(x == 5);
        }
    } => Ok(())
}

// Covers modes.rs:1945
test_verify_one_file! {
    #[test] propose_1_656 verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        proof fn p() {
            let mut x = false;
            let f: spec_fn(bool) -> bool = |b: bool| b;
            x = f(proph());
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for assignment to non-prophetic location")
}

// Covers modes.rs:2097
test_verify_one_file! {
    #[test] propose_1_734 verus_code! {
        use vstd::prelude::*;

        fn f<const N: usize>() -> (r: usize) {
            N
        }
    } => Ok(())
}

// Covers modes.rs:945
test_verify_one_file! {
    #[test] propose_2_161_tuple_pattern_exec_use verus_code! {
        use vstd::prelude::*;

        fn f(t: (u8, u8)) -> (r: u8)
            ensures r == t.0
        {
            let (a, b) = t;
            a
        }
    } => Ok(())
}

// Covers modes.rs:1913
test_verify_one_file! {
    #[test] propose_2_622_spec_call_prophetic_arg verus_code! {
        use vstd::prelude::*;

        spec fn g(v: u8) -> u8 {
            v
        }

        spec fn sp(r: &mut u8) -> u8 {
            g(*final(r))
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

// Covers modes.rs:1934
test_verify_one_file! {
    #[test] propose_2_648_spec_callee_proof_fn verus_code! {
        use vstd::prelude::*;

        proof fn mk() -> (r: spec_fn(u8) -> bool)
        {
            |x: u8| x == x
        }

        spec fn sp() -> bool {
            mk()(0)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::mk` with mode proof")
}

// Covers modes.rs:2037
test_verify_one_file! {
    #[test] propose_2_707_struct_field_prophetic_spec verus_code! {
        use vstd::prelude::*;

        struct Foo {
            v: u8,
        }

        spec fn sp(r: &mut u8) -> Foo {
            Foo { v: *final(r) }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

// Covers modes.rs:2072
test_verify_one_file! {
    #[test] propose_2_723_struct_update_tail_prophetic verus_code! {
        use vstd::prelude::*;

        struct Foo {
            v: u8,
            w: u8,
        }

        spec fn sp(r: &mut Foo) -> Foo {
            Foo { v: 1, ..*final(r) }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

// Covers modes.rs:2097
test_verify_one_file! {
    #[test] propose_2_735_const_generic_exec_use verus_code! {
        use vstd::prelude::*;

        fn f<const N: usize>() -> (r: usize)
            ensures r == N
        {
            N
        }

        fn main() {
            let x = f::<3>();
            assert(x == 3);
        }
    } => Ok(())
}

// Covers modes.rs:3031, 3042
test_verify_one_file! {
    #[test] r2_modes_m_proof_in_spec_misplaced code! {
        use vstd::prelude::*;
        macro_rules! pis { () => { #[verifier::proof_in_spec] { }; } }
        verus! {
        spec fn f(i: nat) -> nat decreases i {
            proof {
                pis!();
            }
            if i == 0 { 0 } else { f((i - 1) as nat) }
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "already in proof mode")
}

// Covers modes.rs:1144, 1581, 1582, 1615, 1625
test_verify_one_file! {
    #[test] r2_modes_m_proof_write_tuple_with_tracked verus_code! {
        use vstd::prelude::*;

        pub tracked struct Tok {}
        fn set(t: &mut (Tok, u8))
            ensures final(t).1 == 7
        {
            proof { t.1 = 7; }
        }
    } => Ok(())
}

// Covers modes.rs:3306, 3323
test_verify_one_file! {
    #[test] r2_modes_m_reborrow_proof_in_spec verus_code! {
        use vstd::prelude::*;

        pub struct Tok { v: u8 }
        uninterp spec fn arb<A>() -> A;
        proof fn lemma_mut(tracked x: &mut Tok) {
        }
        spec fn f(i: nat) -> nat decreases i {
            proof {
                let ghost r: &mut Tok = arb();
                lemma_mut(r);
            }
            if i == 0 { 0 } else { f((i - 1) as nat) }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

// Covers modes.rs:2880
test_verify_one_file! {
    #[test] r2_modes_m_tracked_swap_exec_places verus_code! {
        use vstd::prelude::*;

        fn f(r: &mut u8, s: &mut u8) {
            proof { vstd::modes::tracked_swap(r, s); }
        }
        fn g(b: bool) {
            proof { if b { return; } }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["cannot mutate exec-mode place in ghost code", "cannot return from non-exec code in exec function"])
}

// Covers modes.rs:3547, 3553
test_verify_one_file! {
    #[test] r3_vir_a_patterns_ghost_let_tuple_refutable verus_code! {
        use vstd::prelude::*;
        use std::convert::Infallible;

        proof fn good(r: Result<int, Infallible>) {
            let (Ok(x), y) = (r, 1int); // FAILS
            assert(y == 1);
            assert(r == Ok::<int, Infallible>(x));
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers modes.rs:670
test_verify_one_file! {
    #[test] s_return_cut_rs verus_code! {
        use vstd::prelude::*;

        fn f(b: bool) -> (r: u32) ensures b ==> r == 1, !b ==> r == 0 {
            if b { return 1; }
            assert(!b);
            0
        }
    } => Ok(())
}

// Covers modes.rs:1893; rust_to_vir_func.rs:2097
test_verify_one_file! {
    #[test] w_block_one_stmt_rs verus_code! {
        use vstd::prelude::*;

        proof fn p() {}
        fn f() -> u32 { let x: u32 = { p(); 5 }; x }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::p` with mode proof")
}

// Covers modes.rs:2617
test_verify_one_file! {
    #[test] w_m_assert_forall_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { assert forall|i: int| g(i) implies (g(i) || pf()) by {} }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2588
test_verify_one_file! {
    #[test] w_m_assert_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { assert(pf()); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2275
test_verify_one_file! {
    #[test] w_m_chained_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f(a: int) { let b = 0 <= a < (if pf() { 1int } else { 2int }); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2318
test_verify_one_file! {
    #[test] w_m_closure_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { let c = |i: int| pf(); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:3816
test_verify_one_file! {
    #[test] w_m_dec_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn r(n: nat) decreases (if pf() { n } else { n }) { if n > 0 { r((n - 1) as nat); } }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:3787
test_verify_one_file! {
    #[test] w_m_ens_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        fn f() ensures pf() {}
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2265
test_verify_one_file! {
    #[test] w_m_exteq_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f(s: Seq<int>) { let b = s =~= (if pf() { s } else { s }); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2297
test_verify_one_file! {
    #[test] w_m_forall_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { let b = forall|i: int| #[trigger] g(i) && pf(); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:3397
test_verify_one_file! {
    #[test] w_m_has_resolved_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { let b = has_resolved(pf()); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2234
test_verify_one_file! {
    #[test] w_m_implies_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { let b = true ==> pf(); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2851
test_verify_one_file! {
    #[test] w_m_inv_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        fn f() { let mut i: u32 = 0; while i < 3 invariant pf(), i <= 3, decreases 3 - i { i = i + 1; } }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2647
test_verify_one_file! {
    #[test] w_m_nl_req_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { assert(true) by (nonlinear_arith) requires pf(); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:3770
test_verify_one_file! {
    #[test] w_m_req_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        fn f() requires pf() {}
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:3802; rust_to_vir_func.rs:2346
test_verify_one_file! {
    #[test] w_m_returns_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        fn f() -> (r: bool) returns pf() { true }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:1940
test_verify_one_file! {
    #[test] w_m_specfn_arg_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f(c: spec_fn(bool) -> bool) { let b = c(pf()); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2453
test_verify_one_file! {
    #[test] w_m_trigger_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        proof fn f() { assert(forall|i: int| #![trigger g(i), pf()] g(i)); }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::pf` with mode proof")
}

// Covers modes.rs:2230
test_verify_one_file! {
    #[test] w_r_implies_rs verus_code! {
        use vstd::prelude::*;

        proof fn pf() -> bool { true }
        spec fn g(i: int) -> bool { true }
        fn f(a: bool) -> bool { a ==> a }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

// Covers modes.rs:2075
test_verify_one_file! {
    #[test] w_typinv_ctor_rs verus_code! {
        use vstd::prelude::*;

        pub struct P { x: u32 }
        impl P {
            #[verifier::type_invariant]
            spec fn inv(&self) -> bool { self.x > 5 }
        }
        /* FAILS */ fn f() -> P { P { x: 3 } }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}
