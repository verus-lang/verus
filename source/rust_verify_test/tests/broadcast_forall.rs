#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn p(i: int)
            ensures f(i)
        {
            reveal(f);
        }

        proof fn test1() {
            broadcast use p;
            assert(f(10));
        }

        proof fn test2() {
            assert(f(10)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn p(i: int)
            ensures f(i) // FAILS
        {
        }

        proof fn test1() {
            broadcast use p;
            assert(f(10));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn p1(i: int)
            ensures f(i)
        {
            broadcast use p2;
        }

        broadcast proof fn p2(i: int)
            ensures f(i) // FAILS
        {
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_cycle_disallowed_1 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            broadcast use p;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively use a broadcast proof fn")
}

test_verify_one_file! {
    #[test] test_cycle_disallowed_2 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { false }

        broadcast proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            broadcast use q;
        }

        broadcast proof fn q(i: int)
            ensures f(i)
            decreases i
        {
            broadcast use p;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively use a broadcast proof fn")
}

test_verify_one_file! {
    #[test] test_cycle_ordering_3 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { false }

        broadcast proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            q(i);
        }

        proof fn q(i: int)
            ensures f(i)
            decreases i
        {
            broadcast use p;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively use a broadcast proof fn")
}

test_verify_one_file! {
    #[test] test_sm verus_code! {
        // This tests the fix for an issue with the heuristic for pushing broadcast_forall
        // functions to the front.
        // Specifically, the state_machine! macro generates some external_body functions
        // which got pushed to the front by those heurstics. But those external_body functions
        // depended on the the proof fn `stuff_inductive` (via the extra_dependencies mechanism)
        // This caused the `stuff_inductive` to end up BEFORE the broadcast_forall function
        // it needed.

        use vstd::*;
        use verus_state_machines_macros::*;

        pub uninterp spec fn f() -> bool;

        #[verifier::external_body]
        broadcast proof fn f_is_true()
            ensures #[trigger] f(),
        {
        }

        state_machine!{ X {
            fields {
                pub a: u8,
            }

            transition!{
                stuff() {
                    update a = 5;
                }
            }

            #[invariant]
            pub spec fn inv(&self) -> bool {
                true
            }

            #[inductive(stuff)]
            fn stuff_inductive(pre: Self, post: Self) {
                broadcast use f_is_true;
                assert(f());
            }
        }}
    } => Ok(())
}

const RING_ALGEBRA: &str = verus_code_str! {
    mod ring {
        use verus_builtin::*;

        pub struct Ring {
            pub i: nat,
        }

        impl Ring {
            pub closed spec fn inv(&self) -> bool {
                self.i < 10
            }

            pub closed spec fn succ(&self) -> Ring {
                Ring { i: if self.i == 9 { 0 } else { self.i + 1 } }
            }

            pub closed spec fn prev(&self) -> Ring {
                Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as nat } }
            }
        }

        pub broadcast proof fn Ring_succ(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.succ()).prev() == p
        { }

        pub broadcast proof fn Ring_prev(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.prev()).succ() == p
        { }

        pub broadcast group Ring_properties {
            Ring_succ,
            Ring_prev,
        }
    }
};

test_verify_one_file! {
    #[test] test_ring_algebra_basic RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            proof fn t1(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p); // FAILS
            }

            proof fn t2(p: Ring) requires p.inv() {
                broadcast use Ring_succ;
                assert(p.succ().prev() == p);
            }

            proof fn t3(p: Ring) requires p.inv() {
                broadcast use Ring_succ;
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t4(p: Ring) requires p.inv() {
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t5(p: Ring) requires p.inv() {
                broadcast use {Ring_succ, Ring_prev};
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }

            proof fn t6(p: Ring) requires p.inv() {
                broadcast use Ring_properties;
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

const RING_ALGEBRA_MEMBERS: &str = verus_code_str! {
    mod ring {
        use verus_builtin::*;

        pub struct Ring {
            pub i: nat,
        }

        impl Ring {
            pub closed spec fn inv(&self) -> bool {
                self.i < 10
            }

            pub closed spec fn succ(&self) -> Ring {
                Ring { i: if self.i == 9 { 0 } else { self.i + 1 } }
            }

            pub closed spec fn prev(&self) -> Ring {
                Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as nat } }
            }

            pub broadcast proof fn succ_ensures(p: Ring)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.succ()).prev() == p
            { }

            pub broadcast proof fn prev_ensures(p: Ring)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.prev()).succ() == p
            { }

            pub broadcast group properties {
                Ring::succ_ensures,
                Ring::prev_ensures,
            }
        }
    }
};

test_verify_one_file! {
    #[test] test_ring_algebra_member RING_ALGEBRA_MEMBERS.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            proof fn t1(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p); // FAILS
            }

            proof fn t2(p: Ring) requires p.inv() {
                broadcast use Ring::succ_ensures;
                assert(p.succ().prev() == p);
            }

            proof fn t3(p: Ring) requires p.inv() {
                broadcast use Ring::succ_ensures;
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t4(p: Ring) requires p.inv() {
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t5(p: Ring) requires p.inv() {
                broadcast use {Ring::succ_ensures, Ring::prev_ensures};
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }

            proof fn t6(p: Ring) requires p.inv() {
                broadcast use Ring::properties;
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_ring_algebra_mod_level_1 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            broadcast use Ring_succ;

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_mod_level_2 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            broadcast use Ring_properties;

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_mod_level_3 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            broadcast use {Ring_prev, Ring_succ};

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_broadcast_use_stmt_1 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            proof fn t2(p: Ring) requires p.inv() {
                broadcast use {Ring_prev, Ring_succ};
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_reveal_broadcast RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            proof fn t2(p: Ring) requires p.inv() {
                reveal(Ring_prev);
                reveal(Ring_succ);
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function, got proof-mode function")
}

test_verify_one_file! {
    #[test] test_ring_algebra_mod_level_not_allowed_1 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            broadcast use Ring_prev;
            broadcast use Ring_succ;

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "only one module-level `broadcast use` allowed for each module")
}

test_verify_one_file! {
    #[test] test_circular_module_reveal verus_code! {
        mod mf {
            use vstd::prelude::*;
            #[verifier::opaque]
            pub open spec fn f(i: int) -> bool { false }
        }

        mod m1 {
            use vstd::prelude::*;
            use crate::mf::*;
            use crate::m2::*;

            broadcast use q;

            pub broadcast proof fn p(i: int)
                ensures f(i)
                decreases i
            {
            }
        }

        mod m2 {
            use vstd::prelude::*;
            use crate::mf::*;
            use crate::m1::*;

            broadcast use p;

            pub broadcast proof fn q(i: int)
                ensures f(i)
                decreases i
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

const RING_ALGEBRA_MEMBERS_GENERIC: &str = verus_code_str! {
    mod ring {
        use vstd::prelude::*;

        pub struct Ring<T: Copy> {
            pub i: nat,
            pub t: T,
        }

        impl<T: Copy> Ring<T> {
            pub closed spec fn inv(&self) -> bool {
                self.i < 10
            }

            pub closed spec fn succ(&self) -> Self {
                Ring { i: if self.i == 9 { 0 } else { self.i + 1 }, t: self.t }
            }

            pub closed spec fn prev(&self) -> Self {
                Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as nat }, t: self.t }
            }

            pub broadcast proof fn succ_ensures(p: Self)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.succ()).prev() == p
            { }

            pub broadcast proof fn prev_ensures(p: Self)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.prev()).succ() == p
            { }

            pub broadcast group properties {
                Ring::succ_ensures,
                Ring::prev_ensures,
            }
        }
    }
};

test_verify_one_file! {
    #[test] test_ring_algebra_member_generic RING_ALGEBRA_MEMBERS_GENERIC.to_string() + verus_code_str! {
        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            broadcast use Ring::properties;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_exec verus_code! {
        mod ring {
            use verus_builtin::*;

            pub struct Ring {
                pub i: u64,
            }

            impl Ring {
                pub closed spec fn inv(&self) -> bool {
                    self.i < 10
                }

                pub closed spec fn spec_succ(&self) -> Ring {
                    Ring { i: if self.i == 9 { 0 } else { (self.i + 1) as u64 } }
                }

                pub closed spec fn spec_prev(&self) -> Ring {
                    Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as u64 } }
                }

                pub broadcast proof fn spec_succ_ensures(p: Ring)
                    requires p.inv()
                    ensures p.inv() && (#[trigger] p.spec_succ()).spec_prev() == p
                { }

                pub broadcast proof fn spec_prev_ensures(p: Ring)
                    requires p.inv()
                    ensures p.inv() && (#[trigger] p.spec_prev()).spec_succ() == p
                { }

                pub broadcast group properties {
                    Ring::spec_succ_ensures,
                    Ring::spec_prev_ensures,
                }
            }
        }

        mod m2 {
            use verus_builtin::*;
            use crate::ring::*;

            fn t2(p: Ring) requires p.inv() {
                broadcast use Ring::properties;
                assert(p.spec_succ().spec_prev() == p);
                assert(p.spec_prev().spec_succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_pruning_module_level_reveal verus_code! {
        // TODO: this intentionally proves false,
        // as this was the original scenario where this bug was discovered
        // it's obviously not an unsoundness (due to the `assume(false)`

        pub open spec fn f(i: int) -> bool { false }

        mod m1 {
            use super::*;

            broadcast use super::m2::lemma;

            pub proof fn lemma(i: int)
                ensures f(i)
                decreases i
            {
            }
        }

        mod m2 {
            use super::*;

            pub broadcast proof fn lemma(i: int)
                ensures #[trigger] f(i)
                decreases i
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pruning_for_krate_regression_1209 verus_code! {
        pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat)
            requires a % (b * c) == 0, b > 0, c > 0
            ensures a % b == 0
        {
            broadcast use vstd::arithmetic::div_mod::lemma_mod_breakdown;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pruning_for_krate_regression_1209_2 verus_code! {
        broadcast use vstd::arithmetic::div_mod::lemma_mod_breakdown;

        pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat)
            requires a % (b * c) == 0, b > 0, c > 0
            ensures a % b == 0
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] broadcast_group_should_check_member_is_broadcast_regression_1355 verus_code! {
        proof fn lemma_foo()
            ensures true
        {}

        broadcast group group_foo {
            lemma_foo,
        }

        proof fn lemma_bar() {
            broadcast use group_foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "lemma_foo is not a broadcast proof fn")
}

test_verify_one_file! {
    #[ignore] #[test] broadcast_old_syntax_warning verus_code! {
        broadcast use vstd::seq_lib::group_seq_properties, vstd::set_lib::group_set_properties;
    } => Ok(err) => {
        assert!(err.errors.is_empty());
        assert!(err.warnings.iter().find(|w| w.message.contains("broadcast use")).iter().next().is_some());
    }
}

test_verify_one_file! {
    #[test] broadcast_mut_params verus_code! {
        #[verifier::opaque]
        #[verifier::prophetic]
        pub closed spec fn foo<A>(s: &mut A) -> bool {
            has_resolved(s)
        }

        pub broadcast proof fn test_broadcast<A>(s: &mut A)
            ensures
                #[trigger] foo(s) <==> has_resolved(s)
        {
            reveal(foo);
        }

        proof fn test<A>(x: &mut A) {
            broadcast use test_broadcast;
            assert(foo(x) <==> has_resolved(x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] broadcast_prune_inline verus_code! {
        mod m1 {
            use verus_builtin::*; use verus_builtin_macros::*;

            pub closed spec fn f(i: int) -> int { i }

            #[verifier::inline]
            pub open spec fn g(i: int) -> int { f(i) }

            pub broadcast proof fn p(i: int)
                ensures
                    #![trigger g(i)]
                    g(i) == i,
            {
            }

            pub broadcast group b {
                p,
            }
        }

        mod m2 {
            use verus_builtin::*; use verus_builtin_macros::*;

            proof fn test() {
                use crate::m1::{f, g};
                broadcast use crate::m1::b;
                assert(f(10) == 10);
            }
        }
    } => Ok(())
}

// Issue #1166: a broadcast axiom enabled before a for-loop must stay available
// inside the isolated loop. `admit` is confined to this uninterpreted predicate.
test_verify_one_file! {
    #[test] issue_1166_broadcast_visible_in_for_loop verus_code! {
        use vstd::prelude::*;

        pub uninterp spec fn map_contains_key_opaque<Key, Value>(m: Map<Key, Value>, k: Key) -> bool;

        pub broadcast proof fn axiom_map_contains_key_opaque<Key, Value>(m: Map<Key, Value>, k: Key)
            ensures
                #[trigger] map_contains_key_opaque::<Key, Value>(m, k) <==> m.contains_key(k),
        {
            admit();
        }

        fn test_axiom(m: Map<u64, u32>, k: u64)
            requires
                map_contains_key_opaque(m, k),
        {
            broadcast use axiom_map_contains_key_opaque;
            for _i in 0..10
                invariant
                    map_contains_key_opaque(m, k),
            {
                assert(m.contains_key(k)) by {
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] broadcast_use_reaches_isolated_loops verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::opaque]
        spec fn g(i: int) -> bool { true }

        broadcast proof fn lemma_f(i: int)
            ensures #[trigger] f(i),
        {
            reveal(f);
        }

        broadcast proof fn lemma_g(i: int)
            ensures #[trigger] g(i),
        {
            reveal(g);
        }

        broadcast group group_fg {
            lemma_f,
            lemma_g,
        }

        fn test_for() {
            broadcast use lemma_f;
            let mut n: u64 = 0;
            for x in 0u64..2u64
                invariant n == x,
            {
                assert(f(10));
                n = n + 1;
            }
            assert(n == 2);
        }

        fn test_while() {
            broadcast use lemma_f;
            let mut i: u64 = 0;
            while i < 2
                invariant i <= 2,
                decreases 2 - i,
            {
                assert(f(10));
                i = i + 1;
            }
        }

        fn test_nested() {
            broadcast use lemma_f;
            let mut i: u64 = 0;
            while i < 2
                invariant i <= 2,
                decreases 2 - i,
            {
                let mut j: u64 = 0;
                while j < 2
                    invariant j <= 2,
                    decreases 2 - j,
                {
                    assert(f(10));
                    j = j + 1;
                }
                i = i + 1;
            }
        }

        fn test_group() {
            broadcast use group_fg;
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(1));
                assert(g(1));
                i = i + 1;
            }
        }

        fn test_positive_branch_and_nested(b: bool) {
            if b {
                broadcast use lemma_f;
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    let mut j: u64 = 0;
                    while j < 1
                        invariant j <= 1,
                        decreases 1 - j,
                    {
                        assert(f(3));
                        j = j + 1;
                    }
                    i = i + 1;
                }
            }
        }

        fn test_closure_sees_outer_broadcast() {
            broadcast use lemma_f;
            let clos = |x: u64| -> (r: u64)
                ensures r == x,
            {
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(f(4));
                    i = i + 1;
                }
                x
            };
            let _ = clos(1u64);
        }

        fn test_proof_block_broadcast_reaches_later_loop() {
            proof {
                broadcast use lemma_f;
            }
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(5));
                i = i + 1;
            }
        }

        // `assert by` and `by (nonlinear_arith)` are separate proof contexts.
        // Directives established before them stay available to a later loop,
        // and the nonlinear query itself does not import those directives.
        fn test_broadcast_survives_proof_queries() {
            broadcast use lemma_f;
            assert(f(6)) by {
            };
            assert(true) by (nonlinear_arith) {
            };
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(6));
                i = i + 1;
            }
        }

        fn test_isolation_boundary_pre_stms() {
            broadcast use lemma_f;
            let mut i: u64 = 0;
            #[verus::internal(loop_isolation_boundary)]
            {
                broadcast use lemma_g;
                let y: u64 = 1;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(f(7));
                    assert(g(7));
                    assert(y == 1);
                    i = i + 1;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] broadcast_use_does_not_leak_across_queries verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn lemma_f(i: int)
            ensures f(i),
        {
            reveal(f);
        }

        fn no_broadcast() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10)); // FAILS
                i = i + 1;
            }
        }

        fn broadcast_after_loop() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10)); // FAILS
                i = i + 1;
            }
            broadcast use lemma_f;
        }

        fn sibling_branch(b: bool) {
            if b {
                broadcast use lemma_f;
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(f(10));
                    i = i + 1;
                }
            } else {
                let mut i: u64 = 0;
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(f(10)); // FAILS
                    i = i + 1;
                }
            }
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10)); // FAILS
                i = i + 1;
            }
        }

        fn only_inside_completed_loop() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                broadcast use lemma_f;
                assert(f(10));
                i = i + 1;
            }
            let mut j: u64 = 0;
            while j < 1
                invariant j <= 1,
                decreases 1 - j,
            {
                assert(f(10)); // FAILS
                j = j + 1;
            }
        }

        fn nonlinear_query_stays_isolated() {
            broadcast use lemma_f;
            assert(f(10)) by (nonlinear_arith) { // FAILS
            };
        }

        fn closure_broadcast_does_not_escape() {
            let clos = |x: u64| -> (r: u64)
                ensures r == x,
            {
                broadcast use lemma_f;
                assert(f(10));
                x
            };
            let _ = clos(1u64);
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10)); // FAILS
                i = i + 1;
            }
        }

        fn assert_by_broadcast_does_not_escape() {
            assert(true) by {
                broadcast use lemma_f;
                assert(f(10));
            };
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10)); // FAILS
                i = i + 1;
            }
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] ordinary_facts_stay_isolated verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        broadcast proof fn lemma_f(i: int)
            ensures f(i),
        {
            reveal(f);
        }

        fn precondition_not_in_invariant(x: u64)
            requires x == 5,
        {
            broadcast use lemma_f;
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10));
                assert(x == 5); // FAILS
                i = i + 1;
            }
        }

        fn local_not_in_invariant() {
            let y: u64 = 6;
            broadcast use lemma_f;
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10));
                assert(y == 6); // FAILS
                i = i + 1;
            }
        }

        fn outside_boundary_not_in_invariant() {
            broadcast use lemma_f;
            let z: u64 = 7;
            let mut i: u64 = 0;
            #[verus::internal(loop_isolation_boundary)]
            {
                while i < 1
                    invariant i <= 1,
                    decreases 1 - i,
                {
                    assert(f(10));
                    assert(z == 7); // FAILS
                    i = i + 1;
                }
            }
        }

        #[verifier::loop_isolation(false)]
        fn not_isolated(x: u64)
            requires x == 5,
        {
            let y: u64 = 6;
            broadcast use lemma_f;
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                assert(f(10));
                assert(x == 5);
                assert(y == 6);
                i = i + 1;
            }
        }
    } => Err(err) => assert_fails(err, 3)
}
