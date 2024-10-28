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
        use state_machines_macros::*;

        pub spec fn f() -> bool;

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
        use builtin::*;

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
            use builtin::*;
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
                broadcast use Ring_succ, Ring_prev;
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
        use builtin::*;

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
            use builtin::*;
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
                broadcast use Ring::succ_ensures, Ring::prev_ensures;
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
            use builtin::*;
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
            use builtin::*;
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
            use builtin::*;
            use crate::ring::*;

            broadcast use Ring_prev, Ring_succ;

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
            use builtin::*;
            use crate::ring::*;

            proof fn t2(p: Ring) requires p.inv() {
                broadcast use Ring_prev, Ring_succ;
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_reveal_broadcast RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use builtin::*;
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
            use builtin::*;
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
        use builtin::*;

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
            use builtin::*;
            use crate::ring::*;

            broadcast use Ring::properties;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_exec verus_code! {
        mod ring {
            use builtin::*;

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
            use builtin::*;
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
