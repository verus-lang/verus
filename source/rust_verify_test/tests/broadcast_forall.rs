#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
        {
            reveal(f);
        }

        proof fn test1() {
            reveal(p);
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

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i) // FAILS
        {
        }

        proof fn test1() {
            reveal(p);
            assert(f(10));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p1(i: int)
            ensures f(i)
        {
            reveal(p2);
        }

        #[verifier::broadcast_forall]
        proof fn p2(i: int)
            ensures f(i) // FAILS
        {
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_cycle_disallowed_1 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            reveal(p);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively reveal broadcast_forall")
}

test_verify_one_file! {
    #[test] test_cycle_disallowed_2 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { false }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            reveal(q);
        }

        #[verifier::broadcast_forall]
        proof fn q(i: int)
            ensures f(i)
            decreases i
        {
            reveal(p);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively reveal broadcast_forall")
}

test_verify_one_file! {
    #[test] test_cycle_ordering_3 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { false }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            q(i);
        }

        proof fn q(i: int)
            ensures f(i)
            decreases i
        {
            reveal(p);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively reveal broadcast_forall")
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
        #[verifier::broadcast_forall]
        proof fn f_is_true()
            ensures f(),
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

        #[verifier::broadcast_forall]
        pub proof fn Ring_succ(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.succ()).prev() == p
        { }

        #[verifier::broadcast_forall]
        pub proof fn Ring_prev(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.prev()).succ() == p
        { }

        reveal_group! {
        pub Ring_properties =>
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
                reveal(Ring_succ);
                assert(p.succ().prev() == p);
            }

            proof fn t3(p: Ring) requires p.inv() {
                reveal(Ring_succ);
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t4(p: Ring) requires p.inv() {
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t5(p: Ring) requires p.inv() {
                reveal(Ring_succ);
                reveal(Ring_prev);
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }

            proof fn t6(p: Ring) requires p.inv() {
                reveal(Ring_properties);
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

            #[verifier::broadcast_forall]
            pub proof fn succ_ensures(p: Ring)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.succ()).prev() == p
            { }

            #[verifier::broadcast_forall]
            pub proof fn prev_ensures(p: Ring)
                requires p.inv()
                ensures p.inv() && (#[trigger] p.prev()).succ() == p
            { }

            reveal_group! {
            pub properties =>
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
                reveal(Ring::succ_ensures);
                assert(p.succ().prev() == p);
            }

            proof fn t3(p: Ring) requires p.inv() {
                reveal(Ring::succ_ensures);
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t4(p: Ring) requires p.inv() {
                assert(p.prev().succ() == p); // FAILS
            }

            proof fn t5(p: Ring) requires p.inv() {
                reveal(Ring::succ_ensures);
                reveal(Ring::prev_ensures);
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }

            proof fn t6(p: Ring) requires p.inv() {
                reveal(Ring::properties);
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

            reveal Ring_succ;

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

            reveal Ring_properties;

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

            reveal Ring_prev, Ring_succ;

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ring_algebra_mod_level_not_allowed_1 RING_ALGEBRA.to_string() + verus_code_str! {
        mod m2 {
            use builtin::*;
            use crate::ring::*;

            reveal Ring_prev;
            reveal Ring_succ;

            proof fn t2(p: Ring) requires p.inv() {
                assert(p.succ().prev() == p);
                assert(p.prev().succ() == p);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "only one module-level revealed allowed for each module")
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

            reveal q;

            #[verifier::broadcast_forall]
            pub proof fn p(i: int)
                ensures f(i)
                decreases i
            {
            }
        }

        mod m2 {
            use vstd::prelude::*;
            use crate::mf::*;
            use crate::m1::*;

            reveal p;

            #[verifier::broadcast_forall]
            pub proof fn q(i: int)
                ensures f(i)
                decreases i
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a trait definition, which may result in nontermination")
}
