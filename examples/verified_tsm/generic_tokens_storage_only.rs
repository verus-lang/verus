//! Operations that consume or borrow no token, in machines with storage.
//!
//! * `Unit` sources: `<init>_with_unit` returns a `Unit` along with the
//!   initializer's outputs, and `Unit::split` divides one into two. A machine
//!   whose only tokenized state is storage (and constants) has no field token
//!   to take a unit from (`unit_from_<field>`).
//! * A guard without a borrowed token guards from the instance itself (it
//!   holds a leaked unit token, with the constants' fragment).
//! * A property that reads only constants holds in the reachable state with
//!   the instance's constants (part of the instance's type invariant).
//! * The port of rust_verify_test `relation_codegen_opt_general`: general
//!   `None` operands of an `option` and a `storage_option` field.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    StorageOnly {
        fields {
            #[sharding(constant)]
            pub k: int,

            #[sharding(storage_imap)]
            pub v: IMap<int, int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.k > 0
            &&& self.v.dom().contains(self.k)
            &&& self.v[self.k] == 5
            // General storage_imap withdrawals need finite operands.
            &&& self.v.dom().finite()
        }

        init!{
            initialize(k: int, m: IMap<int, int>) {
                require(k > 0 && m.dom().contains(k) && m[k] == 5 && m.dom().finite());
                init k = k;
                init v = m;
            }
        }

        // A guard of the invariant's entry; no token is borrowed.
        property!{
            read() {
                guard v >= [pre.k => 5];
            }
        }

        // A property of the constants only.
        property!{
            k_positive() {
                assert(pre.k > 0);
            }
        }

        // Withdraws everything but the guarded entry; consumes no token.
        transition!{
            take_rest() {
                birds_eye let rest = pre.v.remove(pre.k);
                withdraw v -= (rest);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, k: int, m: IMap<int, int>) { }

        #[inductive(take_rest)]
        fn take_rest_inductive(pre: Self, post: Self) {
            assert(post.v.dom().contains(post.k));
            assert(post.v.dom() =~= ISet::empty().insert(post.k));
        }
    }
}

// rust_verify_test `relation_codegen_opt_general` (with an initializer).
verified_tokenized_state_machine! {
    Y {
        fields {
            #[sharding(option)]
            pub opt: Option<int>,

            #[sharding(storage_option)]
            pub storage_opt: Option<int>,
        }

        init!{
            initialize() {
                init opt = Option::None;
                init storage_opt = Option::None;
            }
        }

        property!{
            ro() {
                guard storage_opt >= (Option::<int>::None);
            }
        }

        transition!{
            tr1() {
                have opt >= (Option::<int>::None);
            }
        }

        transition!{
            tr2() {
                add opt += (Option::<int>::None);
                deposit storage_opt += (Option::<int>::None);
            }
        }

        transition!{
            tr3() {
                remove opt -= (Option::<int>::None);
                withdraw storage_opt -= (Option::<int>::None);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(tr1)]
        fn tr1_inductive(pre: Self, post: Self) { }

        #[inductive(tr2)]
        fn tr2_inductive(pre: Self, post: Self) { }

        #[inductive(tr3)]
        fn tr3_inductive(pre: Self, post: Self) { }
    }
}

verus! {

proof fn storage_only_client() {
    let m = IMap::<int, int>::empty().insert(3, 5).insert(4, 6);
    let tracked mut stored = IMap::tracked_empty();
    stored.tracked_insert(3int, 5int);
    stored.tracked_insert(4int, 6int);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(unit)) = StorageOnly::Instance::initialize_with_unit(3, m, stored);
    assert(inst.k() == 3);
    let tracked g = inst.read();
    assert(*g == 5);
    inst.k_positive();
    assert(inst.k() > 0);
    let tracked (u1, u2) = unit.split();
    let tracked rest = inst.take_rest(u1);
    // A second withdrawal: the guarded entry stays.
    let tracked rest2 = inst.take_rest(u2);
    let tracked g2 = inst.read();
    assert(*g2 == 5);
}

proof fn y_client() {
    let tracked (Tracked(inst), Tracked(opt), Tracked(unit)) = Y::Instance::initialize_with_unit(None);
    assert(opt is None);
    let tracked g = inst.ro();
    assert(g is None);
    inst.tr1(&opt);
    let tracked (u1, u2) = unit.split();
    let tracked added = inst.tr2(None, u1);
    assert(added is None);
    let tracked withdrawn = inst.tr3(added, u2);
    assert(withdrawn is None);
}

}

fn main() {}
