//! Persistent option/bool reference operands, plus the persistent count strategy.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    PersistentScalars {
        fields {
            #[sharding(persistent_option)] pub choice: Option<int>,
            #[sharding(persistent_bool)] pub ready: bool,
            #[sharding(persistent_count)] pub lower_bound: nat,
        }
        #[invariant] pub fn stable_choice(&self) -> bool {
            self.choice is Some ==> self.choice->Some_0 == 7int
        }
        init! { initialize(value: Option<int>, ready: bool, count: nat) {
            require(value is Some ==> value->Some_0 == 7int);
            init choice = value;
            init ready = ready;
            init lower_bound = count;
        } }
        transition! { record_singleton() {
            add choice (union)= Some(7int);
            add ready (union)= true;
        } }
        readonly! { observe_singleton() {
            have choice >= Some(let value);
            have ready >= true;
            assert(value == 7int);
        } }
        transition! { record_optional(value: Option<int>, flag: bool, count: nat) {
            require(value is Some ==> value->Some_0 == 7int);
            add choice (union)= (value);
            add ready (union)= (flag);
            add lower_bound (union)= (count);
        } }
        readonly! { observe_optional(value: Option<int>, flag: bool, count: nat) {
            have choice >= (value);
            have ready >= (flag);
            have lower_bound >= (count);
        } }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, value: Option<int>, ready: bool, count: nat) {}
        #[inductive(record_singleton)]
        fn singleton_inductive(pre: Self, post: Self) {}
        #[inductive(record_optional)]
        fn optional_inductive(pre: Self, post: Self, value: Option<int>, flag: bool, count: nat) {}
    }
}

fn main() {
    proof {
        let tracked token = PersistentScalars::Protocol::initialize(None, false, 0nat);
        let tracked token = PersistentScalars::Protocol::record_optional(token, None, false, 0nat);
        let tracked token = PersistentScalars::Protocol::observe_optional(token, None, false, 0nat);
        let tracked token = PersistentScalars::Protocol::record_singleton(token);
        let tracked token = PersistentScalars::Protocol::observe_singleton(token);
        let tracked token = PersistentScalars::Protocol::record_optional(
            token,
            Some(7int),
            true,
            4nat,
        );
        let tracked token = PersistentScalars::Protocol::record_optional(token, None, false, 2nat);
        let tracked token = PersistentScalars::Protocol::observe_optional(
            token,
            Some(7int),
            true,
            4nat,
        );
        assert(PersistentScalars::Fragment::op(token.fragment(), token.fragment())
            == token.fragment());
        let tracked copy = token.duplicate();
        let tracked token = PersistentScalars::Protocol::record_optional(
            token,
            Some(7int),
            true,
            9nat,
        );
        let tracked copy = PersistentScalars::Protocol::observe_optional(
            copy,
            Some(7int),
            true,
            4nat,
        );
        assert(copy.fragment().lower_bound.count == 4);
        assert(token.fragment().lower_bound.count == 9);
    }
}

} // verus!
