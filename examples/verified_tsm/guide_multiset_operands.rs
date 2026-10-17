//! Every multiset operand form, including repeated values and empty no-ops.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BagOperands {
        fields { #[sharding(multiset)] pub values: Multiset<int>, }
        init! { initialize(m: Multiset<int>) { init values = m; } }
        transition! { add_one(value: int) { add values += { value }; } }
        transition! { remove_one(value: int) { remove values -= { value }; } }
        readonly! { have_one(value: int) { have values >= { value }; } }
        transition! { add_many(m: Multiset<int>) { add values += (m); } }
        transition! { remove_many(m: Multiset<int>) { remove values -= (m); } }
        readonly! { have_many(m: Multiset<int>) { have values >= (m); } }
    }
}

fn main() {
    proof {
        let empty = Multiset::<int>::empty();
        let repeated = empty.insert(7int).insert(7int).insert(8int);
        let tracked token = BagOperands::Protocol::initialize(empty);
        let tracked token = BagOperands::Protocol::add_many(token, repeated);
        let tracked token = BagOperands::Protocol::have_many(token, repeated);
        let tracked token = BagOperands::Protocol::have_many(token, empty);
        let tracked token = BagOperands::Protocol::remove_many(token, empty);
        let tracked token = BagOperands::Protocol::add_many(token, empty);
        let tracked token = BagOperands::Protocol::remove_one(token, 7int);
        assert(token.fragment().values.at(7int).count == 1);
        let tracked token = BagOperands::Protocol::have_one(token, 7int);
        let tracked token = BagOperands::Protocol::add_one(token, 9int);
        let remaining = empty.insert(7int).insert(8int).insert(9int);
        let tracked token = BagOperands::Protocol::remove_many(token, remaining);
        assert(token.fragment().values.values == empty);
    }
}

} // verus!
