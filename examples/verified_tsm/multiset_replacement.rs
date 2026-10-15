//! Checked bag removal followed by observation and addition, with untouched frames.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_finite_multiset::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 BagReplacement {
    fields {#[sharding(multiset)] pub bag:Multiset<int>,}
    init! {initialize(){init bag=Multiset::empty().insert(10int).insert(11int).insert(99int);}}
    transition! {replace(){
        remove bag -= {10int};
        have bag >= {11int};
        add bag += {12int};
    }}
} }
verus! {

broadcast use {vstd::multiset::group_multiset_axioms, vstd::multiset::group_multiset_properties};

pub open spec fn fragment(bag: Multiset<int>) -> BagReplacement::Fragment {
    BagReplacement::Fragment { bag: finite_multiset_frag(bag) }
}

pub proof fn replace_ready(owned: BagReplacement::Fragment, shared: BagReplacement::Fragment)
    requires
        owned.bag.values == Multiset::empty().insert(10int),
        shared.bag.values == Multiset::empty().insert(11int),
    ensures
        BagReplacement::Protocol::replace_requires(owned, shared),
{
    assert forall|frame: BagReplacement::Fragment, pre: BagReplacement::State|
        pre.invariant() && BagReplacement::Fragment::op(
            BagReplacement::Fragment::op(owned, shared),
            frame,
        ) == BagReplacement::Protocol::embed(pre) implies BagReplacement::State::replace_enabled(
        pre,
    ) && BagReplacement::State::replace_owners_enabled(pre, owned, shared) by {
        let combined = BagReplacement::Fragment::op(owned, shared);
        finite_multiset_owned_frame(combined.bag, frame.bag, pre.bag, 10int);
        finite_multiset_owned_frame(combined.bag, frame.bag, pre.bag, 11int);
    }
}

pub proof fn complete_bag_history() {
    let tracked token = BagReplacement::Protocol::initialize();
    assert(Multiset::empty().insert(10int).add(Multiset::empty().insert(11int).insert(99int))
        =~= token.fragment().bag.values);
    let tracked (owned, rest) = token.split(
        fragment(Multiset::empty().insert(10int)),
        fragment(Multiset::empty().insert(11int).insert(99int)),
    );
    assert(Multiset::empty().insert(11int).add(Multiset::empty().insert(99int))
        =~= rest.fragment().bag.values);
    let tracked (shared, outside) = rest.split(
        fragment(Multiset::empty().insert(11int)),
        fragment(Multiset::empty().insert(99int)),
    );
    replace_ready(owned.fragment(), shared.fragment());
    let tracked owned = BagReplacement::Protocol::replace_with_shared(owned, &shared);
    assert(owned.fragment().bag.values =~= Multiset::empty().insert(12int));
    assert(shared.fragment().bag.values == Multiset::empty().insert(11int));
    assert(outside.fragment().bag.values == Multiset::empty().insert(99int));
    let tracked full = owned.join(shared).join(outside);
    assert(full.fragment().bag.values =~= Multiset::empty().insert(12int).insert(11int).insert(
        99int,
    ));
    full.validate();
}

fn main() {
    proof {
        complete_bag_history();
    }
}

} // verus!
