//! Complete original special-operation relations with a checked resource companion.
//! Tagged physical storage preserves both original storage projections; the
//! tracked histories exercise all four transitions and reuse withdrawn permission12.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
use vstd::{imap::*, iset::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verified_state_machine_model! { Y {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(imap)]
        pub map: IMap<int, int>,

        #[sharding(multiset)]
        pub mset: Multiset<int>,

        #[sharding(storage_option)]
        pub storage_opt: Option<int>,

        #[sharding(storage_imap)]
        pub storage_map: IMap<int, int>,
    }

    transition!{
        tr1() {
            remove opt -= ( Option::Some(5) );
            add opt += ( Option::Some(8) );

            remove map -= ( IMap::<int, int>::empty().insert(0, 1) );
            have map >= ( IMap::<int, int>::empty().insert(2, 3) );
            add map += ( IMap::<int, int>::empty().insert(4, 5) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };

            remove mset -= ( Multiset::<int>::singleton(10) );
            have mset >= ( Multiset::<int>::singleton(11) );
            add mset += ( Multiset::<int>::singleton(12) );

            withdraw storage_opt -= ( Option::Some(13) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += ( Option::Some(14) );

            withdraw storage_map -= ( IMap::<int, int>::empty().insert(15, 16) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_map += ( IMap::<int, int>::empty().insert(17, 18) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr2() {
            have opt >= (Option::Some(7));
            add map += (IMap::<int, int>::empty().insert(4, 5)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr3() {
            remove opt -= (Option::Some(7));
            withdraw storage_opt -= (Option::Some(12)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr4() {
            add opt += (Option::Some(7)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += (Option::Some(12)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& imap![0 => 1].submap_of(pre.map)
    &&& imap![2 => 3].submap_of(pre.map.remove_keys(imap![0 => 1int].dom()))
    &&& pre.map.remove_keys(imap![0 => 1int].dom()).dom().disjoint(imap![4 => 5int].dom()) ==> {
        &&& Multiset::singleton(10).subset_of(pre.mset)
        &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
        &&& (pre.storage_opt == Option::Some(13) ==> (imap![15 => 16].submap_of(pre.storage_map)
            ==> (pre.storage_map.remove_keys(imap![15 => 16int].dom()).dom().disjoint(
            imap![17 => 18int].dom(),
        ) ==> {
            &&& post.opt == Option::Some(8)
            &&& post.map == pre.map.remove_keys(imap![0 => 1int].dom()).union_prefer_right(
                imap![4 => 5],
            )
            &&& post.mset == pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
            &&& post.storage_opt == Option::Some(14)
            &&& post.storage_map == pre.storage_map.remove_keys(
                imap![15 => 16int].dom(),
            ).union_prefer_right(imap![17 => 18])
        })))
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& post.opt == Option::Some(8)
    &&& imap![0 => 1].submap_of(pre.map)
    &&& imap![2 => 3].submap_of(pre.map.remove_keys(imap![0 => 1int].dom()))
    &&& pre.map.remove_keys(imap![0 => 1int].dom()).dom().disjoint(imap![4 => 5int].dom())
    &&& post.map == pre.map.remove_keys(imap![0 => 1int].dom()).union_prefer_right(imap![4 => 5])
    &&& Multiset::singleton(10).subset_of(pre.mset)
    &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
    &&& post.mset == pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
    &&& pre.storage_opt == Option::Some(13)
    &&& post.storage_opt == Option::Some(14)
    &&& imap![15 => 16].submap_of(pre.storage_map)
    &&& pre.storage_map.remove_keys(imap![15 => 16int].dom()).dom().disjoint(
        imap![17 => 18int].dom(),
    )
    &&& post.storage_map == pre.storage_map.remove_keys(
        imap![15 => 16int].dom(),
    ).union_prefer_right(imap![17 => 18])
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4) ==> {
        &&& post.map == pre.map.union_prefer_right(imap![4 => 5])
        &&& post.opt == pre.opt
        &&& post.storage_opt == pre.storage_opt
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4)
    &&& post.map == pre.map.union_prefer_right(imap![4 => 5])
    &&& post.opt == pre.opt
    &&& post.storage_opt == pre.storage_opt
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& pre.storage_opt == Option::Some(12) ==> {
        &&& post.storage_opt == Option::None
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
        &&& post.opt == Option::None
    }
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& post.opt == Option::None
    &&& pre.storage_opt == Option::Some(12)
    &&& post.storage_opt == Option::None
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
    pre.opt == Option::None ==> ((pre.storage_opt == Option::None ==> {
        &&& post.storage_opt == Option::Some(12)
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
        &&& post.opt == Option::Some(7)
    }))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::None
    &&& post.opt == Option::Some(7)
    &&& pre.storage_opt == Option::None
    &&& post.storage_opt == Option::Some(12)
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

proof fn correct_tr1(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1(pre, post));
    ensures(rel_tr1(pre, post));
}

proof fn rev_tr1(pre: Y::State, post: Y::State) {
    requires(rel_tr1(pre, post));
    ensures(Y::State::tr1(pre, post));
}

proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1_strong(pre, post));
    ensures(rel_tr1_strong(pre, post));
}

proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr1_strong(pre, post));
    ensures(Y::State::tr1_strong(pre, post));
}

proof fn correct_tr2(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2(pre, post));
    ensures(rel_tr2(pre, post));
}

proof fn rev_tr2(pre: Y::State, post: Y::State) {
    requires(rel_tr2(pre, post));
    ensures(Y::State::tr2(pre, post));
}

proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2_strong(pre, post));
    ensures(rel_tr2_strong(pre, post));
}

proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr2_strong(pre, post));
    ensures(Y::State::tr2_strong(pre, post));
}

proof fn correct_tr3(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3(pre, post));
    ensures(rel_tr3(pre, post));
}

proof fn rev_tr3(pre: Y::State, post: Y::State) {
    requires(rel_tr3(pre, post));
    ensures(Y::State::tr3(pre, post));
}

proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3_strong(pre, post));
    ensures(rel_tr3_strong(pre, post));
}

proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr3_strong(pre, post));
    ensures(Y::State::tr3_strong(pre, post));
}

proof fn correct_tr4(pre: Y::State, post: Y::State) {
    requires(Y::State::tr4(pre, post));
    ensures(rel_tr4(pre, post));
}

proof fn rev_tr4(pre: Y::State, post: Y::State) {
    requires(rel_tr4(pre, post));
    ensures(Y::State::tr4(pre, post));
}

proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr4_strong(pre, post));
    ensures(rel_tr4_strong(pre, post));
}

proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr4_strong(pre, post));
    ensures(Y::State::tr4_strong(pre, post));
}

} // verus!
fn main() {}
