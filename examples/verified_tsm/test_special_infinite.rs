//! Complete original special-operation relations and reference proofs.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
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
            remove opt -= Some(5);
            add opt += Some(8);

            remove map -= [0 => 1];
            have map >= [2 => 3];
            add map += [4 => 5] by { /* Original unsafe override omitted from this pure diagnostic. */ };

            remove mset -= {10};
            have mset >= {11};
            add mset += {12};

            withdraw storage_opt -= Some(13) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += Some(14);

            withdraw storage_map -= [15 => 16] by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_map += [17 => 18] by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr2() {
            have opt >= Some(7);
            add map += [4 => 5] by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr3() {
            remove opt -= Some(7);
            withdraw storage_opt -= Some(12) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr4() {
            add opt += Some(7) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += Some(12) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& pre.map.contains_pair(0, 1)
    &&& pre.map.remove(0).contains_pair(2, 3)
    &&& !pre.map.remove(0).dom().contains(4) ==> pre.mset.count(10) >= 1 && pre.mset.remove(
        10,
    ).count(11) >= 1 && (pre.storage_opt == Option::Some(13) ==> (pre.storage_map.contains_pair(
        15,
        16,
    ) ==> (!pre.storage_map.remove(15).dom().contains(17) ==> post.storage_map
        == pre.storage_map.remove(15).insert(17, 18) && post.opt == Option::Some(8) && post.map
        == pre.map.remove(0).insert(4, 5) && post.mset == pre.mset.remove(10).insert(12)
        && post.storage_opt == Option::Some(14))))
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& post.opt == Option::Some(8)
    &&& pre.map.contains_pair(0, 1)
    &&& pre.map.remove(0).contains_pair(2, 3)
    &&& !pre.map.remove(0).dom().contains(4)
    &&& post.map == pre.map.remove(0).insert(4, 5)
    &&& pre.mset.count(10) >= 1
    &&& pre.mset.remove(10).count(11) >= 1
    &&& post.mset == pre.mset.remove(10).insert(12)
    &&& pre.storage_opt == Option::Some(13)
    &&& post.storage_opt == Option::Some(14)
    &&& pre.storage_map.contains_pair(15, 16)
    &&& !pre.storage_map.remove(15).dom().contains(17)
    &&& post.storage_map == pre.storage_map.remove(15).insert(17, 18)
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4) ==> {
        &&& post.map == pre.map.insert(4, 5)
        &&& post.opt == pre.opt
        &&& post.storage_opt == pre.storage_opt
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4)
    &&& post.map == pre.map.insert(4, 5)
    &&& post.opt == pre.opt
    &&& post.storage_opt == pre.storage_opt
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& pre.storage_opt == Option::Some(12) ==> post.storage_opt == Option::None && post.map
        == pre.map && post.storage_map == pre.storage_map && post.mset == pre.mset && post.opt
        == Option::None
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
