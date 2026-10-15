// EXPECTED-ERROR: error: precondition not satisfied
// EXPECTED-ERROR: precondition not satisfied
//! Complete original persistent map model, references, and native client.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*};
verified_tokenized_state_machine! {

Y {
    fields {
        #[sharding(persistent_map)]
        pub c: Map<int, int>,
    }

    init!{
        initialize() {
            init c = Map::empty().insert(1, 2);
        }
    }

    transition!{
        tr1() {
            have c >= [1 => 2];
            add c (union)= [3 => 4];
        }
    }

    transition!{
        tr2() {
            add c (union)= (
                Map::empty().insert(5, 9).insert(12, 15)
            );
        }
    }

    transition!{
        tr3() {
            have c >= (
                Map::empty().insert(5, 9).insert(12, 15)
            );
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        imply(self.c.dom().contains(5), self.c.index(5) == 9)
        &&
        imply(self.c.dom().contains(12), self.c.index(12) == 15)
        &&
        imply(self.c.dom().contains(3), self.c.index(3) == 4)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self) { }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.c.dom().contains(1)
    &&& pre.c.index(1) == 2
    &&& ((pre.c.dom().contains(3) ==> pre.c.index(3) == 4) ==> (post.c == pre.c.insert(3, 4)))
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.c.dom().contains(1)
    &&& pre.c.index(1) == 2
    &&& ((pre.c.dom().contains(3) ==> pre.c.index(3) == 4) && (post.c == pre.c.insert(3, 4)))
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9) && (pre.c.dom().contains(12) ==> pre.c.index(
        12,
    ) == 15)) ==> post.c == pre.c.insert(5, 9).insert(12, 15)
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9) && (pre.c.dom().contains(12) ==> pre.c.index(
        12,
    ) == 15)) && post.c == pre.c.insert(5, 9).insert(12, 15)
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
    &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
    &&& pre.c == post.c
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
    &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
    &&& pre.c == post.c
}

proof fn correct_tr(pre: Y::State, post: Y::State)
    ensures
        rel_tr1(pre, post) == Y::State::tr1(pre, post),
        rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
        rel_tr2(pre, post) == Y::State::tr2(pre, post),
        rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
        rel_tr3(pre, post) == Y::State::tr3(pre, post),
        rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
{
    assert_maps_equal!(
                pre.c.insert(5, 9).insert(12, 15),
                pre.c.union_prefer_right(
                    Map::empty().insert(5, 9).insert(12, 15)
                )
            );

    if rel_tr3(pre, post) {
        assert(Map::empty().insert(5, 9).insert(12, 15).submap_of(pre.c));
        assert(Y::State::tr3(pre, post));
    }
    if Y::State::tr3(pre, post) {
        assert(Map::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(5));
        assert(Map::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(12));
        assert(pre.c.dom().contains(5));
        assert(pre.c.dom().contains(12));
        assert(rel_tr3(pre, post));
    }
}

proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(mut init_m)) = Y::Instance::initialize();
    inst.tr3(&init_m);
}

fn main() {
    proof {
        test_inst();
    }
}

} // verus!
