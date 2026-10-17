//! Complete original binding test: all relations and checked physical clients.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, iset::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(map)]
        pub map: Map<int, u64>,

        #[sharding(storage_map)]
        pub storage_map: Map<int, u64>,
    }

    init!{
        initialize() {
            init opt = Option::Some(2);
            init map = Map::<int,u64>::empty().insert(1, 5);
            init storage_map = Map::<int,u64>::empty().insert(1, 6);
        }
    }

    #[invariant]
    pub fn maps_eq(&self) -> bool {
        equal(self.map.dom(), self.storage_map.dom())
    }

    #[invariant]
    pub fn maps_6(&self) -> bool {
        forall |k| imply(self.storage_map.dom().contains(k),
            self.storage_map.index(k) == 6)
    }

    transition!{
        tr1() {
            remove opt -= Some(let x);
            require(x == 2);
        }
    }

    transition!{
        tr2(key: int) {
            remove map -= [key => let x];
            require(x == 5);

            withdraw storage_map -= [key => let y];
            assert(y == 6);
        }
    }

    readonly!{
        tr3(key: int) {
            have map >= [key => let x];
            require(x == 5);

            guard storage_map >= [key => 6];
        }
    }

    property!{
        tr4(key: int) {
            have map >= [key => let x];
            require(x == 5);

            guard storage_map >= [key => 6];
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self, key: int) { }
}}
verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(2)
    &&& post.opt == Option::None
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(2)
    &&& post.opt == Option::None
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
}

spec fn rel_tr2(pre: Y::State, post: Y::State, key: int) -> bool {
    &&& pre.map.dom().contains(key)
    &&& pre.map.index(key) == 5
    &&& ((pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6) ==> {
        &&& post.map == pre.map.remove(key)
        &&& post.storage_map == pre.storage_map.remove(key)
        &&& post.opt == pre.opt
    })
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    &&& pre.map.dom().contains(key)
    &&& pre.map.index(key) == 5
    &&& ((pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6) && {
        &&& post.map == pre.map.remove(key)
        &&& post.storage_map == pre.storage_map.remove(key)
        &&& post.opt == pre.opt
    })
}

spec fn rel_tr3(pre: Y::State, post: Y::State, key: int) -> bool {
    &&& pre.map.dom().contains(key)
    &&& pre.map.index(key) == 5
    &&& ((pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6) ==> {
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.opt == pre.opt
    })
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    &&& pre.map.dom().contains(key)
    &&& pre.map.index(key) == 5
    &&& ((pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6) && {
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.opt == pre.opt
    })
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

proof fn correct_tr2(pre: Y::State, post: Y::State, key: int) {
    requires(Y::State::tr2(pre, post, key));
    ensures(rel_tr2(pre, post, key));
}

proof fn rev_tr2(pre: Y::State, post: Y::State, key: int) {
    requires(rel_tr2(pre, post, key));
    ensures(Y::State::tr2(pre, post, key));
}

proof fn correct_tr2_strong(pre: Y::State, post: Y::State, key: int) {
    requires(Y::State::tr2_strong(pre, post, key));
    ensures(rel_tr2_strong(pre, post, key));
}

proof fn rev_tr2_strong(pre: Y::State, post: Y::State, key: int) {
    requires(rel_tr2_strong(pre, post, key));
    ensures(Y::State::tr2_strong(pre, post, key));
}

proof fn correct_tr3(pre: Y::State, post: Y::State, key: int) {
    requires(Y::State::tr3(pre, post, key));
    ensures(rel_tr3(pre, post, key));
}

proof fn rev_tr3(pre: Y::State, post: Y::State, key: int) {
    requires(rel_tr3(pre, post, key));
    ensures(Y::State::tr3(pre, post, key));
}

proof fn correct_tr3_strong(pre: Y::State, post: Y::State, key: int) {
    requires(Y::State::tr3_strong(pre, post, key));
    ensures(rel_tr3_strong(pre, post, key));
}

proof fn rev_tr3_strong(pre: Y::State, post: Y::State, key: int) {
    requires(rel_tr3_strong(pre, post, key));
    ensures(Y::State::tr3_strong(pre, post, key));
}

} // verus!
verus! {

proof fn do_tokens() {
    let tracked mut m: Map<int, u64> = Map::tracked_empty();
    m.tracked_insert(1, 6u64);
    let tracked (Tracked(inst), Tracked(opt_token), Tracked(mut map_tokens)) =
        Y::Instance::initialize(m);

    match opt_token {
        Option::None => {
            assert(false);
        },
        Option::Some(opt_token) => {
            inst.tr1(opt_token);

            assert(map_tokens.dom().contains(1));
            let tracked map_token = map_tokens.remove(1);

            let tracked the_guard = inst.tr4(1, &map_token);
            assert(*the_guard == 6);

            let tracked t = inst.tr2(1, map_token);
            assert(t == 6);
        },
    };
}

fn main() {
    proof {
        let tracked mut m: Map<int, u64> = Map::tracked_empty();
        m.tracked_insert(1, 6u64);
        let tracked (Tracked(inst), Tracked(opt_token), Tracked(mut map_tokens)) =
            Y::Instance::initialize(m);
        match opt_token {
            Option::None => {
                assert(false);
            },
            Option::Some(opt_token) => {
                inst.tr1(opt_token);
                let tracked map_token = map_tokens.remove(1);
                let tracked the_guard = inst.tr3(1, &map_token);
                assert(*the_guard == 6);
                let tracked the_guard = inst.tr4(1, &map_token);
                assert(*the_guard == 6);
                let tracked t = inst.tr2(1, map_token);
                assert(t == 6);
                let tracked t = inst.tr2(1, map_token);
                assert(map_tokens.dom().is_empty());
            },
        }
    }
}

} // verus!
