#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{pervasive::*, *};
verus! {

verified_tokenized_state_machine!{  AuthFrag<#[verifier::reject_recursive_types] K, V> {
    fields {
        #[sharding(variable)]
        pub fragments_map: Map<K, V>,

        #[sharding(map)]
        pub fragments: Map<K, V>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments == self.fragments_map
    }

    init!{
        initialize(m: Map<K, V>) {
            init fragments_map = m;
            init fragments = m;
        }
    }

    transition!{
        update_key(key: K, new_value: V) {
            update fragments_map = pre.fragments_map.insert(key, new_value);

            remove fragments -= [ key => let _ ];
            add fragments += [ key => new_value ];
        }
    }

    property!{
        values_agree(key: K) {
            have fragments >= [ key => let frag_value ];
            assert(pre.fragments_map.dom().contains(key)
                && frag_value == pre.fragments_map.index(key));
        }
    }


    #[inductive(initialize)]
    fn init_inductive(post: Self, m: Map<K, V>) { }

    #[inductive(update_key)]
    fn update_key_inductive(pre: Self, post: Self, key: K, new_value: V) {
        assert_maps_equal!(post.fragments, post.fragments_map);
    }
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(fragments_map), Tracked(fragments)) =
            AuthFrag::Instance::initialize(Map::<nat, int>::empty());
        assert(fragments_map.value() == Map::<nat, int>::empty());
        assert(fragments.map() == Map::<nat, int>::empty());
        assert(fragments_map.instance_id() == inst.id() && fragments.instance_id() == inst.id());
    }
}

} // verus!
