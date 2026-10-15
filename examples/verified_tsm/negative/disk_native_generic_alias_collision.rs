#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{pervasive::*, *};
verus! {

verified_tokenized_state_machine!{  AuthFrag<#[verifier::reject_recursive_types] fragments_map, V> {
    fields {
        #[sharding(variable)]
        pub auth: Map<fragments_map, V>,

        #[sharding(map)]
        pub fragments: Map<fragments_map, V>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments == self.auth
    }

    init!{
        initialize(m: Map<fragments_map, V>) {
            init auth = m;
            init fragments = m;
        }
    }

    transition!{
        update_key(key: fragments_map, new_value: V) {
            update auth = pre.auth.insert(key, new_value);

            remove fragments -= [ key => let _ ];
            add fragments += [ key => new_value ];
        }
    }

    property!{
        values_agree(key: fragments_map) {
            have fragments >= [ key => let frag_value ];
            assert(pre.auth.dom().contains(key)
                && frag_value == pre.auth.index(key));
        }
    }


    #[inductive(initialize)]
    fn init_inductive(post: Self, m: Map<fragments_map, V>) { }

    #[inductive(update_key)]
    fn update_key_inductive(pre: Self, post: Self, key: fragments_map, new_value: V) {
        assert_maps_equal!(post.fragments, post.auth);
    }
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(auth), Tracked(fragments)) =
            AuthFrag::Instance::initialize(Map::<nat, int>::empty());
        assert(auth.value() == Map::<nat, int>::empty());
        assert(fragments.map() == Map::<nat, int>::empty());
        assert(auth.instance_id() == inst.id() && fragments.instance_id() == inst.id());
    }
}

} // verus!
