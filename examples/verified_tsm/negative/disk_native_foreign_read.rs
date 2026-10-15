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
        pub auth: Map<K, V>,

        #[sharding(map)]
        pub fragments: Map<K, V>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments == self.auth
    }

    init!{
        initialize(m: Map<K, V>) {
            init auth = m;
            init fragments = m;
        }
    }

    transition!{
        update_key(key: K, new_value: V) {
            update auth = pre.auth.insert(key, new_value);

            remove fragments -= [ key => let _ ];
            add fragments += [ key => new_value ];
        }
    }

    property!{
        values_agree(key: K) {
            have fragments >= [ key => let frag_value ];
            assert(pre.auth.dom().contains(key)
                && frag_value == pre.auth.index(key));
        }
    }


    #[inductive(initialize)]
    fn init_inductive(post: Self, m: Map<K, V>) { }

    #[inductive(update_key)]
    fn update_key_inductive(pre: Self, post: Self, key: K, new_value: V) {
        assert_maps_equal!(post.fragments, post.auth);
    }
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(auth), Tracked(fragments)) =
            AuthFrag::Instance::initialize(Map::<nat, int>::empty().insert(1nat, 10int));
        let tracked (Tracked(other), Tracked(other_auth), Tracked(mut other_fragments)) =
            AuthFrag::Instance::initialize(Map::<nat, int>::empty().insert(1nat, 10int));
        let tracked fragment = other_fragments.remove(1nat);
        inst.values_agree(1nat, &auth, &fragment);
    }
}

} // verus!
