#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{pervasive::*, *};
verus! {

verified_tokenized_state_machine!{  AuthFrag<#[verifier::reject_recursive_types] __tsm_authority_map_pre, __tsm_authority_map_point> {
    fields {
        #[sharding(variable)]
        pub auth: Map<__tsm_authority_map_pre, __tsm_authority_map_point>,

        #[sharding(map)]
        pub fragments: Map<__tsm_authority_map_pre, __tsm_authority_map_point>,
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.fragments == self.auth
    }

    init!{
        initialize(m: Map<__tsm_authority_map_pre, __tsm_authority_map_point>) {
            init auth = m;
            init fragments = m;
        }
    }

    transition!{
        update_key(__tsm_authority_map_before: __tsm_authority_map_pre, __tsm_authority_map_entry: __tsm_authority_map_point) {
            update auth = pre.auth.insert(__tsm_authority_map_before, __tsm_authority_map_entry);

            remove fragments -= [ __tsm_authority_map_before => let _ ];
            add fragments += [ __tsm_authority_map_before => __tsm_authority_map_entry ];
        }
    }

    property!{
        values_agree(__tsm_authority_map_before: __tsm_authority_map_pre) {
            have fragments >= [ __tsm_authority_map_before => let frag_value ];
            assert(pre.auth.dom().contains(__tsm_authority_map_before)
                && frag_value == pre.auth.index(__tsm_authority_map_before));
        }
    }


    #[inductive(initialize)]
    fn init_inductive(post: Self, m: Map<__tsm_authority_map_pre, __tsm_authority_map_point>) { }

    #[inductive(update_key)]
    fn update_key_inductive(pre: Self, post: Self, __tsm_authority_map_before: __tsm_authority_map_pre, __tsm_authority_map_entry: __tsm_authority_map_point) {
        assert_maps_equal!(post.fragments, post.auth);
    }
}}

proof fn alias_type(tracked fragments: AuthFrag::fragments_map<nat, int>) {
}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut auth), Tracked(mut fragments)) =
            AuthFrag::Instance::initialize(Map::<nat, int>::empty().insert(1nat, 10int));
        let tracked fragment = fragments.remove(1nat);
        inst.values_agree(1nat, &auth, &fragment);
        inst.values_agree(1nat, &auth, &fragment);
        let tracked fragment = inst.update_key(1nat, 20int, &mut auth, fragment);
        inst.values_agree(1nat, &auth, &fragment);
        assert(auth.value() == Map::<nat, int>::empty().insert(1nat, 20int));
        fragments.insert(fragment);
        assert(fragments.map() == auth.value());
        alias_type(fragments);
    }
}

} // verus!
