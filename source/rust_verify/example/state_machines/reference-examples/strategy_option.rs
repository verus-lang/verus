#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::modes::*;
use vstd::option::*;
use vstd::{pervasive::*, *};

use state_machines_macros::tokenized_state_machine;

verus! {

// ANCHOR: full
tokenized_state_machine!{ State {
    fields {
        #[sharding(variable)]
        pub token_exists: bool,

        #[sharding(option)]
        pub field: Option<int>,
    }

    #[invariant]
    pub fn token_exists_correct(&self) -> bool {
        self.token_exists <==> self.field.is_Some()
    }

    init!{
        initialize(v: int) {
            init field = Option::Some(v);
            init token_exists = true;
        }
    }

    transition!{
        add_token(v: int) {
            require !pre.token_exists;
            update token_exists = true;

            add field += Some(v);
        }
    }

    transition!{
        remove_token() {
            remove field -= Some(let _);

            assert pre.token_exists;
            update token_exists = false;
        }
    }

    transition!{
        have_token() {
            have field >= Some(let _);

            assert pre.token_exists;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, v: int) { }

    #[inductive(add_token)]
    fn add_token_inductive(pre: Self, post: Self, v: int) { }

    #[inductive(remove_token)]
    fn remove_token_inductive(pre: Self, post: Self) { }

    #[inductive(have_token)]
    fn have_token_inductive(pre: Self, post: Self) { }
}}

proof fn option_example() {
    #[verifier::proof]
    let (Tracked(instance), Tracked(mut token_exists), Tracked(token_opt)) =
        State::Instance::initialize(5);
    #[verifier::proof]
    let token = token_opt.tracked_unwrap();
    assert(token@.value == 5);
    instance.have_token(&token_exists, &token);
    assert(token_exists@.value == true);
    instance.remove_token(&mut token_exists, token);  // consumes token
    assert(token_exists@.value == false);  // updates token_exists to `false`
    #[verifier::proof]
    let token = instance.add_token(19, &mut token_exists);
    assert(token_exists@.value == true);  // updates token_exists to `true`
    assert(token@.value == 19);  // new token has value 19
}

// ANCHOR_END: full
fn main() {
}

} // verus!
