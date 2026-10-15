// EXPECTED-ERROR: verified effect bindings must precede modifications of their source field
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
BoundAfterReplacement {
    fields {
        #[sharding(imap)] pub entries: IMap<int, nat>,
        #[sharding(option)] pub output: Option<nat>,
    }
    init! { initialize() {
        init entries = IMap::empty().insert(0int, 1nat);
        init output = None;
    } }
    transition! { replace_then_bind() {
        remove entries -= [0int => 1nat];
        add entries += [0int => 2nat];
        have entries >= [0int => let selected];
        add output += Some(selected);
    } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(replace_then_bind)] fn replace_then_bind_inductive(pre: Self, post: Self) {}
});

} // verus!
fn main() {}
