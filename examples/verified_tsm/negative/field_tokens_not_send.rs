// EXPECTED-ERROR: cannot be sent between threads safely
// Checked-only soundness negative: the token of a `variable` field of a machine over
// a `!Send` type (`Rc<u64>`) is `!Send`, so it cannot move to another thread. (The
// trusted macro's tokens are unconditionally `Send` and accept this program.)
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::thread::*;
verus! {

verified_tokenized_state_machine!(
    Generic<T> {
        fields { #[sharding(variable)] pub item: T, }
        init!{ initialize(item: T) { init item = item; } }
    }
);

fn main() {
    let tracked (Tracked(_instance), Tracked(item)) =
        Generic::Instance::<std::rc::Rc<u64>>::initialize(arbitrary());
    let _handle = spawn(
        move || -> (result: Tracked<Generic::item<std::rc::Rc<u64>>>) { Tracked(item) },
    );
}

} // verus!
