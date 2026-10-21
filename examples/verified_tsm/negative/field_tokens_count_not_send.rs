// EXPECTED-ERROR: cannot be sent between threads safely
// Checked-only soundness negative: a `count` token of a machine over a `!Send` type
// (`Rc<u64>`, here only the type of a constant) is `!Send`. (The trusted macro's
// tokens are unconditionally `Send` and accept this program.)
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::thread::*;
verus! {

verified_tokenized_state_machine! {
    GenericCount<T> {
        fields {
            #[sharding(constant)] pub value: T,
            #[sharding(count)] pub input: nat,
        }
        init!{ initialize(value: T) { init value = value; init input = 1; } }
    }
}

fn main() {
    let ghost value = arbitrary::<std::rc::Rc<u64>>();
    let tracked (Tracked(_instance), Tracked(input)) =
        GenericCount::Instance::<std::rc::Rc<u64>>::initialize(value);
    let _handle = spawn(
        move || -> (result: Tracked<GenericCount::input<std::rc::Rc<u64>>>) { Tracked(input) },
    );
}

} // verus!
