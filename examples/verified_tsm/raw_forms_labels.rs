//! Raw backend statement forms: labeled machines. Init and transition labels
//! are ordinary first parameters of the generated relations and operations.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Labeled {
        fields {
            #[sharding(variable)] pub number: int,
            #[sharding(count)] pub ticks: nat,
        }
        pub struct InitLabel { pub start: int }
        pub enum Label { Add { n: int }, Tick }
        #[invariant] pub fn even(&self) -> bool { self.number % 2 == 0 }
        init! { initialize(label: InitLabel) {
            require(label.start % 2 == 0);
            init number = label.start;
            init ticks = 0;
        } }
        transition! { add(label: Label, n: int) {
            require(label == Label::Add { n } && n % 2 == 0);
            update number = pre.number + n;
        } }
        transition! { tick(label: Label) {
            require(label is Tick);
            add ticks += (1);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel) {}
        #[inductive(add)] fn add_inductive(pre: Self, post: Self, label: Label, n: int) {}
        #[inductive(tick)] fn tick_inductive(pre: Self, post: Self, label: Label) {}
    }
}
proof fn labeled_history() {
    let tracked token = Labeled::Protocol::initialize(Labeled::InitLabel { start: 4 });
    let tracked token = Labeled::Protocol::add(token, Labeled::Label::Add { n: 2 }, 2);
    let tracked token = Labeled::Protocol::tick(token, Labeled::Label::Tick);
    assert(token.fragment().number->Some_0->Exclusive_0 == 6);
}
fn main() {}

} // verus!
