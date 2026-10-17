//! Labeled machines on the generic interface. Init and transition labels are
//! ordinary first parameters of the generated relations, so the generated
//! operations take them as their first arguments, as in the raw interface
//! (`raw_forms_labels.rs`). Labels may have the machine's type parameters.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
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
        property! { even_now(label: Label) {
            assert(pre.number % 2 == 0);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel) {}
        #[inductive(add)] fn add_inductive(pre: Self, post: Self, label: Label, n: int) {}
        #[inductive(tick)] fn tick_inductive(pre: Self, post: Self, label: Label) {}
    }
}

verified_tokenized_state_machine! {
    Cell<T> {
        fields {
            #[sharding(option)] pub owner: Option<T>,
            #[sharding(storage_option)] pub cell: Option<T>,
        }
        pub struct InitLabel<T> { pub v: T }
        pub enum Label<T> { Take { v: T }, Peek }
        #[invariant] pub fn same(&self) -> bool { self.cell == self.owner }
        init! { initialize(label: InitLabel<T>) {
            init owner = Some(label.v);
            init cell = Some(label.v);
        } }
        transition! { take(label: Label<T>, v: T) {
            require(label == Label::Take { v });
            remove owner -= Some(v);
            withdraw cell -= Some(v);
        } }
        property! { peek(label: Label<T>, v: T) {
            require(label is Peek);
            have owner >= Some(v);
            guard cell >= Some(v);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel<T>) {}
        #[inductive(take)] fn take_inductive(pre: Self, post: Self, label: Label<T>, v: T) {}
    }
}
verus! {

proof fn labeled_client() {
    let tracked (Tracked(inst), Tracked(number), Tracked(ticks)) = Labeled::Instance::initialize(Labeled::InitLabel { start: 4 });
    let tracked mut number = number;
    inst.add(Labeled::Label::Add { n: 2 }, 2, &mut number);
    assert(number.value() == 6);
    let tracked t = inst.tick(Labeled::Label::Tick);
    assert(t.count() == 1);
    inst.even_now(Labeled::Label::Tick, &number);
}

proof fn cell_client<T>(tracked x: T) {
    let ghost v = x;
    let tracked (Tracked(inst), Tracked(owner)) = Cell::Instance::<T>::initialize(Cell::InitLabel { v }, Some(x));
    let tracked o = owner.tracked_unwrap();
    let tracked g = inst.peek(Cell::Label::Peek, v, &o);
    assert(*g == v);
    let tracked y = inst.take(Cell::Label::Take { v }, v, o);
    assert(y == v);
}
}

fn main() {}
