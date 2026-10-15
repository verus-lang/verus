//! Constants and existential, unowned history alongside an exclusive value.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Adder {
        fields {
            #[sharding(variable)] pub number: int,
            #[sharding(constant)] pub maximum: int,
            #[sharding(not_tokenized)] pub history: int,
        }
        #[invariant] pub fn inv(&self) -> bool {
            0 <= self.number <= self.maximum && self.history == self.number
        }
        init! { initialize(maximum: int) {
            require maximum >= 0;
            init number = 0;
            init maximum = maximum;
            init history = 0;
        } }
        transition! { add(n: int) {
            require 0 <= n;
            require pre.number + n <= pre.maximum;
            update number = pre.number + n;
            update history = pre.history + n;
        } }
        property! { bounded() {
            assert pre.number <= pre.maximum;
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, maximum:int) {}
        #[inductive(add)] fn add_inductive(pre:Self, post:Self, n:int) {}
    }
}

pub proof fn hidden_state_demo() {
    let tracked token = Adder::Protocol::initialize(10);
    let tracked token = Adder::Protocol::add(token, 4);
    let tracked token = Adder::Protocol::bounded(token);
    assert(token.fragment().number->Some_0->Exclusive_0 == 4);
}

/// An executable integer carries the generated token for the same value.
/// The protocol's hidden history stays existential and has no runtime storage.
pub struct RuntimeAdder {
    pub value: u32,
    pub maximum: u32,
    pub token: Tracked<Adder::Token>,
}

impl RuntimeAdder {
    pub open spec fn wf(self) -> bool {
        self.token@.fragment().number == Some(
            vstd::resource::exclusive::ExclusiveRA::Exclusive(self.value as int),
        ) && self.token@.fragment().maximum == Some(
            vstd::resource::agree::AgreementRA::Agree(self.maximum as int),
        )
    }

    pub fn new(maximum: u32) -> (out: Self)
        ensures
            out.wf(),
            out.value == 0,
            out.maximum == maximum,
    {
        let tracked token = Adder::Protocol::initialize(maximum as int);
        Self { value: 0, maximum, token: Tracked(token) }
    }

    pub fn add(self, amount: u32) -> (out: Self)
        requires
            self.wf(),
            self.value as int + amount as int <= self.maximum as int,
        ensures
            out.wf(),
            out.value as int == self.value as int + amount as int,
            out.maximum == self.maximum,
    {
        let tracked token = Adder::Protocol::add(self.token.get(), amount as int);
        Self { value: self.value + amount, maximum: self.maximum, token: Tracked(token) }
    }

    pub fn read(&self) -> (out: u32)
        requires
            self.wf(),
        ensures
            out == self.value,
            out as int <= self.maximum as int,
    {
        proof {
            self.token.borrow().facts(self.value as int <= self.maximum as int);
        }
        self.value
    }
}

fn main() {
    let mut adder = RuntimeAdder::new(10);
    adder = adder.add(4);
    adder = adder.add(3);
    let observed = adder.read();
    assert(observed == 7);
    assert(observed <= 10);
}

} // verus!
