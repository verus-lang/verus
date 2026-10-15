use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  Constant {
    fields {
        #[sharding(constant)] pub limit: int,
        #[sharding(variable)] pub value: int,
    }
    #[invariant] pub fn inv(&self) -> bool { self.value <= self.limit }
    init! { initialize(limit: int) {
        require limit >= 0;
        init limit = limit;
        init value = 0;
    } }
    transition! { set(value: int) {
        require value <= pre.limit;
        update value = value;
    } }
    property! { bound() { assert pre.value <= pre.limit; } }
    #[inductive(initialize)] fn initialize_inductive(post:Self, limit:int) {}
    #[inductive(set)] fn set_inductive(pre:Self, post:Self, value:int) {}
}}

pub struct RuntimeValue {
    pub limit: u32,
    pub value: u32,
    pub instance: Tracked<Constant::Instance>,
    pub token: Tracked<Constant::value>,
}

impl RuntimeValue {
    pub open spec fn wf(self) -> bool {
        self.instance@.limit() == self.limit as int && self.token@.instance_id()
            == self.instance@.id() && self.token@.value() == self.value as int
    }

    pub fn new(limit: u32) -> (out: (Self, Tracked<Constant::Instance>))
        ensures
            out.0.wf(),
            out.0.value == 0,
            out.0.limit == limit,
            out.1@.id() == out.0.token@.instance_id(),
            out.1@.limit() == limit as int,
    {
        let tracked (Tracked(instance), Tracked(token)) = Constant::Instance::initialize(
            limit as int,
        );
        let tracked constant = instance.clone();
        (
            Self { limit, value: 0, instance: Tracked(instance), token: Tracked(token) },
            Tracked(constant),
        )
    }

    pub fn set(self, value: u32) -> (out: Self)
        requires
            self.wf(),
            value <= self.limit,
        ensures
            out.wf(),
            out.limit == self.limit,
            out.value == value,
            out.token@.instance_id() == self.token@.instance_id(),
    {
        let tracked mut token = self.token.get();
        proof {
            self.instance.borrow().set(value as int, &mut token);
        }
        Self { limit: self.limit, value, instance: self.instance, token: Tracked(token) }
    }

    pub fn read(&self) -> (out: u32)
        requires
            self.wf(),
        ensures
            out == self.value,
            out <= self.limit,
    {
        proof {
            self.instance.borrow().bound(self.token.borrow());
        }
        self.value
    }
}

fn main() {
    let (mut value, Tracked(constant)) = RuntimeValue::new(10);
    value = value.set(9);
    let observed = value.read();
    assert(observed == 9);
    assert(constant.id() == value.token@.instance_id());
    assert(constant.limit() == 10);
    value = value.set(3);
    let observed = value.read();
    assert(observed == 3);
    assert(constant.limit() == 10);
}

} // verus!
