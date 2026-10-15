//! Agreement tokens duplicate by an idempotence proof, while mutable values
//! stay exclusive. Duplication uses the generic verified Token operation.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Constant {
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
        #[inductive(initialize)] fn initialize_inductive(post:Self, limit:int) {}
        #[inductive(set)] fn set_inductive(pre:Self, post:Self, value:int) {}
    }
}

pub proof fn duplicate_constant_demo() {
    use vstd::resource::agree::AgreementRA;
    use vstd::resource::exclusive::ExclusiveRA;
    let tracked all = Constant::Protocol::initialize(10);
    let c = Constant::Fragment { limit: Some(AgreementRA::Agree(10int)), value: None };
    let v = Constant::Fragment { limit: None, value: Some(ExclusiveRA::Exclusive(0int)) };
    let tracked (constant, value) = all.split(c, v);
    let tracked copy = constant.duplicate();
    let tracked owned = copy.join(value);
    let tracked owned = Constant::Protocol::set(owned, 9);
    // Another copy retains the same agreed constant after the mutable update.
    assert(constant.fragment().limit->Some_0->Agree_0 == 10);
    assert(owned.fragment().value->Some_0->Exclusive_0 == 9);
}

pub struct RuntimeValue {
    pub limit: u32,
    pub value: u32,
    pub token: Tracked<Constant::Token>,
}

impl RuntimeValue {
    pub open spec fn wf(self) -> bool {
        self.token@.fragment().limit == Some(
            vstd::resource::agree::AgreementRA::Agree(self.limit as int),
        ) && self.token@.fragment().value == Some(
            vstd::resource::exclusive::ExclusiveRA::Exclusive(self.value as int),
        )
    }

    /// Retain a separate agreed limit while the runtime object owns its value.
    pub fn new(limit: u32) -> (out: (Self, Tracked<Constant::Token>))
        ensures
            out.0.wf(),
            out.0.value == 0,
            out.0.limit == limit,
            out.1@.loc() == out.0.token@.loc(),
            out.1@.fragment().limit == Some(
                vstd::resource::agree::AgreementRA::Agree(limit as int),
            ),
            out.1@.fragment().value is None,
    {
        use vstd::resource::agree::AgreementRA;
        use vstd::resource::exclusive::ExclusiveRA;
        let tracked all = Constant::Protocol::initialize(limit as int);
        let ghost constant = Constant::Fragment {
            limit: Some(AgreementRA::Agree(limit as int)),
            value: None,
        };
        let ghost value = Constant::Fragment {
            limit: None,
            value: Some(ExclusiveRA::Exclusive(0int)),
        };
        let tracked (constant, value) = all.split(constant, value);
        let tracked owned = constant.duplicate().join(value);
        (Self { limit, value: 0, token: Tracked(owned) }, Tracked(constant))
    }

    pub fn set(self, value: u32) -> (out: Self)
        requires
            self.wf(),
            value <= self.limit,
        ensures
            out.wf(),
            out.limit == self.limit,
            out.value == value,
            out.token@.loc() == self.token@.loc(),
    {
        let tracked token = Constant::Protocol::set(self.token.get(), value as int);
        Self { limit: self.limit, value, token: Tracked(token) }
    }

    pub fn read(&self) -> (out: u32)
        requires
            self.wf(),
        ensures
            out == self.value,
            out <= self.limit,
    {
        proof {
            self.token.borrow().facts(self.value as int <= self.limit as int);
        }
        self.value
    }
}

fn main() {
    let (mut value, Tracked(constant)) = RuntimeValue::new(10);
    value = value.set(9);
    let observed = value.read();
    assert(observed == 9);
    assert(constant.loc() == value.token@.loc());
    assert(constant.fragment().limit->Some_0->Agree_0 == 10);
    value = value.set(3);
    let observed = value.read();
    assert(observed == 3);
    assert(constant.fragment().limit->Some_0->Agree_0 == 10);
}

} // verus!
