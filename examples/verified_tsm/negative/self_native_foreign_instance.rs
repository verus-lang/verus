// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(variable)]
        pub x: int,

        #[sharding(variable)]
        pub recursing: Option<Box<Self>>,
    }

    init!{
        ini(t: Self) {
            let r: Self = t;
            init x = r.x;
            init recursing = t.recursing;
        }
    }

    pub open spec fn add1(x: int) -> int {
        x + 1
    }

    transition!{
        tr(a: int) {
            update x = Self::add1(a);
        }
    }

    transition!{
        tr2(y: Option<Box<Self>>) {
            let t: Option<Box<Self>> = y;
            update recursing = t;
        }
    }

    transition!{
        tr3() {
            update recursing = Option::<Box<Self>>::None;
        }
    }

}}

verus! {

pub proof fn foo() {
    let tracked (Tracked(inst), Tracked(mut x_tok), Tracked(mut r_tok)) = Y::Instance::ini(
        Y::State { x: 5, recursing: Option::None },
    );
    inst.tr(19, &mut x_tok);
    assert(x_tok.value() == 20);

    inst.tr2(Option::<Box<Y::State>>::None, &mut r_tok);
    assert(equal(Option::<Box<Y::State>>::None, r_tok.value()));

    inst.tr3(&mut r_tok);
    assert(equal(Option::<Box<Y::State>>::None, r_tok.value()));
}

} // verus!
verus! {

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut x_tok), Tracked(mut r_tok)) = Y::Instance::ini(
            Y::State { x: 5, recursing: Option::None },
        );
        let tracked (Tracked(other_inst), Tracked(other_x_tok), Tracked(mut other_r_tok)) =
            Y::Instance::ini(Y::State { x: 5, recursing: Option::None });
        inst.tr2(Option::<Box<Y::State>>::None, &mut other_r_tok);
    }
}

} // verus!
