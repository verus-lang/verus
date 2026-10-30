// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) {
                    match x {
                        Option::Some(x1) => {
                            require w;
                            update m[0] = x1;
                        }
                        Option::None => {
                            assert y by { assume(false); };
                            update a = 99;
                        }
                    }

                    assert z by { assume(false); };

                    match v {
                        Option::Some(v1) => {
                            update b = v1;
                        }
                        Option::None => {
                            update m[1] = 11;
                        }
                    }
                }
            }
        }}

proof fn weak_is_insufficient() {
    let pre = X::State { m: IMap::empty(), a: 0int, b: 0int };
    assert(X::State::tr_enabled(pre, None, false, false, false, None));
    let post = X::take_step::tr(pre, None, false, false, false, None);
}

fn main() {
}

} // verus!
