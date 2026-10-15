// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::*;
verus! {

pub struct Boolean;

impl Machine for Boolean {
    type Fragment = CountRA;

    type State = bool;

    open spec fn invariant(state: bool) -> bool {
        true
    }

    open spec fn embed(state: bool) -> CountRA {
        CountRA {
            count: if state {
                1nat
            } else {
                0nat
            },
        }
    }
}

pub struct Pair;

impl Machine for Pair {
    type Fragment = ProductRA<Option<ExclusiveRA<nat>>, CountRA>;

    type State = (nat, bool);

    open spec fn invariant(state: Self::State) -> bool {
        state.0 <= 1 && state.1
    }

    open spec fn embed(state: Self::State) -> Self::Fragment {
        ProductRA {
            left: Some(ExclusiveRA::Exclusive(state.0)),
            right: CountRA {
                count: if state.1 {
                    1nat
                } else {
                    0nat
                },
            },
        }
    }
}

fn main() {
    proof {
        let tracked all = Token::<Pair>::alloc_state((0nat, true));
        let current = ProductRA {
            left: Some(ExclusiveRA::Exclusive(0nat)),
            right: CountRA { count: 0 },
        };
        let reading = ProductRA { left: None, right: CountRA { count: 1 } };
        let tracked (counter, reader) = all.split(current, reading);
        let tracked observation = reader.observe();
        let bad = ProductRA {
            left: Some(ExclusiveRA::Exclusive(2nat)),
            right: CountRA { count: 0 },
        };
        let tracked counter = counter.update_with_observation(&observation, bad);
    }
}

} // verus!
