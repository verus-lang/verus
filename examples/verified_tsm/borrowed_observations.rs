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
        {
            let tracked token = Token::<Boolean>::alloc_state(true);
            let tracked observation = {
                let tracked temporary = token.observe();
                let tracked merged = temporary.join(&temporary);
                merged.weaken(CountRA { count: 1 })
            };
            let tracked aliased = observation.join(&observation);
            let tracked repeated = aliased.join(&observation).join(&observation);
            repeated.validate();
            assert(fragment_included::<Boolean>(CountRA { count: 1 }, repeated.fragment()));
            let frame = choose|frame: CountRA, state: bool|
                Boolean::invariant(state) && CountRA::op(repeated.fragment(), frame)
                    == Boolean::embed(state);
            assert(repeated.fragment().count == 1);
            token.validate();
        }
        {
            let tracked all = Token::<Pair>::alloc_state((0nat, true));
            let current = ProductRA {
                left: Some(ExclusiveRA::Exclusive(0nat)),
                right: CountRA { count: 0 },
            };
            let reading = ProductRA { left: None, right: CountRA { count: 1 } };
            let tracked (counter, reader) = all.split(current, reading);
            let tracked observation = reader.observe();
            let tracked observation = observation.join(&observation);
            let tracked observation = observation.weaken(reading);
            assert(observation.fragment() == reading);
            let next = ProductRA {
                left: Some(ExclusiveRA::Exclusive(1nat)),
                right: CountRA { count: 0 },
            };
            assert(frame_update::<Pair>(
                ProductRA::op(current, observation.fragment()),
                ProductRA::op(next, observation.fragment()),
            )) by {
                assert forall|z: <Pair as Machine>::Fragment, state: <Pair as Machine>::State|
                    Pair::invariant(state) && ProductRA::op(
                        ProductRA::op(current, observation.fragment()),
                        z,
                    ) == Pair::embed(state) implies exists|post: <Pair as Machine>::State|
                    Pair::invariant(post) && ProductRA::op(
                        ProductRA::op(next, observation.fragment()),
                        z,
                    ) == Pair::embed(post) by {
                    let post = (1nat, state.1);
                    assert(Pair::invariant(post));
                    assert(ProductRA::op(ProductRA::op(next, observation.fragment()), z)
                        == Pair::embed(post));
                }
            }
            let tracked counter = counter.update_with_observation(&observation, next);
            assert(counter.fragment() == next);
            observation.validate();
            assert(frame_update_nondeterministic::<Pair>(
                ProductRA::op(next, observation.fragment()),
                ISet::new(|new: <Pair as Machine>::Fragment| new == current).map(
                    |new: <Pair as Machine>::Fragment| ProductRA::op(new, observation.fragment()),
                ),
            )) by {
                assert forall|z: <Pair as Machine>::Fragment, state: <Pair as Machine>::State|
                    Pair::invariant(state) && ProductRA::op(
                        ProductRA::op(next, observation.fragment()),
                        z,
                    ) == Pair::embed(state) implies exists|
                    new: <Pair as Machine>::Fragment,
                    post: <Pair as Machine>::State,
                |
                    ISet::new(|new: <Pair as Machine>::Fragment| new == current).map(
                        |new: <Pair as Machine>::Fragment|
                            ProductRA::op(new, observation.fragment()),
                    ).contains(new) && Pair::invariant(post) && ProductRA::op(new, z)
                        == Pair::embed(post) by {
                    let post = (0nat, state.1);
                    let combined = ProductRA::op(current, observation.fragment());
                    assert(Pair::invariant(post));
                    assert(ProductRA::op(combined, z) == Pair::embed(post));
                    assert(ISet::new(|new: <Pair as Machine>::Fragment| new == current).contains(
                        current,
                    ));
                }
            }
            let tracked counter = counter.update_nondeterministic_with_observation(
                &observation,
                ISet::new(|new: <Pair as Machine>::Fragment| new == current),
            );
            assert(counter.fragment() == current);
            assert(reader.fragment() == reading);
            let tracked all = counter.join(reader);
            all.validate();
        }
    }
}

} // verus!
