use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::{fragment_included, CountRA, Machine};
use vstd::resource::tsm_storage::*;
verus! {

pub struct Stored;

type Fragment = ProductRA<
    Option<ExclusiveRA<nat>>,
    ProductRA<Option<ExclusiveRA<PointsTo<u64>>>, CountRA>,
>;

impl Machine for Stored {
    type Fragment = Fragment;

    type State = (nat, PointsTo<u64>, bool);

    open spec fn invariant(s: Self::State) -> bool {
        s.0 <= 1 && s.1.value() == 7u64
    }

    open spec fn embed(s: Self::State) -> Fragment {
        ProductRA {
            left: Some(ExclusiveRA::Exclusive(s.0)),
            right: ProductRA {
                left: Some(ExclusiveRA::Exclusive(s.1)),
                right: CountRA {
                    count: if s.2 {
                        1nat
                    } else {
                        0nat
                    },
                },
            },
        }
    }
}

impl StorageMachine for Stored {
    type Key = int;

    type Value = PointsTo<u64>;

    open spec fn storage(s: Self::State) -> IMap<int, PointsTo<u64>> {
        if s.2 {
            IMap::empty().insert(0int, s.1)
        } else {
            IMap::empty()
        }
    }
}

pub open spec fn counter(n: nat) -> Fragment {
    ProductRA {
        left: Some(ExclusiveRA::Exclusive(n)),
        right: ProductRA { left: None, right: CountRA { count: 0 } },
    }
}

pub open spec fn reader(p: PointsTo<u64>, present: bool) -> Fragment {
    ProductRA {
        left: None,
        right: ProductRA {
            left: Some(ExclusiveRA::Exclusive(p)),
            right: CountRA {
                count: if present {
                    1nat
                } else {
                    0nat
                },
            },
        },
    }
}

proof fn change_counter(old: nat, next: nat)
    requires
        old <= 1,
        next <= 1,
    ensures
        frame_exchange::<Stored>(counter(old), IMap::empty(), counter(next), IMap::empty()),
{
    assert forall|frame: Fragment, s: <Stored as Machine>::State|
        Stored::invariant(s) && Fragment::op(counter(old), frame) == Stored::embed(s) implies {
        &&& Stored::storage(s).dom().disjoint(IMap::<int, PointsTo<u64>>::empty().dom())
        &&& IMap::<int, PointsTo<u64>>::empty().submap_of(
            Stored::storage(s).union_prefer_right(IMap::empty()),
        )
        &&& exists|after: <Stored as Machine>::State|
            Stored::invariant(after) && Fragment::op(counter(next), frame) == Stored::embed(after)
                && Stored::storage(after) == Stored::storage(s).union_prefer_right(
                IMap::empty(),
            ).remove_keys(IMap::<int, PointsTo<u64>>::empty().dom())
    } by {
        assert(frame.left is None);
        assert(Fragment::op(counter(next), frame) == Stored::embed((next, s.1, s.2)));
        assert(Stored::storage((next, s.1, s.2)) == Stored::storage(s));
    }
}

proof fn reset_counter(reading: Fragment)
    ensures
        frame_exchange_nondeterministic::<Stored>(
            Fragment::op(counter(1), reading),
            IMap::empty(),
            ISet::new(
                |pair: (Fragment, IMap<int, PointsTo<u64>>)|
                    pair.0 == counter(0) && pair.1 == IMap::<int, PointsTo<u64>>::empty(),
            ).map(
                |pair: (Fragment, IMap<int, PointsTo<u64>>)|
                    (Fragment::op(pair.0, reading), pair.1),
            ),
        ),
{
    let outputs = ISet::new(
        |pair: (Fragment, IMap<int, PointsTo<u64>>)|
            pair.0 == counter(0) && pair.1 == IMap::<int, PointsTo<u64>>::empty(),
    );
    let mapped = outputs.map(
        |pair: (Fragment, IMap<int, PointsTo<u64>>)| (Fragment::op(pair.0, reading), pair.1),
    );
    change_counter(1, 0);
    frame_exchange_with_extra::<Stored>(
        counter(1),
        IMap::empty(),
        counter(0),
        IMap::empty(),
        reading,
    );
    assert forall|frame: Fragment, s: <Stored as Machine>::State|
        Stored::invariant(s) && Fragment::op(Fragment::op(counter(1), reading), frame)
            == Stored::embed(s) implies exists|
        new: Fragment,
        withdraw: IMap<int, PointsTo<u64>>,
        after: <Stored as Machine>::State,
    |
        {
            &&& mapped.contains((new, withdraw))
            &&& Stored::invariant(after)
            &&& Fragment::op(new, frame) == Stored::embed(after)
            &&& Stored::storage(s).dom().disjoint(IMap::<int, PointsTo<u64>>::empty().dom())
            &&& Stored::storage(after).dom().disjoint(withdraw.dom())
            &&& Stored::storage(s).union_prefer_right(IMap::empty()) =~= Stored::storage(
                after,
            ).union_prefer_right(withdraw)
        } by {
        let after = choose|after: <Stored as Machine>::State|
            Stored::invariant(after) && Fragment::op(Fragment::op(counter(0), reading), frame)
                == Stored::embed(after) && Stored::storage(after) == Stored::storage(
                s,
            ).union_prefer_right(IMap::empty()).remove_keys(
                IMap::<int, PointsTo<u64>>::empty().dom(),
            );
        assert(outputs.contains((counter(0), IMap::empty())));
        assert(mapped.contains((Fragment::op(counter(0), reading), IMap::empty())));
        assert(Stored::storage(s) =~= Stored::storage(after).union_prefer_right(IMap::empty()));
    }
}

fn main() {
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let ghost p = permission;
    let tracked mut base = IMap::tracked_empty();
    proof {
        base.tracked_insert(0int, permission);
    }
    let tracked all = StorageToken::<Stored>::alloc_state((0nat, p, true), base);
    let tracked (owner, reading) = all.split(counter(0), reader(p, true));
    let tracked observation = {
        let tracked temporary = reading.observe();
        temporary.join(&temporary).weaken(reader(p, true))
    };
    let tracked overlapping = observation.join(&observation);
    proof {
        overlapping.validate();
        assert(fragment_included::<Stored>(reader(p, true), overlapping.fragment()));
        let frame = choose|frame: Fragment, s: <Stored as Machine>::State|
            Stored::invariant(s) && Fragment::op(overlapping.fragment(), frame) == Stored::embed(s);
        assert(overlapping.fragment().right.right.count == 1);
    }
    let ghost guarded = IMap::empty().insert(0int, p);
    proof {
        Fragment::op_unit(reader(p, true));
    }
    let tracked guard = {
        let tracked temporary = observation.weaken(reader(p, true));
        temporary.guard(guarded)
    };
    proof {
        change_counter(0, 1);
        frame_exchange_with_extra::<Stored>(
            counter(0),
            IMap::empty(),
            counter(1),
            IMap::empty(),
            observation.fragment(),
        );
    }
    let tracked (owner, empty) = owner.exchange_with_observation(
        &observation,
        IMap::tracked_empty(),
        counter(1),
        IMap::empty(),
    );
    assert(empty == IMap::<int, PointsTo<u64>>::empty());
    let before = *cell.borrow(Tracked(guard.tracked_borrow(0int)));
    assert(before == 7);
    let ghost outputs = ISet::new(
        |pair: (Fragment, IMap<int, PointsTo<u64>>)|
            pair.0 == counter(0) && pair.1 == IMap::<int, PointsTo<u64>>::empty(),
    );
    proof {
        reset_counter(observation.fragment());
    }
    let tracked (owner, _) = owner.exchange_nondeterministic_with_observation(
        &observation,
        IMap::tracked_empty(),
        outputs,
    );
    let after = *cell.borrow(Tracked(guard.tracked_borrow(0int)));
    assert(after == 7);
    let tracked all = owner.join(reading);
    proof {
        assert(all.fragment() == Stored::embed((0nat, p, true)));
        assert forall|frame: Fragment, s: <Stored as Machine>::State|
            Stored::invariant(s) && Fragment::op(all.fragment(), frame) == Stored::embed(
                s,
            ) implies {
            &&& Stored::storage(s).dom().disjoint(IMap::<int, PointsTo<u64>>::empty().dom())
            &&& guarded.submap_of(Stored::storage(s).union_prefer_right(IMap::empty()))
            &&& exists|after: <Stored as Machine>::State|
                Stored::invariant(after) && Fragment::op(Stored::embed((0nat, p, false)), frame)
                    == Stored::embed(after) && Stored::storage(after) == Stored::storage(
                    s,
                ).union_prefer_right(IMap::empty()).remove_keys(guarded.dom())
        } by {
            assert(frame.left is None);
            assert(frame.right.left is None);
            assert(s == (0nat, p, true));
            assert(frame.right.right.count == 0);
            assert(Fragment::op(Stored::embed((0nat, p, false)), frame) == Stored::embed(
                (0nat, p, false),
            ));
            assert(Stored::storage(s).union_prefer_right(IMap::empty()).remove_keys(guarded.dom())
                =~= IMap::<int, PointsTo<u64>>::empty());
            assert(Stored::invariant((0nat, p, false)));
            assert(Stored::storage((0nat, p, false)) == Stored::storage(s).union_prefer_right(
                IMap::empty(),
            ).remove_keys(guarded.dom()));
        }
    }
    let tracked (_, mut withdrawn) = all.exchange(
        IMap::tracked_empty(),
        Stored::embed((0nat, p, false)),
        guarded,
    );
    let tracked permission = withdrawn.tracked_remove(0int);
    let value = cell.into_inner(Tracked(permission));
    assert(value == 7);
}

} // verus!
