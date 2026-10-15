//! Small demonstrations of the invariant-completion resource foundation.
//! Verification: verus examples/verified_tsm/algebra.rs
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::*;

verus! {

broadcast use vstd::iset::group_iset_lemmas;

pub struct Count {
    pub amount: nat,
}

impl ResourceAlgebra for Count {
    open spec fn valid(self) -> bool {
        true
    }

    open spec fn op(a: Self, b: Self) -> Self {
        Count { amount: a.amount + b.amount }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl PCM for Count {
    open spec fn unit() -> Self {
        Count { amount: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

pub struct BoundedCounter;

impl Machine for BoundedCounter {
    type Fragment = Count;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        state <= 10
    }

    open spec fn embed(state: nat) -> Count {
        Count { amount: state }
    }
}

/// The caller owns only three of seven counts. The remaining four counts stay
/// valid through an update, and recombine into the resulting six-count state.
proof fn split_update_join() {
    let tracked all = Token::<BoundedCounter>::alloc_state(7);
    let tracked (left, right) = all.split(Count { amount: 3 }, Count { amount: 4 });
    assert(frame_update::<BoundedCounter>(left.fragment(), Count { amount: 2 })) by {
        assert forall|frame: Count, state: nat|
            BoundedCounter::invariant(state) && Count::op(left.fragment(), frame)
                == BoundedCounter::embed(state) implies exists|next: nat|
            BoundedCounter::invariant(next) && Count::op(Count { amount: 2 }, frame)
                == BoundedCounter::embed(next) by {
            let next = 2 + frame.amount;
            assert(BoundedCounter::invariant(next) && Count::op(Count { amount: 2 }, frame)
                == BoundedCounter::embed(next));
        }
    };
    let tracked left = left.update(Count { amount: 2 });
    let tracked all = left.join(right);
    assert(all.fragment().amount == 6);
    all.facts(all.fragment().amount <= 10);
}

/// A nondeterministic update chooses an output compatible with every frame.
proof fn nondeterministic_decrement() {
    let tracked token = Token::<BoundedCounter>::alloc_state(3);
    let outputs = ISet::new(|c: Count| c.amount == 0 || c.amount == 1);
    assert(frame_update_nondeterministic::<BoundedCounter>(token.fragment(), outputs)) by {
        assert forall|frame: Count, state: nat|
            BoundedCounter::invariant(state) && Count::op(token.fragment(), frame)
                == BoundedCounter::embed(state) implies exists|new: Count, next: nat|
            outputs.contains(new) && BoundedCounter::invariant(next) && Count::op(new, frame)
                == BoundedCounter::embed(next) by {
            assert(outputs.contains(Count { amount: 1 }) && BoundedCounter::invariant(
                1 + frame.amount,
            ) && Count::op(Count { amount: 1 }, frame) == BoundedCounter::embed(1 + frame.amount));
        }
    };
    let tracked token = token.update_nondeterministic(outputs);
    assert(token.fragment().amount == 0 || token.fragment().amount == 1);
    token.facts(token.fragment().amount <= 10);
}

/// Shared inputs can remain borrowed across a protocol operation.
proof fn borrowed_input() {
    let tracked all = Token::<BoundedCounter>::alloc_state(7);
    let tracked (mut left, right) = all.split(Count { amount: 3 }, Count { amount: 4 });
    left.validate_2(&right);
    let tracked empty = right.empty();
    assert(empty.fragment().amount == 0 && empty.loc() == right.loc());
    assert(frame_update::<BoundedCounter>(
        Count::op(left.fragment(), right.fragment()),
        Count::op(Count { amount: 2 }, right.fragment()),
    )) by {
        assert forall|frame: Count, state: nat|
            BoundedCounter::invariant(state) && Count::op(
                Count::op(left.fragment(), right.fragment()),
                frame,
            ) == BoundedCounter::embed(state) implies exists|next: nat|
            BoundedCounter::invariant(next) && Count::op(
                Count::op(Count { amount: 2 }, right.fragment()),
                frame,
            ) == BoundedCounter::embed(next) by {
            let next = 6 + frame.amount;
            assert(BoundedCounter::invariant(next) && Count::op(
                Count::op(Count { amount: 2 }, right.fragment()),
                frame,
            ) == BoundedCounter::embed(next));
        }
    };
    let tracked left = left.update_with_shared(&right, Count { amount: 2 });
    assert(right.fragment().amount == 4);
    let tracked all = left.join(right);
    assert(all.fragment().amount == 6);
}

/// The outer unit is valid even if no machine state satisfies the invariant.
pub struct Impossible;

impl Machine for Impossible {
    type Fragment = Count;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        false
    }

    open spec fn embed(state: nat) -> Count {
        Count { amount: state }
    }
}

proof fn empty_machine_has_a_unit() {
    Inved::<Impossible>::unit_valid();
    assert(Inved::<Impossible>::Unit.valid());
    assert(!Inved::<Impossible>::Value(Count { amount: 0 }).valid());
}

pub struct Persistent {
    pub amount: nat,
}

impl ResourceAlgebra for Persistent {
    open spec fn valid(self) -> bool {
        true
    }

    open spec fn op(a: Self, b: Self) -> Self {
        Persistent {
            amount: if a.amount >= b.amount {
                a.amount
            } else {
                b.amount
            },
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl PCM for Persistent {
    open spec fn unit() -> Self {
        Persistent { amount: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

pub struct PersistentCounter;

impl Machine for PersistentCounter {
    type Fragment = Persistent;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        state <= 10
    }

    open spec fn embed(state: nat) -> Persistent {
        Persistent { amount: state }
    }
}

proof fn persistent_duplicate() {
    let tracked token = Token::<PersistentCounter>::alloc_state(5);
    let tracked copy = token.duplicate();
    assert(copy.loc() == token.loc());
    assert(copy.fragment().amount == 5);
    let tracked token = token.join(copy);
    assert(token.fragment().amount == 5);
}

fn main() {
}

} // verus!
