//! Native field tokens travel separately through an existing atomic invariant.
#[path = "counting_to_2.rs"]
mod counting_protocol;

use counting_protocol::X;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

pub struct CounterPredicate;

impl AtomicInvariantPredicate<Loc, u32, X::counter> for CounterPredicate {
    open spec fn atomic_inv(instance: Loc, v: u32, g: X::counter) -> bool {
        g.instance_id() == instance && g.value() == v as int
    }
}

pub type Counter = AtomicU32<Loc, X::counter, CounterPredicate>;

pub fn increment_a(
    atomic: &Counter,
    Tracked(instance): Tracked<&X::Instance>,
    Tracked(token): Tracked<X::inc_a>,
) -> (new_token: Tracked<X::inc_a>)
    requires
        atomic.well_formed(),
        atomic.constant() == instance.id(),
        token.instance_id() == instance.id(),
        !token.value(),
    ensures
        new_token@.instance_id() == instance.id(),
        new_token@.value(),
{
    let tracked mut token = token;
    atomic_with_ghost!(atomic => fetch_add(1);
        ghost c => {
            instance.increment_will_not_overflow_u32(&c);
            instance.tr_inc_a(&mut c, &mut token);
        }
    );
    Tracked(token)
}

pub fn demo() {
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
    ) = X::Instance::initialize();
    let atomic = Counter::new(Ghost(instance.id()), 0, Tracked(counter_token));
    let new_token = increment_a(&atomic, Tracked(&instance), Tracked(inc_a_token));
    let (v, Tracked(c)) = atomic.into_inner();
    proof {
        let tracked new_token = new_token.get();
        c.borrow_token().facts_3(
            new_token.borrow_token(),
            inc_b_token.borrow_token(),
            c.value() == 1,
        );
    }
    assert(c.value() == 1);
    assert(v == 1);
}

} // verus!
fn main() {
    demo();
}
