// EXPECTED-ERROR: use of moved value
#![allow(non_snake_case)]
use std::marker::PhantomData;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

pub const MAX_PCPU_COUNT: usize = 64;

pub open spec fn wrapping_add(x: u32, y: u32) -> u32 {
    if x + y > u32::MAX {
        (x + y - (u32::MAX + 1)) as u32
    } else {
        (x + y) as u32
    }
}

// Sanity check our definition above
pub broadcast proof fn wrapping_add_ensures(x: u32, y: u32)
    ensures
        #[trigger] wrapping_add(x, y) == (x + y) % 0x1_0000_0000,
{
}

pub open spec fn count<T>(o: Option<T>) -> int {
    match o {
        Option::Some(_) => 1,
        Option::None => 0,
    }
}

verified_tokenized_state_machine!(

MutexToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        // The constant portion of the invariant we maintain about the stored value
        #[sharding(constant)]
        pub k : K,

        // Placeholder for the invariant we maintain about the store variable
        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        // Regulate how many threads can access the mutex at one time
        #[sharding(count)]
        pub mutex_access: nat,

        // Model of the atomic that's issuing tickets
        #[sharding(variable)]
        pub next_ticket: u32,

        // Model of the atomic that controls lock acquisition
        #[sharding(variable)]
        pub now_serving: u32,

        // Threads holding a ticket and waiting to enter
        #[sharding(set)]
        pub waiters: Set<u32>,

        // When the lock is held by a thread, this tells us which ticket that thread used to enter
        #[sharding(option)]
        pub locked: Option<u32>,

        // The value protected by the lock
        #[sharding(storage_option)]
        pub val: Option<V>,

        // Working in single-threaded mode
        #[sharding(variable)]
        pub single_threaded: bool,

        // Values of the ticket counters
        #[sharding(option)]
        pub single_values: Option<(u32, u32)>,
    }

    #[invariant]
    pub fn next_ticket(&self) -> bool {
        &&& self.next_ticket == (self.now_serving + self.waiters.len() + count(self.locked)) % 0x1_0000_0000
    }

    #[invariant]
    pub fn waiters_bound(&self) -> bool {
        self.waiters.len() + count(self.locked) + self.mutex_access == MAX_PCPU_COUNT
    }

    #[invariant]
    pub fn serving(&self) -> bool {
        self.waiters.contains(self.now_serving) ==> self.val.is_some()
    }

    #[invariant]
    pub fn valid_v(&self) -> bool {
        self.val matches Some(v) ==> Pred::inv(self.k, v)
    }

    #[invariant]
    pub fn locked(&self) -> bool {
        self.locked.is_some() <==> self.val.is_none()
    }

    #[invariant]
    pub fn locked_val(&self) -> bool {
        self.locked matches Some(v) ==> v == self.now_serving
    }

    #[invariant]
    pub fn waiters(&self) -> bool {
        if self.now_serving <= self.next_ticket {
            &&& forall |i:u32| i < self.now_serving || i >= self.next_ticket ==> !self.waiters.contains(i)
            &&& forall |i| self.now_serving + 1 <= i < self.next_ticket ==> self.waiters.contains(i)
        } else {
            &&& forall |i:u32| i > self.now_serving || i < self.next_ticket ==> self.waiters.contains(i)
            &&& forall |i| self.next_ticket <= i < self.now_serving ==> !self.waiters.contains(i)
        }
    }

    #[invariant]
    pub fn mutex_access_bound(&self) -> bool {
        self.mutex_access <= MAX_PCPU_COUNT
    }

    #[invariant]
    pub fn single_threaded(&self) -> bool {
        &&& self.single_threaded ==> self.mutex_access == MAX_PCPU_COUNT && (self.single_values matches Some((next, now)) && next == self.next_ticket && now == self.now_serving && next == now)
        &&& !self.single_threaded <==> self.single_values is None
        &&& self.mutex_access < MAX_PCPU_COUNT ==> !self.single_threaded
    }

    property! {
        locked_value_is_now_serving(n: u32) {
            have locked >= Some(n);
            assert(pre.now_serving == n);
        }
    }

    init! {
        new(k: K, v: V) {
            require Pred::inv(k, v);
            init k = k;
            init pred = PhantomData;
            init mutex_access = MAX_PCPU_COUNT as nat;
            init next_ticket = 0;
            init now_serving = 0;
            init waiters = Set::empty();
            init locked = None;
            init val = Some(v);
            init single_threaded = false;
            init single_values = None;
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self, k: K, v: V) {
    }

    transition! {
        take_ticket() {
            require(!pre.single_threaded);
            remove mutex_access -= (1);
            update next_ticket = wrapping_add(pre.next_ticket, 1);
            birds_eye let ticket = pre.next_ticket;
            add waiters += set { ticket };
            assert(ticket == pre.next_ticket);
        }
    }

    #[inductive(take_ticket)]
    fn take_ticket_inductive(pre:Self, post: Self) {
    }

    transition! {
        acquire(t: u32) {
            require t == pre.now_serving;
            remove waiters -= set { t };
            add locked += Some(t);
            birds_eye let v = pre.val->0;
            withdraw val -= Some(v);
            assert Pred::inv(pre.k, v);
        }
    }

    #[inductive(acquire)]
    fn acquire_inductive(pre:Self, post: Self, t: u32) {
    }

    transition! {
        release(v: V, n: u32) {
            require Pred::inv(pre.k, v);
            remove locked -= Some(n);
            deposit val += Some(v);
            update now_serving = wrapping_add(pre.now_serving, 1);
            add mutex_access += (1);
        }
    }

    #[inductive(release)]
    fn release_inductive(pre:Self, post: Self, v: V, n: u32) {
    }

    transition! {
        enter_single_threaded() {
            require(!pre.single_threaded);
            have mutex_access >= (MAX_PCPU_COUNT as nat);
            birds_eye let next = pre.next_ticket;
            birds_eye let now = pre.now_serving;
            add single_values += Some((now, next));
            update single_threaded = true;
        }
    }

    #[inductive(enter_single_threaded)]
    fn enter_single_threaded_inductive(pre:Self, post: Self) {
    }

    transition! {
        exit_single_threaded(now: u32, next: u32) {
            require(pre.single_threaded);
            update single_threaded = false;
            remove single_values -= Some((now, next));
        }
    }

    #[inductive(exit_single_threaded)]
    fn exit_single_threaded_inductive(pre:Self, post: Self, now: u32, next: u32) {
    }

    property! {
        single_threaded_now(now: u32, next: u32) {
            require(pre.single_threaded);
            have single_values >= Some((now, next));
            assert(next == pre.now_serving && now == next);
        }
    }

    property! {
        single_threaded_next(now: u32, next: u32) {
            require(pre.single_threaded);
            have single_values >= Some((now, next));
            assert(now == pre.next_ticket && now == next);
        }
    }
});

} // verus!
use vstd::cell::pcell_maybe_uninit as cell;
verus! {

struct CellPred;

impl InvariantPredicate<vstd::cell::CellId, cell::PointsTo<usize>> for CellPred {
    open spec fn inv(k: vstd::cell::CellId, v: cell::PointsTo<usize>) -> bool {
        v.id() == k && v.is_init() && v.value() == 7
    }
}

fn main() {
    let (cell, Tracked(permission)) = cell::PCell::new(7usize);
    let tracked (
        Tracked(instance),
        Tracked(mut mutex_access),
        Tracked(mut next_ticket),
        Tracked(mut now_serving),
        Tracked(waiters),
        Tracked(locked),
        Tracked(mut single_threaded),
        Tracked(single_values),
    ) = MutexToks::Instance::<vstd::cell::CellId, cell::PointsTo<usize>, CellPred>::new(
        cell.id(),
        permission,
        Some(permission),
    );
    let tracked access = mutex_access.split(1);
    proof {
        mutex_access.join(access);
        mutex_access.join(access);
    }
}

} // verus!
