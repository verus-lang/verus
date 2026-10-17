// EXPECTED-ERROR: error: precondition not satisfied
#![allow(non_snake_case)]
#[path = "/local/home/schoeped/.workspace/src/Noether/AwsArgLlcrtNice/theories/verus/concurrency/src/vstd_ext.rs"]
mod vstd_ext;
mod ticket_lock_proofs {
    use vstd::prelude::*;
    verus! {

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

} // verus!
}

use crate::ticket_lock_proofs::{wrapping_add, wrapping_add_ensures};
use crate::vstd_ext::{insert_many, insert_many_properties};
use std::marker::PhantomData;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::invariant::InvariantPredicate;
use vstd::multiset::*;
use vstd::prelude::*;

verus! {

pub const MAX_PCPU_COUNT: usize = 64;

broadcast use wrapping_add_ensures;

pub open spec fn wrapping_add_u24(x: u32, y: u32) -> u32 {
    if x + y > 0xFF_FFFF {
        (x + y - 0x100_0000) as u32
    } else {
        (x + y) as u32
    }
}

// Sanity check our definition above
pub broadcast proof fn wrapping_add_u24_ensures(x: u32, y: u32)
    requires
        x < 0x100_0000 && y < 0x100_0000,
    ensures
        #[trigger] wrapping_add_u24(x, y) == (x + y) % 0x100_0000,
{
}

pub open spec fn countb(b: bool) -> int {
    if b {
        1
    } else {
        0
    }
}

#[derive(Structural, PartialEq)]
pub enum WriterPhase {
    Even,
    Odd,
}

impl WriterPhase {
    pub open spec fn opposite(&self) -> WriterPhase {
        use WriterPhase::*;
        match self {
            Even => Odd,
            Odd => Even,
        }
    }
}

proof fn multiset_len_sums_counts_writerphase(m: Multiset<WriterPhase>)
    ensures
        m.len() == m.count(WriterPhase::Even) + m.count(WriterPhase::Odd),
{
    use WriterPhase::*;
    let e = Multiset::empty();
    let m_even = insert_many(e, Even, m.count(Even));
    let m_new = insert_many(m_even, Odd, m.count(Odd));
    insert_many_properties(e, Even, m.count(Even));
    insert_many_properties(m_even, Odd, m.count(Odd));
    assert(m_new == m);
}

#[derive(Structural, PartialEq)]
pub enum Phase {
    Reader,
    WriterPresent(WriterPhase),
}

impl Phase {
    pub open spec fn new_writer(n: u32) -> Self {
        use WriterPhase::*;
        Phase::WriterPresent(
            if n % 2 == 0 {
                Even
            } else {
                Odd
            },
        )
    }
}

#[derive(Structural, PartialEq)]
pub enum WriterState {
    // A writer has reached the head of the writer queue (with writer ticket number t)
    Pending(u32),
    // A writer has signaled the readers and is waiting for active/ignorant readers to drain
    // It holds (reader_ticket, writer_ticket) and will complete when rout is reader_ticket)
    Draining(u32, u32),
    // A writer has obtained the lock (with writer ticket number t)
    Writing(u32),
    // A writer is exiting (with writer ticket number t), but hasn't incremented wout yet
    Exiting(u32),
}

pub open spec fn absent(s: Option<WriterState>) -> bool {
    s is None
}

pub open spec fn pending(s: Option<WriterState>) -> bool {
    s matches Some(WriterState::Pending(_))
}

pub open spec fn draining(s: Option<WriterState>) -> bool {
    s matches Some(WriterState::Draining(_, _))
}

pub open spec fn writing(s: Option<WriterState>) -> bool {
    s matches Some(WriterState::Writing(_))
}

pub open spec fn exiting(s: Option<WriterState>) -> bool {
    s matches Some(WriterState::Exiting(_))
}

verified_tokenized_state_machine!(

#[verified_local_ready(writer_take_ticket,writer_acquire_begin,writer_present,writer_acquire_complete,writer_release_readers,writer_release_writers,reader_acquire_direct,reader_acquire_delayed,reader_undelayed,reader_release,enter_single_threaded,exit_single_threaded)]
RwToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        // The constant portion of the invariant we maintain about the stored value
        #[sharding(constant)]
        pub k: K,

        // Placeholder for the invariant we maintain about the store variable
        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        // Regulate how many threads can access the mutex at one time
        #[sharding(count)]
        pub lock_access: nat,

        // Value protected by this lock
        #[sharding(storage_option)]
        pub storage: Option<V>,

        // Writer ticket lock
        #[sharding(variable)]
        pub win: u32,

        #[sharding(variable)]
        pub wout: u32,

        #[sharding(set)]
        pub writer_waiters: Set<u32>,

        // Reader ticket lock
        #[sharding(variable)]
        pub rin: u32,

        #[sharding(variable)]
        pub rout: u32,

        #[sharding(option)]
        pub writer: Option<WriterState>,

        #[sharding[variable]]
        pub phase: Phase,

        // Resource handed out to the readers waiting on a writer to finish
        #[sharding(multiset)]
        pub delayed_reader: Multiset<WriterPhase>,

        // References handed out to the live readers
        #[sharding(multiset)]
        pub reader: Multiset<V>,

        // Working in single-threaded mode
        #[sharding(variable)]
        pub single_threaded: bool,

        // Values of the ticket counters
        #[sharding(option)]
        pub single_values: Option<(u32, u32, u32, u32)>,
    }

    #[invariant]
    pub fn win(&self) -> bool {
        &&& self.win == (self.wout + self.writer_waiters.len() + countb(self.writer is Some)) % 0x1_0000_0000
    }

    #[invariant]
    pub fn writer_waiters_bound(&self) -> bool {
        &&& self.writer_waiters.len() + countb(self.writer is Some) <= u32::MAX
    }

    #[invariant]
    pub fn writer_serving(&self) -> bool {
        self.writer_waiters.contains(self.wout) ==> self.storage.is_some() && self.writer is None
    }

    #[invariant]
    pub fn valid_storage(&self) -> bool {
        self.storage matches Some(v) ==> Pred::inv(self.k, v)
    }

    #[invariant]
    pub fn writer(&self) -> bool {
        writing(self.writer) <==> self.storage.is_none()
    }

    #[invariant]
    pub fn writer_storage(&self) -> bool {
        use WriterState::*;
        match self.writer {
            Some(Pending(t)) => t == self.wout,
            Some(Draining(_, w_t)) => w_t == self.wout,
            Some(Writing(t)) => t == self.wout,
            Some(Exiting(t)) => t == self.wout,
            _ => true
        }
    }

    #[invariant]
    pub fn writer_writer_waiters(&self) -> bool {
        &&& if self.wout <= self.win {
            &&& forall |i:u32| i < self.wout || i >= self.win ==> !self.writer_waiters.contains(i)
            &&& forall |i| self.wout + 1 <= i < self.win ==> self.writer_waiters.contains(i)
        } else {
            &&& forall |i:u32| i > self.wout || i < self.win ==> self.writer_waiters.contains(i)
            &&& forall |i| self.win <= i < self.wout ==> !self.writer_waiters.contains(i)
        }
    }

    #[invariant]
    pub fn writer_pending_implies_reader_phase(self) -> bool {
        pending(self.writer) ==> self.phase is Reader
    }

    #[invariant]
    pub fn writer_present_phase(&self) -> bool {
        use WriterPhase::*;
        &&& if !(self.writer is None) && !pending(self.writer) && !exiting(self.writer) {
            self.phase matches Phase::WriterPresent(p) &&
                if exiting(self.writer) {
                    self.wout % 2 == 1 <==> p == Odd
                } else {
                    self.wout % 2 == 0 <==> p == Even
                }
        } else if self.writer is None || pending(self.writer) {
            &&& self.wout % 2 == 0 ==> self.delayed_reader.count(Even) == 0
            &&& self.wout % 2 == 1 ==> self.delayed_reader.count(Odd) == 0
        } else if exiting(self.writer) {
            self.phase is Reader
        } else {
            true
        }
    }

    #[invariant]
    pub fn writer_is_present(&self) -> bool {
        (draining(self.writer) || writing(self.writer)) <==> self.phase is WriterPresent
    }

    #[invariant]
    pub fn writer_blocks_readers(&self) -> bool {
        // Implies that once the writer has completed the draining process,
        // there are no active or ignorant readers
        self.writer matches Some(WriterState::Draining(r_t, w_t)) ==>
            (r_t - self.rout) % 0x100_0000 == self.reader.len() + self.delayed_reader.count(self.phase->0.opposite())
    }

    #[invariant]
    pub fn thread_bound(&self) -> bool {
        self.reader.len() + self.delayed_reader.len() +
        self.writer_waiters.len() + countb(self.writer is Some) +
        self.lock_access == MAX_PCPU_COUNT
    }

    #[invariant]
    pub fn reader_bound(&self) -> bool {
        &&& self.rin < 0x100_0000
        &&& self.rout < 0x100_0000
        &&& self.reader.len() + self.delayed_reader.len() <= u32::MAX
    }

    #[invariant]
    pub fn reader_phase_agreement(&self) -> bool {
        use WriterPhase::*;
        match self.writer {
            None| Some(WriterState::Pending(_)) => {
                if self.wout % 2 == 0  {
                    self.delayed_reader.count(Even) == 0
                } else {
                    self.delayed_reader.count(Odd) == 0
                }
            }
            Some(WriterState::Exiting(_)) => {
                    if self.wout % 2 == 0  {
                        self.delayed_reader.count(WriterPhase::Odd) == 0
                    } else {
                        self.delayed_reader.count(WriterPhase::Even) == 0
                    }
            }
            Some(WriterState::Draining(_, _)) => true,
            Some(_) => self.delayed_reader.count(self.phase->0.opposite()) == 0,
        }
    }

    #[invariant]
    pub fn only_pending_mixes_delayed_readers(&self) -> bool {
        !draining(self.writer) ==>
            (self.delayed_reader.count(WriterPhase::Even) == 0 ||
             self.delayed_reader.count(WriterPhase::Odd) == 0)
    }

    #[invariant]
    pub fn reader_count(&self) -> bool {
        // All of the readers are accounted for by rin - rout
        (self.rin - self.rout) % 0x100_0000  == self.reader.len() + self.delayed_reader.len()
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| #[trigger] self.reader.count(t) > 0 ==> self.storage == Option::Some(t)
    }

    #[invariant]
    pub fn lock_access_bound(&self) -> bool {
        self.lock_access <= MAX_PCPU_COUNT
    }

    #[invariant]
    pub fn single_threaded(&self) -> bool {
        &&& self.single_threaded ==> self.lock_access == MAX_PCPU_COUNT &&
            (self.single_values matches Some((rin, rout, win, wout))
            && rin == self.rin
            && rout == self.rout
            && win == self.win
            && wout == self.wout
            && rin == rout
            && win == wout
            )
        &&& !self.single_threaded <==> self.single_values is None
        &&& self.lock_access < MAX_PCPU_COUNT ==> !self.single_threaded
    }

   init!{
        new(k: K, v: V) {
            require Pred::inv(k, v);
            init k = k;
            init pred = PhantomData;
            init lock_access = MAX_PCPU_COUNT as nat;
            init storage = Option::Some(v);
            init win = 0;
            init wout = 0;
            init writer_waiters = Set::empty();
            init rin = 0;
            init rout = 0;
            init writer = None;
            init phase = Phase::Reader;
            init delayed_reader = Multiset::empty();
            init reader = Multiset::empty();
            init single_threaded = false;
            init single_values = None;
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self, k: K, v: V) {
        broadcast use group_multiset_axioms;
    }

    transition! {
        writer_take_ticket() {
            require(!pre.single_threaded);
            remove lock_access -= (1);
            update win = wrapping_add(pre.win, 1);
            birds_eye let writer_ticket = pre.win;
            add writer_waiters += set { writer_ticket };
            assert(writer_ticket == pre.win);
        }
    }

    #[inductive(writer_take_ticket)]
    fn writer_take_ticket_inductive(pre:Self, post: Self) {
    }

    transition! {
        writer_acquire_begin(t: u32) {
            require t == pre.wout;
            remove writer_waiters -= set { t };
            add writer += Some(WriterState::Pending(t));
        }
    }

    #[inductive(writer_acquire_begin)]
    fn writer_acquire_begin_inductive(pre:Self, post: Self, t: u32) {
    }

    transition! {
        writer_present(t: u32) {
            remove writer -= Some(WriterState::Pending(t));
            update phase = Phase::new_writer(t);
            add writer += Some(WriterState::Draining(pre.rin, t));
        }
    }

    #[inductive(writer_present)]
    fn writer_present_inductive(pre:Self, post: Self, t: u32) {
        // We need this to show that the total length of the delayed readers is equal to the count of each type
        multiset_len_sums_counts_writerphase(pre.delayed_reader);
    }

    transition! {
        writer_acquire_complete(w_t: u32, r_t: u32) {
            // The writer is waiting for rout to reach r_t
            remove writer -= Some(WriterState::Draining(r_t, w_t));
            // rout has in fact reached r_t
            require r_t == pre.rout;

            add writer += Some(WriterState::Writing(w_t));

            // Give the lock-protected value to the writer
            birds_eye let v = pre.storage->0;
            withdraw storage -= Some(v);
            assert Pred::inv(pre.k, v);
        }
    }

    #[inductive(writer_acquire_complete)]
    fn writer_acquire_complete_inductive(pre:Self, post: Self, w_t: u32, r_t: u32) {
    }

    transition! {
        writer_release_readers(v: V, w_t: u32) {
            // v is a valid value for the lock to store
            require Pred::inv(pre.k, v);
            // The writer cannot write an more
            remove writer -= Some(WriterState::Writing(w_t));

            deposit storage += Some(v);

            update phase = Phase::Reader;
            add writer += Some(WriterState::Exiting(w_t));
        }
    }

    #[inductive(writer_release_readers)]
    fn writer_release_readers_inductive(pre:Self, post: Self, v: V, w_t: u32) {
    }

    transition! {
        writer_release_writers(w_t: u32) {
            remove writer -= Some(WriterState::Exiting(w_t));
            update wout = wrapping_add(pre.wout, 1);
            add lock_access += (1);
        }
    }

    #[inductive(writer_release_writers)]
    fn writer_release_writers_inductive(pre:Self, post: Self, w_t: u32) {
    }

    transition! {
        reader_acquire_direct() {
            require(!pre.single_threaded);
            require pre.phase is Reader;
            remove lock_access -= (1);
            update rin = wrapping_add_u24(pre.rin, 1);
            birds_eye let v: V = pre.storage->0;
            add reader += { v };
        }
    }

    #[inductive(reader_acquire_direct)]
    fn reader_acquire_direct_inductive(pre:Self, post: Self) {
    }

    transition! {
        reader_acquire_delayed() {
            require pre.phase is WriterPresent;
            remove lock_access -= (1);
            update rin = wrapping_add_u24(pre.rin, 1);
            add delayed_reader += { pre.phase->0 };
        }
    }

    #[inductive(reader_acquire_delayed)]
    fn reader_acquire_delayed_inductive(pre:Self, post: Self) {
    }

    transition! {
        reader_undelayed(old_phase: WriterPhase) {
            require (pre.phase is Reader || (pre.phase matches Phase::WriterPresent(parity) && parity != old_phase));
            remove delayed_reader -= { old_phase };
            birds_eye let v: V = pre.storage->0;
            add reader += { v };
        }
    }

    #[inductive(reader_undelayed)]
    fn reader_undelayed_inductive(pre:Self, post: Self, old_phase: WriterPhase) {
    }

    transition! {
        reader_release(v: V) {
            remove reader -= { v };
            add lock_access += (1);
            update rout = wrapping_add_u24(pre.rout, 1);
        }
    }

    #[inductive(reader_release)]
    fn reader_release_inductive(pre:Self, post: Self, v: V) {
    }

    transition! {
        enter_single_threaded() {
            require(!pre.single_threaded);
            have lock_access >= (MAX_PCPU_COUNT as nat);
            birds_eye let rin = pre.rin;
            birds_eye let rout = pre.rout;
            birds_eye let win = pre.win;
            birds_eye let wout = pre.wout;
            add single_values += Some((rin, rout, win, wout));
            update single_threaded = true;
        }
    }

    #[inductive(enter_single_threaded)]
    fn enter_single_threaded_inductive(pre:Self, post: Self) {
    }

    transition! {
        exit_single_threaded(rin: u32, rout: u32, win: u32, wout: u32) {
            require(pre.single_threaded);
            update single_threaded = false;
            remove single_values -= Some((rin, rout, win, wout));
        }
    }

    #[inductive(exit_single_threaded)]
    fn exit_single_threaded_inductive(pre:Self, post: Self, rin: u32, rout: u32, win: u32, wout: u32) {
    }

    property! {
        pending_implies_reader(t: u32) {
            have writer >= (Some(WriterState::Pending(t)));
            assert(pre.phase is Reader);
        }
    }

    property! {
        read_guard(v: V) {
            have reader >= { v };
            guard storage >= (Some(v));
            assert Pred::inv(pre.k, v);
        }
    }

    property! {
        exiting_matches_wout(w_t: u32) {
            have writer >= (Some(WriterState::Exiting(w_t)));
            assert(w_t == pre.wout);
        }
    }

    property! {
        rin_bound() {
            assert(pre.rin < 0x100_0000);
        }
    }

    property! {
        rout_bound() {
            assert(pre.rout < 0x100_0000);
        }
    }

    property! {
        single_threaded_rin(rin: u32, rout: u32, win: u32, wout: u32) {
            require(pre.single_threaded);
            have single_values >= Some((rin, rout, win, wout));
            assert(rin == pre.rin && rin == rout && pre.phase is Reader);
        }
    }

    property! {
        single_threaded_rout(rin: u32, rout: u32, win: u32, wout: u32) {
            require(pre.single_threaded);
            have single_values >= Some((rin, rout, win, wout));
            assert(rout == pre.rout && rin == rout);
        }
    }

    property! {
        single_threaded_win(rin: u32, rout: u32, win: u32, wout: u32) {
            require(pre.single_threaded);
            have single_values >= Some((rin, rout, win, wout));
            assert(win == pre.win && win == wout);
        }
    }

    property! {
        single_threaded_wout(rin: u32, rout: u32, win: u32, wout: u32) {
            require(pre.single_threaded);
            have single_values >= Some((rin, rout, win, wout));
            assert(wout == pre.wout && win == wout);
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
        Tracked(mut lock_access),
        Tracked(mut win),
        Tracked(mut wout),
        Tracked(waiters),
        Tracked(mut rin),
        Tracked(mut rout),
        Tracked(writer),
        Tracked(mut phase),
        Tracked(delayed),
        Tracked(readers),
        Tracked(mut single_threaded),
        Tracked(single_values),
    ) = RwToks::Instance::<vstd::cell::CellId, cell::PointsTo<usize>, CellPred>::new(
        cell.id(),
        permission,
        Some(permission),
    );
    let tracked access = lock_access.split(1);
    let tracked (Ghost(value), Tracked(reader)) = instance.reader_acquire_direct(
        access,
        &mut rin,
        &phase,
        &single_threaded,
    );
    let tracked access = lock_access.split(1);
    let tracked waiter = instance.writer_take_ticket(access, &mut win, &single_threaded);
    let tracked writer = instance.writer_acquire_begin(0, &wout, waiter);
    let tracked writer = instance.writer_present(0, &rin, writer, &mut phase);
    let tracked result = instance.writer_acquire_complete(0, 1, &rout, writer);
}

} // verus!
