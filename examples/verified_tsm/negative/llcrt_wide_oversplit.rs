// EXPECTED-ERROR: precondition not satisfied
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#[path = "../support/llcrt_tagged_vstd_ext.rs"]
mod vstd_ext;
mod process_barrier {
    use vstd::prelude::*;
    verus! {

#[repr(u32)]
#[derive(Debug,Clone,Copy,PartialEq,PartialOrd,Structural)]
pub enum BarrierState {
    Blocked = 0,
    Completed = 1,
    Canceled = 2,
}

} // verus!
}
use crate::process_barrier::BarrierState;
use crate::vstd_ext::lemma_map_size;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

/********************************************************************************
 *
 * Define the ticket-related resources we use to specify the barrier.
 * Each thread arrives with a ticket, which is accumulated into a TicketMap.
 * Inside the barrier, the Ticketing trait dictates how a complete TicketMap
 * of incoming tickets is processed to produce a complete TicketMap of outgoing
 * tickets.
 *
 ********************************************************************************/
/// Interface for canceling a barrier
pub trait CancelResource {
    type Instance;

    spec fn wf(&self, instance: &Self::Instance) -> bool;
}

/// Interface for evidence that the barrier was canceled
pub trait CanceledResource: Sized {
    type Instance;

    spec fn wf(&self, instance: &Self::Instance) -> bool;

    proof fn clone(tracked &mut self) -> (tracked result: Self)
        ensures
            forall|instance: Self::Instance| old(self).wf(&instance) == final(self).wf(&instance),
            forall|instance: Self::Instance| old(self).wf(&instance) == result.wf(&instance),
    ;
}

/// Interface for incoming or outgoing tickets
pub trait Ticket {
    type Instance;

    spec fn is_leader(&self) -> bool;

    spec fn wf(&self, instance: &Self::Instance) -> bool;

    spec fn id(&self) -> nat;
}

/// Accumulate sets of (numbered) tickets
pub tracked struct TicketMap<T: Ticket> {
    pub ghost instance: T::Instance,
    pub m: Map<nat, T>,
}

impl<T: Ticket> View for TicketMap<T> {
    type V = Map<nat, T>;

    open spec fn view(&self) -> Map<nat, T> {
        self.m
    }
}

impl<T: Ticket> TicketMap<T> {
    pub open spec fn count(self) -> nat {
        self@.dom().len()
    }

    pub open spec fn valid(m: Map<nat, T>, start: nat, end: nat, instance: T::Instance) -> bool {
        &&& forall|i| start <= i < end ==> #[trigger] m.contains_key(i) && m[i].wf(&instance)
        &&& forall|i| #![auto] start <= i < end ==> m.contains_key(i) && !m[i].is_leader()
    }

    pub open spec fn wf(self) -> bool {
        self@.dom().len() == self.count() && (forall|i|
            0 <= i < self.count() <==> #[trigger] self@.contains_key(i)) && (forall|i|
            0 <= i < self.count() ==> (#[trigger] self@[i]).wf(&self.instance))
    }

    pub open spec fn index_matches_ids(self) -> bool {
        forall|i| 0 <= i < self.count() ==> #[trigger] (self@[i].id()) == i
    }

    pub open spec fn unique_leader(self) -> bool {
        &&& (exists|i| 0 <= i < self.count() && #[trigger] (self@[i].is_leader()))
        &&& (forall|i, j|
            #![auto]
            0 <= i <= j < self.count() ==> self@[i].is_leader() && self@[j].is_leader() ==> i == j)
    }

    pub open spec fn no_leader(self) -> bool {
        forall|i|
            0 <= i < self.count() && self@.contains_key(i) ==> !(#[trigger] self@[i].is_leader())
    }

    pub open spec fn no_leader_strong(self) -> bool {
        forall|i| 0 <= i < self.count() ==> !(#[trigger] self@[i].is_leader())
    }

    pub proof fn new(instance: T::Instance) -> (tracked r: Self)
        ensures
            r.wf(),
            r.index_matches_ids(),
            r.instance == instance,
            r.count() == 0,
    {
        TicketMap { instance, m: Map::tracked_empty() }
    }

    pub proof fn insert(tracked &mut self, tracked t: T)
        requires
            old(self).wf(),
            t.wf(&old(self).instance),
        ensures
            final(self).wf(),
            final(self).instance == old(self).instance,
            final(self).count() == old(self).count() + 1,
            final(self)@ == old(self)@.insert(old(self).count(), t),
    {
        assert(!self@.contains_key(self.count()));
        self.m.tracked_insert(self.count(), t);
    }

    pub proof fn pop(tracked &mut self) -> (tracked t: T)
        requires
            old(self).wf(),
            old(self).count() > 0,
        ensures
            final(self).wf(),
            final(self).instance == old(self).instance,
            final(self).count() == old(self).count() - 1,
            t == old(self)@[(old(self).count() - 1) as nat],
            final(self)@ == old(self)@.remove((old(self).count() - 1) as nat),
    {
        self.m.tracked_remove((self.count() - 1) as nat)
    }

    /// Find and return the unique leader ticket within the TicketMap
    pub proof fn extract_leader(tracked &mut self) -> (tracked leader: T)
        requires
            old(self).wf(),
            old(self).count() > 0,
            old(self).unique_leader(),
        ensures
            leader.is_leader(),
            leader.wf(&final(self).instance),
            final(self).count() == old(self).count() - 1,
            forall|i|
                #![auto]
                0 <= i < final(self).count() && final(self)@.contains_key(i)
                    ==> !final(self)@[i].is_leader(),
            final(self).wf(),
            final(self).instance == old(self).instance,
            TicketMap::valid(final(self).m, 0, final(self).count(), final(self).instance),
    {
        let leader_index = choose|i| #![auto] 0 <= i < self.count() && self.m[i].is_leader();
        let tracked leader = self.m.tracked_remove(leader_index);
        let new_len = self.count();
        let remap = Map::new(
            Set::range(0, new_len),
            |k: nat|
                if k < leader_index {
                    k
                } else {
                    k + 1
                },
        );
        self.m.tracked_map_keys_in_place(remap);
        // Prove that self.wf() holds
        let sir = set_int_range(0, new_len as int);
        let sir_nat = sir.map(|i| i as nat);
        assert(sir_nat.len() == new_len) by {
            lemma_map_size(sir, sir_nat, |i| i as nat);
        }
        assert(sir_nat =~= remap.dom()) by {
            assert forall|i| #![auto] sir_nat.contains(i) == remap.dom().contains(i) by {
                if sir_nat.contains(i) {
                    assert(0 <= i < new_len);
                    assert(remap.dom().contains(i));
                } else {
                    if remap.dom().contains(i) {
                        assert(0 <= i < new_len);
                        assert(sir.contains(i as int));
                        assert(sir_nat.contains(i));
                        assert(false);
                    }
                    assert(!remap.dom().contains(i));
                }
            }
        }
        assert(self.m.dom() == sir_nat);  // OBSERVE

        leader
    }
}

pub trait Completed: Sized {
    type Instance;

    spec fn wf(&self, instance: &Self::Instance) -> bool;

    proof fn clone(tracked &mut self) -> (tracked result: Self)
        ensures
            forall|instance: Self::Instance| old(self).wf(&instance) == final(self).wf(&instance),
            forall|instance: Self::Instance| old(self).wf(&instance) == result.wf(&instance),
    ;
}

pub trait HasInstanceId {
    spec fn my_id(&self) -> InstanceId;
}

/// Define the types for entry and exit tickets, and the `complete` action
/// that processes a complete TicketMap  of incoming tickets to produce a
/// complete TicketMap of outgoing tickets.
pub trait Ticketing {
    type Instance: HasInstanceId;

    // Resource each thread must have to enter the barrier
    type Entry: Ticket<Instance = Self::Instance>;

    // Resource obtained when entering the barrier succeeds
    type Exit: Ticket<Instance = Self::Instance>;

    // Evidence that the barrier completed successfully
    type Completed: Completed<Instance = Self::Instance>;

    // Permission to cancel the barrier
    type MayCancel: CancelResource<Instance = Self::Instance>;

    // Evidence that the barrier has been canceled
    type Canceled: CanceledResource<Instance = Self::Instance>;

    spec fn instance(&self) -> Self::Instance;

    spec fn max_threads(&self) -> nat;

    // Function that converts a complete set of num_threads Entry resources
    // into a complete set of num_threads Exit resources.
    proof fn complete(
        tracked &self,
        tracked entry_tickets: TicketMap<Self::Entry>,
    ) -> (tracked result: (TicketMap<Self::Exit>, Self::Completed))
        requires
            entry_tickets.wf(),
            entry_tickets.instance == self.instance(),
            entry_tickets.count() == self.max_threads(),
        ensures
            ({
                let (exit_tickets, completed) = result;
                exit_tickets.wf() && exit_tickets.unique_leader() && exit_tickets.instance
                    == self.instance() && exit_tickets.count() == self.max_threads()
                    && completed.wf(&self.instance())
            }),
    ;

    // Proof that we can never have successfully completed the barrier and yet have a lingering entry ticket
    proof fn not_done(
        tracked &self,
        tracked completed: &Self::Completed,
        tracked entry_ticket: &Self::Entry,
    )
        requires
            entry_ticket.wf(&self.instance()),
            completed.wf(&self.instance()),
        ensures
            false,
    ;

    // Convert permission to cancel the Ticketing process into evidence that it has been canceled
    proof fn cancel(tracked &self, tracked cancel_ticket: Self::MayCancel) -> (tracked result:
        Self::Canceled)
        requires
            cancel_ticket.wf(&self.instance()),
        ensures
            result.wf(&self.instance()),
    ;
}

// A larger set of states the ghost state machine can be in.
// Some match the physical states, but we also add new ones to reflect intermediate transitions.
pub enum BarrierMachineState {
    Dormant,
    // The entry and exit counts are not yet initialized.
    Initializing,
    // Reset transients before the entry and exit counts, respectively, are cleared.
    Resetting,
    ResettingExit,
    // Transient state in the leader's two-step entry process
    LeaderEntering,
    // Real states
    Blocked,
    Completed,
    Canceled,
}

impl BarrierMachineState {
    pub open spec fn matches_u32(&self, v: u32) -> bool {
        use BarrierMachineState::*;
        match self {
            Dormant => v == BarrierState::Completed as int,
            Initializing => v == BarrierState::Blocked as int,
            Resetting => v == BarrierState::Completed as int,
            ResettingExit => v == BarrierState::Completed as int,
            Blocked => v == BarrierState::Blocked as int,
            LeaderEntering => v == BarrierState::Completed as int,
            Completed => v == BarrierState::Completed as int,
            Canceled => v == BarrierState::Canceled as int,
        }
    }
}

use vstd::cell::pcell::PointsTo;
use vstd::cell::CellId;
use vstd::multiset::*;
use vstd::raw_ptr::MemContents::Init;
use vstd::set_lib::{lemma_int_range, set_int_range};

pub trait StbTicketing<R> {
    type Instance: HasInstanceId;

    // Resource each thread must have to enter the barrier
    type Entry: Ticket<Instance = Self::Instance>;

    // Resource obtained when entering the barrier succeeds
    type Exit: Ticket<Instance = Self::Instance>;

    // Permission to cancel the barrier
    type MayCancel: CancelResource<Instance = Self::Instance>;

    // Evidence that the barrier has been canceled
    type Canceled: CanceledResource<Instance = Self::Instance>;

    // Predicate over valid return values
    spec fn valid_result(&self, r: R) -> bool;

    spec fn instance(&self) -> Self::Instance;

    spec fn max_threads(&self) -> nat;

    // Convert permission to cancel the Ticketing process into evidence that it has been canceled
    proof fn cancel(tracked &self, tracked cancel_ticket: Self::MayCancel) -> (tracked result:
        Self::Canceled)
        requires
            cancel_ticket.wf(&self.instance()),
        ensures
            result.wf(&self.instance()),
    ;
}

pub enum Stage {
    Fresh,
    Entering,
    CanDeposit,
    Deposited,
    // We can't usefully capture these stages, since there's no way to get the resource back to
    // the thread that's initially elected the leader
    // Reading,
    // ReadingDone,
    // Withdrawn,
    Canceled,
}

pub open spec fn only_one(b0: bool, b1: bool, b2: bool) -> bool {
    ||| b0 && !b1 && !b2
    ||| !b0 && b1 && !b2
    ||| !b0 && !b1 && b2
}

pub open spec fn valid_tix_tickets<Result, Tix>(
    m: Map<nat, Tix::Exit>,
    instance: Tix::Instance,
) -> bool where Tix: StbTicketing<Result> {
    forall|i| #[trigger] m.contains_key(i) ==> m[i].wf(&instance) && !m[i].is_leader()
}

pub open spec fn full_follower_perms<Result, Tix: StbTicketing<Result>>(
    m: &SingleThreadedMachine::State<Result, Tix>,
) -> bool {
    forall|i| m.follower_perms.contains(i) <==> 0 <= i < m.max_threads - 1
}

verified_tokenized_state_machine!(
SingleThreadedMachine<Result, Tix: StbTicketing<Result>> {
    fields {
        #[sharding(constant)]
        pub max_threads: nat,

        // The StbTicketing instance deposited in this barrier
        #[sharding(constant)]
        pub ticketing_instance: Tix::Instance,

        #[sharding(option)]
        pub stage: Option<Stage>,

        #[sharding(count)]
        pub may_cancel_entry: nat,

        #[sharding(count)]
        pub may_cancel_result: nat,

        #[sharding(count)]
        pub may_cancel_exit: nat,

        #[sharding(constant)]
        pub result_cell_id: CellId,

        #[sharding(persistent_bool)]
        pub entered: bool,      // We've entered the first barrier

        #[sharding(persistent_bool)]
        pub deposited: bool,      // leader deposited tickets and result_perm

        #[sharding(persistent_bool)]
        pub result: bool,      // We've entered the result barrier

        #[sharding(bool)]
        pub leader: bool,

        #[sharding(persistent_bool)]
        pub returned_duplicable: bool,

        #[sharding(persistent_option)]
        pub canceled: Option<Tix::Canceled>,

        #[sharding(bool)]
        pub withdrawn: bool,

        // Permission used for reading/writing the result cell
        #[sharding(storage_option)]
        pub result_perm: Option<PointsTo<Option<Result>>>,

        // Tickets to track threads entering the initial barrier
        #[sharding(count)]
        pub entering: nat,

        // Tickets to track threads waiting for the result to be written
        #[sharding(count)]
        pub waiting_on_result: nat,

        // Tickets to track threads reading the result; we use a multiset, since we need to track the value
        // stored in result_perm to ensure the value can't change while the readers are reading
        #[sharding(multiset)]
        pub result_readers: Multiset<PointsTo<Option<Result>>>,

        #[sharding(variable)]
        pub control_state_initialized: bool,

        // Exit tickets from the outer StbTicketing instance, which we will give out to the followers
        #[sharding(storage_map)]
        pub exit_tickets: Map<nat, Tix::Exit>,

        // Each element corresponds to a follower (from the entry barrier)
        // and can be used to withdraw the corresponding ticket from exit_tickets
        #[sharding(set)]
        pub follower_perms: Set<int>,   // TODO: Unify this with `waiting_on_result`?
    }

    #[invariant]
    pub fn counts(&self) -> bool {
        &&& self.max_threads > 0
        &&& self.entering <= self.max_threads - 1
        &&& self.waiting_on_result == 0 || self.waiting_on_result == self.max_threads - 1
        &&& self.may_cancel_entry <= self.max_threads
        &&& self.may_cancel_exit <= self.max_threads
        &&& self.may_cancel_result <= self.max_threads
    }

    #[invariant]
    pub fn only_one_state(&self) -> bool {
        &&& only_one(
            self.stage is Some,
            (exists|r| #[trigger](self.result_readers.count(r)) > 0),
            self.returned_duplicable || self.withdrawn,
            )
    }

    #[invariant]
    pub fn no_early_returned_duplicable(&self) -> bool {
        self.stage is Some ==> !self.returned_duplicable
    }

    #[invariant]
    pub fn result_perm(&self) -> bool {
        &&& forall |r| #[trigger](self.result_readers.count(r)) > 0 ==> self.result_perm == Option::Some(r) && self.result_readers.count(r) == self.max_threads
        &&& self.result_perm matches Some(p) ==> p.id() == self.result_cell_id && (p.value() is Some)
    }

    #[invariant]
    pub fn returned(&self) -> bool {
        &&& self.returned_duplicable ==> forall |r| #[trigger](self.result_readers.count(r)) == 0
        &&& self.returned_duplicable && self.leader ==> self.result_perm.is_some() && !self.withdrawn
    }

    #[invariant]
    pub fn stage_implications(&self) -> bool {
        self.stage matches Some(s) ==> {
            use Stage::*;
            match s {
                Fresh =>
                    !self.control_state_initialized &&
                    !self.leader &&
                    self.result_perm.is_none() &&
                    self.waiting_on_result == 0 &&
                    self.entering == 0 &&
                    !self.entered &&
                    !self.deposited &&
                    self.canceled is None &&
                    self.follower_perms.is_empty() &&
                    self.exit_tickets.is_empty() &&
                    !self.result
                ,
                Entering =>
                    (self.control_state_initialized || self.canceled is Some) &&
                    !self.leader &&
                    self.result_perm.is_none() &&
                    self.waiting_on_result == 0 &&
                    !self.entered &&
                    !self.deposited &&
                    self.follower_perms.is_empty() &&
                    self.exit_tickets.is_empty() &&
                    !self.result
                ,
                CanDeposit =>
                    self.result_perm.is_none() &&
                    self.entered &&
                    !self.deposited &&
                    self.waiting_on_result == (self.max_threads - 1) as nat &&
                    self.canceled is None &&
                    full_follower_perms(self) &&
                    self.exit_tickets.is_empty() &&
                    !self.result
                ,
                Deposited =>
                    self.result_perm.is_some() &&
                    self.deposited &&
                    self.entered &&
                    self.waiting_on_result == (self.max_threads - 1) as nat &&
                    self.canceled is None &&
                    !self.result
                ,
                Canceled =>
                    !self.control_state_initialized &&
                    !self.leader &&
                    self.result_perm.is_none() &&
                    self.waiting_on_result == 0 &&
                    !self.entered &&
                    !self.result
                ,
            }
        }
    }

    #[invariant]
    pub fn no_stage_implications(&self) -> bool {
        self.stage is None ==> {
            &&& self.entered
            &&& self.canceled is None
            &&& self.result
            &&& self.entering == 0
            &&& self.waiting_on_result == 0
        }
    }

    #[invariant]
    pub fn may_cancel(&self) -> bool {
        &&& self.stage matches Some(s) ==> {
            use Stage::*;
            match s {
                Fresh => self.may_cancel_entry == self.may_cancel_result == self.may_cancel_exit == 0,
                Entering => {
                   ||| self.may_cancel_entry == self.may_cancel_result == self.may_cancel_exit == self.max_threads
                   ||| self.canceled is Some && (self.may_cancel_entry < self.max_threads || self.may_cancel_result < self.max_threads || self.may_cancel_exit < self.max_threads)
                }
                CanDeposit | Deposited => self.may_cancel_entry == self.may_cancel_result == self.may_cancel_exit == 0,
                Canceled => self.canceled is Some

            }
        }
        &&&
        self.stage is None ==> {
            self.may_cancel_entry == self.may_cancel_result == self.may_cancel_exit == 0
        }
    }

    #[invariant]
    pub fn canceled(&self) -> bool {
        &&& self.canceled is Some ==> ((self.stage matches Some(s) && (s is Canceled)) || self.stage is None) || self.entering < self.max_threads - 1
    }

    #[invariant]
    pub fn canceled2(&self) -> bool {
        &&& self.control_state_initialized ==> self.canceled is None
    }

    #[invariant]
    pub fn leader_is_initialized(&self) -> bool {
        self.leader ==> self.control_state_initialized
    }

    #[invariant]
    pub fn follower_perms_properties(&self) -> bool {
        &&& forall |e| self.follower_perms.contains(e) ==> 0 <= e < self.max_threads - 1
        &&& self.follower_perms.len() <= self.max_threads - 1
        &&& self.deposited ==> forall |e| self.follower_perms.contains(e) ==> self.exit_tickets.contains_key(e as nat)
    }

    #[invariant]
    pub fn exit_tickets_inv(&self) -> bool {
        &&& forall |e|
            #![trigger self.exit_tickets.contains_key(e)]
            #![trigger self.follower_perms.contains(e as int)]
            self.exit_tickets.contains_key(e) ==> self.follower_perms.contains(e as int)
        &&& valid_tix_tickets::<Result,Tix>(self.exit_tickets, self.ticketing_instance)
    }

    #[invariant]
    pub fn entering(&self) -> bool {
        (
            self.stage matches Some(s) ==> match(s) {
                Stage::Entering => self.entering == self.max_threads - 1 || (self.canceled is Some && self.entering < self.max_threads - 1),
                Stage::Canceled => self.canceled is Some,
                _ => self.entering == 0,
            }
        )
    }

    init! {
        new(num_threads: nat, ticketing_instance: Tix::Instance, cell_id: CellId) {
            require(num_threads > 0);
            init max_threads = num_threads;
            init ticketing_instance = ticketing_instance;
            init stage = Some(Stage::Fresh);
            init may_cancel_entry = 0;
            init may_cancel_result = 0;
            init may_cancel_exit = 0;
            init result_cell_id = cell_id;
            init entered = false;
            init deposited = false;
            init result = false;
            init leader = false;
            init returned_duplicable = false;
            init canceled = None;
            init withdrawn = false;
            init result_perm = None;
            init entering = 0;
            init waiting_on_result = 0;
            init result_readers = Multiset::empty();
            init control_state_initialized = false;
            init exit_tickets = Map::empty();
            init follower_perms = Set::empty();
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self, num_threads: nat, ticketing_instance: Tix::Instance, cell_id: CellId) {
    }

    transition! {
        initialize_barrier() {
            remove stage -= Some(Stage::Fresh);
            update control_state_initialized = true;
            add entering += ((pre.max_threads - 1) as nat);
            add may_cancel_entry += (pre.max_threads);
            add may_cancel_result += (pre.max_threads);
            add may_cancel_exit += (pre.max_threads);
            add stage += Some(Stage::Entering);
        }
    }

    #[inductive(initialize_barrier)]
    fn initialize_barrier_inductive(pre:Self, post: Self) {
    }

    transition! {
        enter_complete() {
            remove stage -= Some(Stage::Entering);
            remove entering -= ((pre.max_threads - 1) as nat);
            remove may_cancel_entry -= (pre.max_threads);
            remove may_cancel_result -= (pre.max_threads);
            remove may_cancel_exit -= (pre.max_threads);
            add waiting_on_result += ((pre.max_threads - 1) as nat); // Leader doesn't wait on the result
            add entered (union)= true;
            add leader += true;
            add stage += Some(Stage::CanDeposit);
            add follower_perms += (set_int_range(0, pre.max_threads - 1));
        }
    }

    #[inductive(enter_complete)]
    fn enter_complete_inductive(pre:Self, post: Self) {
        lemma_int_range(0, pre.max_threads - 1);
        assert(post.follower_perms == set_int_range(0, pre.max_threads - 1));   // OBSERVE
    }

    transition! {
        deposit(pptr: PointsTo<Option<Result>>, tickets: Map<nat, Tix::Exit>) {
            require(pptr.id() == pre.result_cell_id && (pptr.value() is Some));
            require(valid_tix_tickets::<Result, Tix>(tickets, pre.ticketing_instance));
            require(forall |i| 0 <= i < pre.max_threads - 1 <==> tickets.contains_key(i));
            remove stage -= Some(Stage::CanDeposit);
            deposit result_perm += Some(pptr);
            deposit exit_tickets += (tickets);
            add deposited (union)= true;
            add stage += Some(Stage::Deposited);
        }
    }

    #[inductive(deposit)]
    fn deposit_inductive(pre:Self, post: Self, pptr: PointsTo<Option<Result>>, tickets: Map<nat, Tix::Exit>) {
    }

    transition! {
        get_exit_ticket(e: int) {
            have deposited >= true;
            remove follower_perms -= set { e };

            withdraw exit_tickets -= [e as nat => let exit_ticket];
            birds_eye let ticket = pre.exit_tickets[e as nat];
            assert(ticket == exit_ticket && ticket.wf(&pre.ticketing_instance) && !ticket.is_leader());
        }
    }

    #[inductive(get_exit_ticket)]
    fn get_exit_inductive(pre:Self, post: Self, e: int) {
    }

    transition! {
        get_reader_perms() {
            remove stage -= Some(Stage::Deposited);
            remove waiting_on_result -= ((pre.max_threads - 1) as nat);
            birds_eye let r_perm = pre.result_perm->0;
            add result (union)= true;
            add result_readers +=
                (Multiset::from_map(
                    Map::new(
                        Set::empty().insert(r_perm),
                        |p| pre.max_threads
                    )
                ));
            //update stage = Stage::Reading;
        }
    }

    #[inductive(get_reader_perms)]
    fn get_reader_perms_inductive(pre:Self, post: Self) {
        assert(pre.result_perm.is_some());
        let r_perm = pre.result_perm->0;
        let m = Map::new(
                    Set::empty().insert(r_perm),
                    |p| pre.max_threads
                );
        let m_prime = Map::empty().insert(r_perm, pre.max_threads);
        assert(m == m_prime);
        assert(post.result_readers.count(r_perm) > 0);  // Trigger the existential
    }


    transition! {
        return_reader_perms(m: Multiset<PointsTo<Option<Result>>>, p: PointsTo<Option<Result>>) {
            //require pre.stage is Reading;
            require m.count(p) == pre.max_threads;
            remove result_readers -= (m);
            add returned_duplicable (union)= (true);
            //update stage = Stage::ReadingDone;
        }
    }

    #[inductive(return_reader_perms)]
    fn return_reader_perms_inductive(pre:Self, post: Self, m: Multiset<PointsTo<Option<Result>>>, p: PointsTo<Option<Result>>) {
        assert(m.subset_of(pre.result_readers));
    }

    transition! {
        withdraw_perms() {
            //require pre.stage is ReadingDone;
            remove leader -= (true);
            have returned_duplicable >= (true);
            add withdrawn += (true);
            update control_state_initialized = false;
            birds_eye let result_p = pre.result_perm->0;
            withdraw result_perm -= (Some(result_p));
            assert(result_p.id() == pre.result_cell_id);
            //update stage = Stage::Withdrawn;
        }
    }

    #[inductive(withdraw_perms)]
    fn withdraw_perms_inductive(pre:Self, post: Self) {
    }

    // transition! {
    //     cancel_entry(canceled_evidence: Tix::Canceled) {
    //         have canceled >= Some(canceled_evidence);
    //         remove may_cancel_entry -= (1);
    //     }
    // }

    // #[inductive(cancel_entry)]
    // fn cancel_entry_inductive(pre:Self, post: Self, canceled_evidence: Tix::Canceled) {
    // }

    // transition! {
    //     cancel_result(canceled_evidence: Tix::Canceled) {
    //         have canceled >= Some(canceled_evidence);
    //         remove may_cancel_result -= (1);
    //     }
    // }

    // #[inductive(cancel_result)]
    // fn cancel_result_inductive(pre:Self, post: Self, canceled_evidence: Tix::Canceled) {
    // }

    // transition! {
    //     cancel_exit(canceled_evidence: Tix::Canceled) {
    //         have canceled >= Some(canceled_evidence);
    //         remove may_cancel_exit -= (1);
    //     }
    // }

    // #[inductive(cancel_exit)]
    // fn cancel_exit_inductive(pre:Self, post: Self, canceled_evidence: Tix::Canceled) {
    // }

    transition! {
        cancel_follower(canceled_evidence_in: Tix::Canceled) {
            require(pre.control_state_initialized);
            require(canceled_evidence_in.wf(&pre.ticketing_instance));
            remove entering -= (1);     // Must give up your right to enter the barrier in order to cancel
            update control_state_initialized = false;
            add canceled (union)= Some(canceled_evidence_in);
        }
    }

    #[inductive(cancel_follower)]
    fn cancel_follower_inductive(pre:Self, post: Self, canceled_evidence_in: Tix::Canceled) {
    }

    transition! {
        cancel_leader(canceled_evidence_in: Tix::Canceled) {
            require(pre.control_state_initialized);
            require(canceled_evidence_in.wf(&pre.ticketing_instance));
            remove stage -= Some(Stage::Entering); // Must give up leader's right to enter the barrier in order to cancel
            update control_state_initialized = false;
            add stage += Some(Stage::Canceled);
            add canceled (union)= Some(canceled_evidence_in);
        }
    }

    #[inductive(cancel_leader)]
    fn cancel_leader_inductive(pre:Self, post: Self, canceled_evidence_in: Tix::Canceled) {
    }

    // Needed to satify a technicality where there are no readers
    transition! {
        generate_empty_waiter_token() {
            add waiting_on_result += (0);
        }
    }

    #[inductive(generate_empty_waiter_token)]
    fn generate_empty_waiter_token_inductive(pre:Self, post: Self) {
    }

    // Needed to satify a technicality where there are no entering threads
    transition! {
        generate_empty_entering_token() {
            add entering += (0);
            add may_cancel_entry += (0);
            add may_cancel_result += (0);
            add may_cancel_exit += (0);
        }
    }

    #[inductive(generate_empty_entering_token)]
    fn generate_empty_entering_token_inductive(pre:Self, post: Self) {
    }

    property! {
        read_guard(x: PointsTo<Option<Result>>) {
            have result_readers >= {x};
            guard result_perm >= (Some(x));
            assert(x.id() == pre.result_cell_id && (x.value() is Some));
        }
    }

    // property! {
    //     read_canceled_evidence() {
    //         have canceled >= (true);
    //         guard canceled_evidence >= Some(evidence);
    //         assert(pre.canceled_evidence.wf());
    //     }
    // }

    property! {
        positive_threads() {
            assert(pre.max_threads > 0);
        }
    }

    property! {
        not_too_many_entering() {
            have entering >= (pre.max_threads);
            assert(false);
        }
    }

    property! {
        not_too_many_waiters() {
            have waiting_on_result >= (pre.max_threads);
            assert(false);
        }
    }

    property! {
        consistent_readers(p0: PointsTo<Option<Result>>, p1: PointsTo<Option<Result>>) {
            have result_readers >= {p0};
            have result_readers >= {p1};
            assert(p0 == p1);
        }
    }

    property! {
        fresh_is_uninitialized() {
            require pre.control_state_initialized;
            have stage >= Some(Stage::Fresh);
            assert(false);
        }
    }

    property! {
        reader_implies_not_done() {
            have entering >= (1);
            have entered >= (true);
            assert(false);
        }
    }

    property! {
        entering_implies_not_done() {
            have stage >= Some(Stage::Entering);
            have entered >= (true);
            assert(false);
        }
    }

    property! {
        deposited_implies_not_done() {
            have stage >= Some(Stage::Deposited);
            have result >= (true);
            assert(false);
        }
    }

    property! {
        waiting_on_result_implies_not_done() {
            have waiting_on_result >= (1);
            have result >= (true);
            assert(false);
        }
    }

    property! {
        result_readers_implies_not_done(x: PointsTo<Option<Result>>) {
            have result_readers >= { x };
            have returned_duplicable >= (true);
            assert(false);
        }
    }

    property! {
        leader_must_be_initialized() {
            require !pre.control_state_initialized;
            have leader >= true;
            assert(false);
        }
    }

    property! {
        entered_cannot_cancel(canceled_evidence: Tix::Canceled) {
            have entered >= (true);
            have canceled >= Some(canceled_evidence);
            assert(false);
        }
    }

    property! {
        entered_cannot_begin_cancel(canceled_evidence: Tix::Canceled) {
            have entered >= (true);
            have canceled >= Some(canceled_evidence);
            assert(false);
        }
    }

});

proof fn check<R, T: StbTicketing<R>>(tracked c: &mut SingleThreadedMachine::entering<R, T>) {
    let n = c.count();
    let tracked part = c.split(n + 1);
}

fn main() {
}

} // verus!
