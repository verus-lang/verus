#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#[path = "support/llcrt_tagged_vstd_ext.rs"]
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

verified_tokenized_state_machine!(
BarrierMachine<Tix: Ticketing> {
    fields {
        // Each time we (re)initialize the barrier, we increment the generation.
        // All of the other resources are indexed by the generation in which they are created.
        #[sharding(variable)]
        pub generation: nat,

        /// Mutex-protected generation snapshot.
        #[sharding(variable)]
        pub generation_snapshot: nat,

        /// Generation snapshot associated with the entry-count atomic.
        #[sharding(variable)]
        pub generation_entry_snapshot: nat,

        #[sharding(constant)]
        pub access_count: nat,

        // Witness that the barrier is dormant.
        #[sharding(bool)]
        pub fresh: bool,

        // One element per access share, tagged with its generation.
        #[sharding(multiset)]
        pub access_gens: Multiset<nat>,

        // The number of threads that must enter the barrier for it to complete.
        #[sharding(persistent_map)]
        pub max_threads: Map<nat, nat>,

        #[sharding(persistent_map)]
        pub ticketing_instance: Map<nat, Tix::Instance>,

        #[sharding(persistent_set)]
        pub okay_to_exit: Set<nat>,

        #[sharding(persistent_set)]
        pub completed: Set<nat>,

        #[sharding(persistent_set)]
        pub canceled_gens: Set<nat>,

        #[sharding(variable)]
        pub state: BarrierMachineState,

        /// Keeps a copy of the state, so that when we hold the mutex, we can stash knowledge of the current state
        #[sharding(variable)]
        pub state_snapshot: BarrierMachineState,

        #[sharding(variable)]
        pub remain_to_enter: nat,

        /// Keeps a copy, so that when we hold the mutex, we can stash knowledge of its current value
        #[sharding(variable)]
        pub remain_to_enter_snapshot: nat,

        #[sharding(variable)]
        pub remain_to_exit: nat,

        /// Keeps a copy, so that when we hold the mutex, we can stash knowledge of its current value
        #[sharding(variable)]
        pub remain_to_exit_snapshot: nat,

        // Generation carried by the leader token.
        #[sharding(option)]
        pub leader: Option<nat>,

        // One generation-tagged token per follower awaiting exit.
        #[sharding(multiset)]
        pub followers: Multiset<nat>,

        #[sharding(storage_map)]
        pub exit_tickets: Map<nat, Tix::Exit>,  // Tickets to allow each thread to provably exit

        #[sharding(storage_option)]
        pub canceled_evidence: Option<Tix::Canceled>,
    }

    pub open spec fn is_initialized(&self) -> bool {
        self.max_threads.dom().contains(self.generation)
    }

    pub open spec fn max_threads_val(&self) -> nat
        recommends self.is_initialized(),
    {
        self.max_threads[self.generation]
    }

    pub open spec fn tix_instance_val(&self) -> Tix::Instance
        recommends self.is_initialized(),
    {
        self.ticketing_instance[self.generation]
    }

    pub open spec fn has_leader(&self) -> bool {
        self.leader is Some
    }

    pub open spec fn num_followers(&self) -> nat {
        self.followers.len()
    }

    #[invariant]
    pub fn inv(&self) -> bool {
        use BarrierMachineState::*;

        &&& self.generation == self.generation_snapshot
        &&& (self.remain_to_enter_snapshot > 0 ==> self.generation == self.generation_entry_snapshot)
        &&& (self.max_threads.dom().contains(self.generation) <==> self.ticketing_instance.dom().contains(self.generation))

        &&& (forall|g: nat| #[trigger] self.max_threads.dom().contains(g) ==> g <= self.generation)
        &&& (forall|g: nat| #[trigger] self.ticketing_instance.dom().contains(g) ==> g <= self.generation)
        &&& (forall|g: nat| #[trigger] self.okay_to_exit.contains(g) ==> g < self.generation || (g == self.generation && (self.state == Completed || self.state == Canceled)))
        &&& (forall|g: nat| #[trigger] self.completed.contains(g) ==> g < self.generation || (g == self.generation && self.state_snapshot == Completed))
        &&& (forall|g: nat| #[trigger] self.canceled_gens.contains(g) ==> g < self.generation || (g == self.generation && self.state_snapshot == Canceled))
        &&& (forall|g: nat| #[trigger] self.okay_to_exit.contains(g) ==> self.max_threads.dom().contains(g) && self.ticketing_instance.dom().contains(g))
        &&& (forall|g: nat| #[trigger] self.completed.contains(g) ==> self.max_threads.dom().contains(g) && self.ticketing_instance.dom().contains(g))
        &&& (forall|g: nat| #[trigger] self.canceled_gens.contains(g) ==> self.max_threads.dom().contains(g) && self.ticketing_instance.dom().contains(g))
        &&& (forall|g: nat| self.completed.contains(g) ==> !self.canceled_gens.contains(g))
        &&& (forall|g: nat| self.canceled_gens.contains(g) ==> !self.completed.contains(g))

        &&& (self.state == Dormant <==> !self.is_initialized())
        &&& ((self.state_snapshot == Dormant || self.state_snapshot == Resetting || self.state_snapshot == ResettingExit) <==> !self.is_initialized())

        &&& (self.leader matches Some(g) ==> g == self.generation)
        &&& (forall|g: nat| #[trigger] self.followers.count(g) > 0 ==> g == self.generation)
        &&& (forall|g: nat| #[trigger] self.access_gens.count(g) > 0 ==> g == self.generation)
        &&& (self.is_initialized() ==> self.access_gens =~= Multiset::from_map(Map::empty().insert(self.generation, self.access_count)))
        &&& (!self.is_initialized() ==> self.access_gens =~= Multiset::empty())

        &&& (self.fresh ==> self.state == Dormant)

        // Transient states occur only in `state_snapshot`.
        &&& (self.state != Initializing)
        &&& (self.state != Resetting)
        &&& (self.state != ResettingExit)
        &&& (self.state_snapshot == Initializing ==> self.state == Blocked)
        &&& (self.state_snapshot == Resetting ==> self.state == Dormant)
        &&& (self.state_snapshot == ResettingExit ==> self.state == Dormant)
        // The entry count may diverge from its snapshot only during a transition.
        &&& ((self.state_snapshot != Initializing && self.state_snapshot != Resetting) ==> self.remain_to_enter == self.remain_to_enter_snapshot)
        &&& (self.remain_to_enter_snapshot > 0 ==> self.remain_to_enter == self.remain_to_enter_snapshot)
        // The mutex snapshot may lag decrements of `remain_to_exit`.
        &&& self.remain_to_exit_snapshot >= self.remain_to_exit
        &&& (self.has_leader() ==> self.state_snapshot == Completed || self.state_snapshot == LeaderEntering)
        &&& (self.okay_to_exit.contains(self.generation) <==> (self.state == Completed || self.state == Canceled))
        &&& (self.remain_to_enter > 0 ==> !self.has_leader())
        &&& (self.state_snapshot != Completed ==> self.exit_tickets.is_empty())
        &&& (self.state_snapshot == Completed <==> self.completed.contains(self.generation))
        &&& (self.state_snapshot == Canceled <==> self.canceled_evidence is Some)
        &&& (self.state_snapshot == Initializing ==> !self.has_leader() && self.num_followers() == 0)
        &&& (self.state_snapshot == Resetting ==> !self.has_leader() && self.num_followers() == 0)
        &&& (self.state_snapshot == ResettingExit ==> !self.has_leader() && self.num_followers() == 0)
        &&& ((self.is_initialized() && self.state_snapshot != Initializing) ==> self.num_followers() < self.max_threads_val())
        &&& (self.state == Blocked ==> self.max_threads_val() > 0)

        // Invariants depending on the state_snapshot, which sometimes deviates from the actual state
        &&& (match self.state_snapshot {
            Dormant => {
                &&& self.state == Dormant
                &&& !self.has_leader()
                &&& self.remain_to_enter == 0
                &&& self.remain_to_enter_snapshot == 0
                &&& self.remain_to_exit == 0
                &&& self.num_followers() == 0
            }
            Initializing => {
                &&& self.state == Blocked
                &&& !self.has_leader()
                &&& self.num_followers() == 0
                &&& self.is_initialized()
            }
            Resetting => {
                &&& self.state == Dormant
                &&& !self.has_leader()
                &&& self.num_followers() == 0
                &&& !self.is_initialized()
                &&& self.remain_to_enter_snapshot == 0
            }
            ResettingExit => {
                &&& self.state == Dormant
                &&& !self.has_leader()
                &&& self.num_followers() == 0
                &&& !self.is_initialized()
                &&& self.remain_to_enter == 0
                &&& self.remain_to_enter_snapshot == 0
            }
            Blocked | Completed | Canceled => self.state == self.state_snapshot,
            LeaderEntering => {
                &&& self.has_leader()
                &&& self.remain_to_enter == 0
                &&& self.remain_to_enter_snapshot == 0
                &&& self.is_initialized()
                &&& self.remain_to_exit == self.max_threads_val()
                &&& (self.remain_to_enter + self.num_followers() + 1 == self.max_threads_val())
                &&& self.state == Blocked
            }
        })

        // Invariants depending on the actual state
        &&& ({match self.state {
            Dormant => {
                    &&& !self.has_leader()
                    &&& self.num_followers() == 0
                    // Counter clearing completes after the state becomes dormant.
                    &&& ((self.state_snapshot != Resetting && self.state_snapshot != ResettingExit) ==> {
                        &&& self.remain_to_enter == 0
                        &&& self.remain_to_exit == 0
                        &&& self.remain_to_exit_snapshot == 0
                    })
                }
                Initializing => false,
                Resetting => false,
                ResettingExit => false,
                Blocked => {
                    &&& self.is_initialized()
                    &&& (self.state_snapshot != LeaderEntering && self.state_snapshot != Initializing ==>
                        {
                            &&& !self.has_leader()
                            &&& self.remain_to_enter > 0
                            &&& self.remain_to_exit == self.max_threads_val()
                            &&& (self.remain_to_enter + self.num_followers() == self.max_threads_val())
                        })
                }
                LeaderEntering => false,
                Completed => {
                    &&& self.is_initialized()
                    &&& self.remain_to_enter == 0
                    &&& (self.remain_to_exit == self.num_followers() + if self.has_leader() { 1nat } else { 0 })
                    &&& (TicketMap::valid(self.exit_tickets, 0, self.num_followers(), self.tix_instance_val()))
                    &&& self.exit_tickets.dom() =~= Set::<nat>::range(0, self.num_followers())
                }
                Canceled => {
                    &&& self.is_initialized()
                    &&& !self.has_leader()
                    &&& self.remain_to_enter > 0
                    &&& self.remain_to_exit == self.remain_to_enter + self.num_followers()
                }
            }
        })
    }

    init! {
        new(access_count: nat) {
            init generation = 0;
            init generation_snapshot = 0;
            init generation_entry_snapshot = 0;
            init access_count = access_count;
            init fresh = true;
            init access_gens = Multiset::empty();
            init max_threads = Map::empty();
            init ticketing_instance = Map::empty();
            init okay_to_exit = Set::empty();
            init completed = Set::empty();
            init canceled_gens = Set::empty();
            init state = BarrierMachineState::Dormant;
            init state_snapshot = BarrierMachineState::Dormant;
            init remain_to_enter = 0;
            init remain_to_enter_snapshot = 0;
            init remain_to_exit = 0;
            init remain_to_exit_snapshot = 0;
            init leader = None;
            init followers = Multiset::empty();
            init exit_tickets = Map::empty();
            init canceled_evidence = None;
        }
    }

    #[inductive(new)]
    fn new_inductive(post: Self, access_count: nat) {
    }

    // A fresh token proves the state is dormant. The mutex invariant excludes reset snapshots,
    // allowing a mutex holder to conclude that the snapshot is also dormant.
    property! {
        fresh_is_dormant() {
            have fresh >= true;
            require(pre.state_snapshot != BarrierMachineState::Resetting
                 && pre.state_snapshot != BarrierMachineState::ResettingExit);
            assert(pre.state_snapshot == BarrierMachineState::Dormant);
        }
    }

    // The state transition advances the generation and enters `Initializing`; the entry and
    // exit transitions then reset their counts. A drained mutex snapshot proves no threads remain.

    transition! {
        reinit_state_from_completed(num_threads: nat, ticketing_instance_in: Tix::Instance) {
            require(pre.state == BarrierMachineState::Completed);
            require(num_threads > 0);
            require(pre.remain_to_exit_snapshot == 0);
            remove access_gens -= (Multiset::from_map(Map::empty().insert(pre.generation, pre.access_count)));
            add max_threads (union)= [(pre.generation + 1) as nat => num_threads];
            add ticketing_instance (union)= [(pre.generation + 1) as nat => ticketing_instance_in];
            add access_gens += (Multiset::from_map(Map::empty().insert((pre.generation + 1) as nat, pre.access_count)));
            update state = BarrierMachineState::Blocked;
            update state_snapshot = BarrierMachineState::Initializing;
            update generation = (pre.generation + 1) as nat;
            update generation_snapshot = (pre.generation + 1) as nat;
            // Decouple the entry snapshot until the entry atomic is updated.
            update remain_to_enter_snapshot = 0;
        }
    }

    #[inductive(reinit_state_from_completed)]
    fn reinit_state_from_completed_inductive(pre: Self, post: Self, num_threads: nat, ticketing_instance_in: Tix::Instance) {
    }

    transition! {
        reinit_state_from_canceled(num_threads: nat, ticketing_instance_in: Tix::Instance) {
            require(pre.state == BarrierMachineState::Canceled);
            require(num_threads > 0);
            require(pre.remain_to_exit_snapshot == pre.remain_to_enter_snapshot);
            remove access_gens -= (Multiset::from_map(Map::empty().insert(pre.generation, pre.access_count)));
            withdraw canceled_evidence -= Some(let _canceled_ev);
            add max_threads (union)= [(pre.generation + 1) as nat => num_threads];
            add ticketing_instance (union)= [(pre.generation + 1) as nat => ticketing_instance_in];
            add access_gens += (Multiset::from_map(Map::empty().insert((pre.generation + 1) as nat, pre.access_count)));
            update state = BarrierMachineState::Blocked;
            update state_snapshot = BarrierMachineState::Initializing;
            update generation = (pre.generation + 1) as nat;
            update generation_snapshot = (pre.generation + 1) as nat;
            // Decouple the entry snapshot until the entry atomic is updated.
            update remain_to_enter_snapshot = 0;
        }
    }

    #[inductive(reinit_state_from_canceled)]
    fn reinit_state_from_canceled_inductive(pre: Self, post: Self, num_threads: nat, ticketing_instance_in: Tix::Instance) {
    }

    // `Resetting` and `ResettingExit` bridge the entry and exit atomic updates. The reset consumes
    // all access shares and restores `fresh` without minting resources for the new generation.

    transition! {
        reinit_dormant_from_completed() {
            require(pre.state == BarrierMachineState::Completed);
            require(pre.remain_to_exit_snapshot == 0);
            remove access_gens -= (Multiset::from_map(Map::empty().insert(pre.generation, pre.access_count)));
            add fresh += true;
            update state = BarrierMachineState::Dormant;
            update state_snapshot = BarrierMachineState::Resetting;
            update generation = (pre.generation + 1) as nat;
            update generation_snapshot = (pre.generation + 1) as nat;
            update remain_to_enter_snapshot = 0;
        }
    }

    #[inductive(reinit_dormant_from_completed)]
    fn reinit_dormant_from_completed_inductive(pre: Self, post: Self) {
    }

    transition! {
        reinit_dormant_from_canceled() {
            require(pre.state == BarrierMachineState::Canceled);
            require(pre.remain_to_exit_snapshot == pre.remain_to_enter_snapshot);
            remove access_gens -= (Multiset::from_map(Map::empty().insert(pre.generation, pre.access_count)));
            withdraw canceled_evidence -= Some(let _canceled_ev);
            add fresh += true;
            update state = BarrierMachineState::Dormant;
            update state_snapshot = BarrierMachineState::Resetting;
            update generation = (pre.generation + 1) as nat;
            update generation_snapshot = (pre.generation + 1) as nat;
            // Decouple the snapshot until the entry atomic clears the residual count.
            update remain_to_enter_snapshot = 0;
        }
    }

    #[inductive(reinit_dormant_from_canceled)]
    fn reinit_dormant_from_canceled_inductive(pre: Self, post: Self) {
    }

    transition! {
        reinit_dormant_clear_enter() {
            require(pre.state_snapshot == BarrierMachineState::Resetting);
            update remain_to_enter = 0;
            update state_snapshot = BarrierMachineState::ResettingExit;
            update generation_entry_snapshot = pre.generation_snapshot;
        }
    }

    #[inductive(reinit_dormant_clear_enter)]
    fn reinit_dormant_clear_enter_inductive(pre: Self, post: Self) { }

    transition! {
        reinit_dormant_finish() {
            require(pre.state_snapshot == BarrierMachineState::ResettingExit);
            update remain_to_exit = 0;
            update remain_to_exit_snapshot = 0;
            update state_snapshot = BarrierMachineState::Dormant;
        }
    }

    #[inductive(reinit_dormant_finish)]
    fn reinit_dormant_finish_inductive(pre: Self, post: Self) { }

    transition! {
        initialize_state(num_threads: nat, ticketing_instance_in: Tix::Instance) {
            require(pre.state == BarrierMachineState::Dormant);
            require(num_threads > 0);
            remove fresh -= true;
            add max_threads (union)= [pre.generation => num_threads];
            add ticketing_instance (union)= [pre.generation => ticketing_instance_in];
            add access_gens += (Multiset::from_map(Map::empty().insert(pre.generation, pre.access_count)));
            update state = BarrierMachineState::Blocked;
            update state_snapshot = BarrierMachineState::Initializing;
        }
    }

    #[inductive(initialize_state)]
    fn initialize_state_inductive(pre: Self, post: Self, num_threads: nat, ticketing_instance_in: Tix::Instance) {
    }

    transition! {
        initialize_remain_to_enter() {
            // We can only observe state_snapshot here, not state (which lives
            // in the state atomic); an invariant links the two.
            require(pre.state_snapshot == BarrierMachineState::Initializing);
            have max_threads >= [pre.generation_snapshot => let mt];
            update remain_to_enter = mt;
            update remain_to_enter_snapshot = mt;
            update generation_entry_snapshot = pre.generation_snapshot;
        }
    }

    #[inductive(initialize_remain_to_enter)]
    fn initialize_remain_to_enter_inductive(pre: Self, post: Self) { }

    transition! {
        initialize_finish() {
            require(pre.state_snapshot == BarrierMachineState::Initializing);
            have max_threads >= [pre.generation_snapshot => let mt];
            require(pre.remain_to_enter_snapshot == mt);
            update remain_to_exit = mt;
            update remain_to_exit_snapshot = mt;
            update state_snapshot = BarrierMachineState::Blocked;
        }
    }

    #[inductive(initialize_finish)]
    fn initialize_finish_inductive(pre: Self, post: Self) { }

    transition! {
        drain_sync() {
            update remain_to_exit_snapshot = pre.remain_to_exit;
        }
    }

    #[inductive(drain_sync)]
    fn drain_sync_inductive(pre: Self, post: Self) { }

    transition! {
        cancel(canceled_evidence_in: Tix::Canceled) {
            require(pre.state_snapshot != BarrierMachineState::LeaderEntering);
            require(pre.state_snapshot != BarrierMachineState::Initializing);
            require(pre.state == BarrierMachineState::Blocked);
            have ticketing_instance >= [pre.generation => let ti];
            require(canceled_evidence_in.wf(&ti));
            update state = BarrierMachineState::Canceled;
            update state_snapshot = BarrierMachineState::Canceled;
            add okay_to_exit (union)= set { pre.generation };
            add canceled_gens (union)= set { pre.generation };
            deposit canceled_evidence += Some(canceled_evidence_in);
        }
    }

    #[inductive(cancel)]
    fn cancel_inductive(pre: Self, post: Self, canceled_evidence_in: Tix::Canceled) {
    }

    transition! {
        enter_leader_begin() {
            require(pre.state_snapshot == BarrierMachineState::Blocked);
            require(pre.remain_to_enter == 1);
            update remain_to_enter = 0;
            update remain_to_enter_snapshot = 0;
            // The entry atomic uses the mutex's generation snapshot.
            add leader += Some(pre.generation_snapshot);
            update state_snapshot = BarrierMachineState::LeaderEntering;
        }
    }

    #[inductive(enter_leader_begin)]
    fn enter_leader_begin_inductive(pre: Self, post: Self) {
    }

    transition! {
        enter_leader_finish(tickets: Map<nat, Tix::Exit>) {
            require(pre.state_snapshot == BarrierMachineState::LeaderEntering);
            have ticketing_instance >= [pre.generation => let ti];
            have max_threads >= [pre.generation => let mt];
            require(TicketMap::valid(tickets, 0, (mt - 1) as nat, ti));
            require(tickets.dom() =~= Set::<nat>::range(0, (mt - 1) as nat));
            have leader >= Some(pre.generation);
            update state = BarrierMachineState::Completed;
            update state_snapshot = BarrierMachineState::Completed;
            add okay_to_exit (union)= set { pre.generation };
            add completed (union)= set { pre.generation };
            deposit exit_tickets += (tickets);
        }
    }

    #[inductive(enter_leader_finish)]
    fn enter_leader_finish_inductive(pre: Self, post: Self, tickets: Map<nat, Tix::Exit>) {
    }

    transition! {
        enter_follower() {
            require(pre.state_snapshot == BarrierMachineState::Blocked);
            require(pre.remain_to_enter > 1);
            update remain_to_enter = (pre.remain_to_enter - 1) as nat;
            update remain_to_enter_snapshot = (pre.remain_to_enter - 1) as nat;
            // The entry atomic uses the mutex's generation snapshot.
            add followers += { pre.generation_snapshot };
        }
    }

    #[inductive(enter_follower)]
    fn enter_follower_inductive(pre: Self, post: Self) { }

    // Exit tokens carry the generation because its token is unavailable in the exit atomic.

    transition! {
        exit_leader(gen: nat) {
            remove leader -= Some(gen);
            // Completion disambiguates `Completed` from `LeaderEntering`.
            have completed >= set { gen };
            assert(pre.remain_to_exit > 0);
            update remain_to_exit = (pre.remain_to_exit - 1) as nat;
        }
    }

    #[inductive(exit_leader)]
    fn exit_leader_inductive(pre: Self, post: Self, gen: nat) {
        assert(pre.state == BarrierMachineState::Completed);
    }

    transition! {
        exit_follower_completed(gen: nat) {
            remove followers -= { gen };
            have completed >= set { gen };
            have ticketing_instance >= [gen => let ti];
            assert(pre.remain_to_exit > 0);
            update remain_to_exit = (pre.remain_to_exit - 1) as nat;
            withdraw exit_tickets -= [(pre.followers.len() - 1) as nat => let exit_ticket];
            birds_eye let ticket = pre.exit_tickets[(pre.followers.len() - 1) as nat];
            assert(ticket == exit_ticket && ticket.wf(&ti) && !ticket.is_leader());
        }
    }

    #[inductive(exit_follower_completed)]
    fn exit_follower_completed_inductive(pre: Self, post: Self, gen: nat) {
        assert(post.exit_tickets.dom() =~= Set::<nat>::range(0, post.followers.len())) by {}
    }

    transition! {
        exit_follower_canceled(gen: nat) {
            remove followers -= { gen };
            have canceled_gens >= set { gen };
            assert(pre.remain_to_exit > 0);
            update remain_to_exit = (pre.remain_to_exit - 1) as nat;
        }
    }

    #[inductive(exit_follower_canceled)]
    fn exit_follower_canceled_inductive(pre: Self, post: Self, gen: nat) {
        use BarrierMachineState::*;
    }

    property! {
        state_snapshot_matches_state() {
            assert(match pre.state_snapshot {
                BarrierMachineState::Dormant => pre.state == BarrierMachineState::Dormant,
                BarrierMachineState::Initializing => pre.state == BarrierMachineState::Blocked,
                BarrierMachineState::Resetting | BarrierMachineState::ResettingExit => pre.state == BarrierMachineState::Dormant,
                BarrierMachineState::Blocked | BarrierMachineState::Completed | BarrierMachineState::Canceled => pre.state == pre.state_snapshot,
                BarrierMachineState::LeaderEntering => pre.state == BarrierMachineState::Blocked
            });
        }
    }

    // An access share pins the barrier to its initialized generation.
    property! {
        not_dormant(gen: nat) {
            have access_gens >= (Multiset::empty().insert(gen));
            assert(Multiset::<nat>::empty().insert(gen).count(gen) == 1);
            assert(gen == pre.generation);
            assert(pre.state != BarrierMachineState::Dormant);
            assert(pre.state_snapshot != BarrierMachineState::Dormant);
        }
    }

    // An access share pins the mutex snapshot to the same generation.
    property! {
        access_gen_matches_snapshot(gen: nat) {
            have access_gens >= (Multiset::empty().insert(gen));
            assert(Multiset::<nat>::empty().insert(gen).count(gen) == 1);
            assert(gen == pre.generation_snapshot);
        }
    }

    property! {
        state_not_dormant(gen: nat) {
            have access_gens >= (Multiset::empty().insert(gen));
            assert(Multiset::<nat>::empty().insert(gen).count(gen) == 1);
            assert(gen == pre.generation);
            assert(pre.state != BarrierMachineState::Dormant);
        }
    }

    property! {
        enter_snapshot_matches() {
            require(pre.state_snapshot != BarrierMachineState::Initializing);
            require(pre.state_snapshot != BarrierMachineState::Resetting);
            assert(pre.remain_to_enter_snapshot == pre.remain_to_enter);
        }
    }

    property! {
        blocked_means_positive_remain_to_enter() {
            assert(pre.state_snapshot == BarrierMachineState::Blocked ==> pre.remain_to_enter > 0);
        }
    }

    property! {
        dormant_means_zero_remain_to_exit() {
            require(pre.state_snapshot == BarrierMachineState::Dormant);
            assert(pre.remain_to_exit == 0);
        }
    }

    property! {
        positive_remain_to_enter() {
            assert({
                &&& pre.state_snapshot == BarrierMachineState::Blocked ==> pre.remain_to_enter > 0
                &&& pre.state_snapshot == BarrierMachineState::Canceled ==> pre.remain_to_enter > 0
                &&& pre.state_snapshot == BarrierMachineState::Completed ==> pre.remain_to_enter == 0
                &&& pre.state_snapshot == BarrierMachineState::Dormant ==> pre.remain_to_enter == 0
            });
        }
    }

    property! {
        generation_matches() {
            assert(pre.generation == pre.generation_snapshot);
        }
    }

    // A positive entry snapshot is tagged with the mutex generation.
    property! {
        entry_gen_matches_mutex_gen() {
            require(pre.remain_to_enter_snapshot > 0);
            assert(pre.generation_entry_snapshot == pre.generation_snapshot);
        }
    }
});

fn main() {
}

} // verus!
