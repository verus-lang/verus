// rust_verify/tests/example.rs expect-warnings
#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
#![allow(unused_imports)]

// port of single-writer_state single-reader_state queue from LinearDafny
// https://github.com/vmware-labs/verified-betrfs/tree/concurrency-experiments/concurrency/spsc-queue

// ANCHOR:full
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::cell::*;
use vstd::map::*;
use vstd::modes::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::{pervasive::*, prelude::*, *};

verus! {

use verus_state_machines_macros::verified_tokenized_state_machine;

// ANCHOR: enum_state
#[is_variant]
pub enum ProducerState {
    Idle(nat),  // local copy of writer_pos
    Producing(nat),
}

#[is_variant]
pub enum ConsumerState {
    Idle(nat),  // local copy of reader_pos
    Consuming(nat),
}

// ANCHOR_END: enum_state
// ANCHOR: fields
verified_tokenized_state_machine!{

#[verified_local_ready(produce_start, produce_end, consume_start, consume_end)]
RingState<T> {
    fields {
        // IDs of the cells used in the ring buffer.
        // These are fixed throughout the protocol.

        #[sharding(constant)]
        pub cell_ids: Seq<CellId>,

        // All the stored permissions

        #[sharding(storage_map)]
        pub physical_cells: Map<nat, cell::PointsTo<T>>,

        // Represents the shared `reader_pos` field

        #[sharding(variable)]
        pub reader_pos: nat,

        // Represents the shared `writer_pos` field

        #[sharding(variable)]
        pub writer_pos: nat,

        // Represents the local state of the single-writer_state

        #[sharding(variable)]
        pub writer_state: ProducerState,

        // Represents the local state of the single-reader_state

        #[sharding(variable)]
        pub reader_state: ConsumerState,
    }
    // ANCHOR_END: fields

    pub open spec fn len(&self) -> nat {
        self.cell_ids.len()
    }

    // ANCHOR: inc_wrap
    pub open spec fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }
    // ANCHOR_END: inc_wrap

    // Make sure the writer_state state and the reader_state state aren't inconsistent.

    #[invariant]
    pub fn not_overlapping(&self) -> bool {
        match (self.writer_state, self.reader_state) {
            (ProducerState::Producing(writer_pos), ConsumerState::Idle(reader_pos)) => {
                Self::inc_wrap(writer_pos, self.len()) != reader_pos
            }
            (ProducerState::Producing(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                reader_pos != writer_pos
                && Self::inc_wrap(writer_pos, self.len()) != reader_pos
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Idle(reader_pos)) => {
                true
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                reader_pos != writer_pos
            }
        }
    }

    // `reader_pos` and `writer_pos` are in-bounds
    // shared `reader_pos` and `writer_pos` fields agree with the ProducerState and ConsumerState

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        0 <= self.reader_pos && self.reader_pos < self.len() &&
        0 <= self.writer_pos && self.writer_pos < self.len()
        && match self.writer_state {
            ProducerState::Producing(writer_pos) => {
                self.writer_pos == writer_pos
            }
            ProducerState::Idle(writer_pos) => {
                self.writer_pos == writer_pos
            }
        }
        && match self.reader_state {
            ConsumerState::Consuming(reader_pos) => {
                self.reader_pos == reader_pos
            }
            ConsumerState::Idle(reader_pos) => {
                self.reader_pos == reader_pos
            }
        }
    }

    // Indicates whether we expect the cell at index `i` to be full based on
    // the values of the `reader_pos` and `writer_pos`.

    pub open spec fn in_active_range(&self, i: nat) -> bool {
        // Note that self.reader_pos = self.writer_pos means empty range
        0 <= i && i < self.len() && (
            if self.reader_pos <= self.writer_pos {
                self.reader_pos <= i && i < self.writer_pos
            } else {
                i >= self.reader_pos || i < self.writer_pos
            }
        )
    }

    // Indicates whether we expect a cell to be checked out or not,
    // based on the writer_state/reader_state state.

    pub open spec fn is_checked_out(&self, i: nat) -> bool {
        self.writer_state == ProducerState::Producing(i)
        || self.reader_state == ConsumerState::Consuming(i)
    }

    // Predicate to determine that the state at cell index `i`
    // is correct. For each index, there are three possibilities:
    //
    //  1. No cell permission is stored
    //  2. Permission is stored; permission indicates a full cell
    //  3. Permission is stored; permission indicates an empty cell
    //
    // Which of these 3 possibilities we should be in depends on the
    // writer_state/reader_state/reader_pos/writer_pos state.

    pub open spec fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            // No cell permission is stored
            !self.physical_cells.dom().contains(i)
        } else {
            // Permission is stored
            self.physical_cells.dom().contains(i)

            // Permission must be for the correct cell:
            && self.physical_cells.index(i).id() == self.cell_ids.index(i as int)

            && if self.in_active_range(i) {
                // The cell is full
                self.physical_cells.index(i).is_init()
            } else {
                // The cell is empty
                self.physical_cells.index(i).is_uninit()
            }
        }
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall|i: nat| 0 <= i && i < self.len() ==>
            self.valid_storage_at_idx(i)
    }

    init!{
        initialize(cell_ids: Seq<CellId>, physical_cells: Map<nat, cell::PointsTo<T>>) {
            // Upon initialization, the user needs to deposit _all_ the relevant
            // cell permissions to start with. Each permission should indicate
            // an empty cell.

            require(
                (forall|i: nat| 0 <= i && i < cell_ids.len() ==>
                    #[trigger] physical_cells.dom().contains(i)
                    && physical_cells.index(i).id() == cell_ids.index(i as int)
                    && physical_cells.index(i).is_uninit())
            );
            require(cell_ids.len() > 0);

            init cell_ids = cell_ids;
            init physical_cells = physical_cells;
            init reader_pos = 0;
            init writer_pos = 0;
            init writer_state = ProducerState::Idle(0);
            init reader_state = ConsumerState::Idle(0);
        }
    }

    // ANCHOR: transition_produce_start
    transition!{
        produce_start() {
            // In order to begin, we have to be in ProducerState::Idle.
            require(pre.writer_state.is_Idle());

            // We'll be comparing the writer_state's _local_ copy of the writer_pos
            // with the _shared_ version of the reader_pos.
            let writer_pos = pre.writer_state.get_Idle_0();
            let reader_pos = pre.reader_pos;

            assert(0 <= writer_pos && writer_pos < pre.cell_ids.len());

            // Compute the incremented writer_pos, wrapping around if necessary.
            let next_tail = Self::inc_wrap(writer_pos, pre.cell_ids.len());

            // We have to check that the buffer isn't full to proceed.
            require(next_tail != reader_pos);

            // Update the writer_state's local state to be in the `Producing` state.
            update writer_state = ProducerState::Producing(writer_pos);

            // Withdraw ("check out") the permission stored at index `writer_pos`.
            // This creates a proof obligation for the transition system to prove that
            // there is actually a permission stored at this index.
            withdraw physical_cells -= [writer_pos => let perm] by {
                assert(pre.valid_storage_at_idx(writer_pos));
            };

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `writer_pos` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                perm.id() == pre.cell_ids.index(writer_pos as int)
                && perm.is_uninit()
            ) by {
                assert(!pre.in_active_range(writer_pos));
                assert(pre.valid_storage_at_idx(writer_pos));
            };
        }
    }
    // ANCHOR_END: transition_produce_start

    // ANCHOR: transition_produce_end
    transition!{
        // This transition is parameterized by the value of the permission
        // being inserted. Since the permission is being deposited
        // (coming from "outside" the system) we can't compute it as a
        // function of the current state, unlike how we did it for the
        // `produce_start` transition).
        produce_end(perm: cell::PointsTo<T>) {
            // In order to complete the produce step,
            // we have to be in ProducerState::Producing.
            require(pre.writer_state.is_Producing());
            let writer_pos = pre.writer_state.get_Producing_0();

            assert(0 <= writer_pos && writer_pos < pre.cell_ids.len());

            // Compute the incremented writer_pos, wrapping around if necessary.
            let next_tail = Self::inc_wrap(writer_pos, pre.cell_ids.len());

            // This time, we don't need to compare the `reader_pos` and `writer_pos` - we already
            // check that, and anyway, we don't have access to the `reader_pos` field
            // for this transition. (This transition is supposed to occur while
            // modifying the `writer_pos` field, so we can't do both.)

            // However, we _do_ need to check that the permission token being
            // checked in satisfies its requirements. It has to be associated
            // with the correct cell, and it has to be full.

            require(perm.id() == pre.cell_ids.index(writer_pos as int)
              && perm.is_init());

            // Perform our updates. Update the writer_pos to the computed value,
            // both the shared version and the writer_state's local copy.
            // Also, move back to the Idle state.
            update writer_state = ProducerState::Idle(next_tail);
            update writer_pos = next_tail;

            // Check the permission back into the physical_cells map.
            deposit physical_cells += [writer_pos => perm] by { assert(pre.valid_storage_at_idx(writer_pos)); };
        }
    }
    // ANCHOR_END: transition_produce_end

    transition!{
        consume_start() {
            // In order to begin, we have to be in ConsumerState::Idle.
            require(pre.reader_state.is_Idle());

            // We'll be comparing the reader_state's _local_ copy of the reader_pos
            // with the _shared_ version of the writer_pos.
            let reader_pos = pre.reader_state.get_Idle_0();
            let writer_pos = pre.writer_pos;

            assert(0 <= reader_pos && reader_pos < pre.cell_ids.len());

            // We have to check that the buffer isn't empty to proceed.
            require(reader_pos != writer_pos);

            // Update the reader_state's local state to be in the `Consuming` state.
            update reader_state = ConsumerState::Consuming(reader_pos);

            // Withdraw ("check out") the permission stored at index `writer_pos`.

            birds_eye let perm = pre.physical_cells.index(reader_pos);
            withdraw physical_cells -= [reader_pos => perm] by {
                assert(pre.valid_storage_at_idx(reader_pos));
            };

            assert(perm.id() == pre.cell_ids.index(reader_pos as int)) by {
                assert(pre.valid_storage_at_idx(reader_pos));
            };
            assert(perm.is_init()) by {
                assert(pre.in_active_range(reader_pos));
                assert(pre.valid_storage_at_idx(reader_pos));
            };
        }
    }

    transition!{
        consume_end(perm: cell::PointsTo<T>) {
            require(pre.reader_state.is_Consuming());
            let reader_pos = pre.reader_state.get_Consuming_0();

            assert(0 <= reader_pos && reader_pos < pre.cell_ids.len());
            let next_head = Self::inc_wrap(reader_pos, pre.cell_ids.len());

            update reader_state = ConsumerState::Idle(next_head);
            update reader_pos = next_head;

            require(perm.id() == pre.cell_ids.index(reader_pos as int)
              && perm.is_uninit());
            deposit physical_cells += [reader_pos => perm] by { assert(pre.valid_storage_at_idx(reader_pos)); };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, cell_ids: Seq<CellId>, physical_cells: Map<nat, cell::PointsTo<T>>) {
        assert forall|i: nat|
            0 <= i && i < post.len() implies post.valid_storage_at_idx(i)
        by {
            assert(post.physical_cells.dom().contains(i));
            /*
            assert(
                post.physical_cells.index(i).id() ==
                post.cell_ids.index(i)
            );
            assert(if post.in_active_range(i) {
                post.physical_cells.index(i).value.is_Some()
            } else {
                post.physical_cells.index(i).value.is_None()
            });*/
        }
    }

    //// Invariant proofs

    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        let writer_pos = pre.writer_state.get_Idle_0();
        assert(!pre.in_active_range(writer_pos));
        match (post.writer_state, post.reader_state) {
            (ProducerState::Producing(writer_pos), ConsumerState::Idle(reader_pos)) => {
                assert(Self::inc_wrap(writer_pos, post.len()) != reader_pos);
            }
            (ProducerState::Producing(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                assert(reader_pos != writer_pos);
                assert(Self::inc_wrap(writer_pos, post.len()) != reader_pos);
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Idle(reader_pos)) => {
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                assert(reader_pos != writer_pos);
            }
        }
        assert(forall|i| pre.valid_storage_at_idx(i) ==> post.valid_storage_at_idx(i));
    }

    #[inductive(produce_end)]
    fn produce_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        assert forall |i|
            pre.valid_storage_at_idx(i) implies
            post.valid_storage_at_idx(i)
        by {
            /*if post.is_checked_out(i) {
                assert(!post.physical_cells.dom().contains(i));
            } else {
                assert(post.physical_cells.dom().contains(i));
                assert(
                    post.physical_cells.index(i).id() ==
                    post.cell_ids.index(i)
                );
                assert(if post.in_active_range(i) {
                    post.physical_cells.index(i).value.is_Some()
                } else {
                    post.physical_cells.index(i).value.is_None()
                });
            }*/
        }
    }

    #[inductive(consume_start)]
    fn consume_start_inductive(pre: Self, post: Self) {
        assert forall |i|
            pre.valid_storage_at_idx(i) implies post.valid_storage_at_idx(i)
        by { }
    }

    #[inductive(consume_end)]
    fn consume_end_inductive(pre: Self, post: Self, perm: cell::PointsTo<T>) {
        let reader_pos = pre.reader_state.get_Consuming_0();
        assert(post.physical_cells.dom().contains(reader_pos));
        assert(
                post.physical_cells.index(reader_pos).id() ==
                post.cell_ids.index(reader_pos as int)
            );
        assert(if post.in_active_range(reader_pos) {
                post.physical_cells.index(reader_pos).is_init()
            } else {
                post.physical_cells.index(reader_pos).is_uninit()
            });

        match (pre.writer_state, pre.reader_state) {
            (ProducerState::Producing(writer_pos), ConsumerState::Idle(reader_pos)) => {
                assert(pre.reader_pos != pre.writer_pos);
            }
            (ProducerState::Producing(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                assert(pre.reader_pos != pre.writer_pos);
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Idle(reader_pos)) => {
                assert(pre.reader_pos != pre.writer_pos);
            }
            (ProducerState::Idle(writer_pos), ConsumerState::Consuming(reader_pos)) => {
                assert(pre.reader_pos != pre.writer_pos);
            }
        };

        assert(pre.reader_pos != pre.writer_pos);
        assert(!post.is_checked_out(reader_pos));
        assert(post.valid_storage_at_idx(reader_pos));

        assert forall |i|
            pre.valid_storage_at_idx(i) implies post.valid_storage_at_idx(i)
        by { }
    }
}}
// ANCHOR: impl_queue_struct


struct_with_invariants!{
    struct Queue<T> {
        buffer: Vec<PCell<T>>,
        reader_pos: AtomicU64<_, RingState::reader_pos<T>, _>,
        writer_pos: AtomicU64<_, RingState::writer_pos<T>, _>,

        instance: Tracked<RingState::Instance<T>>,
    }

    pub closed spec fn wf(&self) -> bool {
        predicate {
            // The Cell IDs in the instance protocol match the cell IDs in the actual vector:
            &&& self.instance@.cell_ids().len() == self.buffer@.len()
            &&& forall|i: int| 0 <= i && i < self.buffer@.len() as int ==>
                self.instance@.cell_ids().index(i) ==
                    self.buffer@.index(i).id()
        }

        invariant on reader_pos with (instance) is (v: u64, g: RingState::reader_pos<T>) {
            &&& g.instance_id() == instance@.id()
            &&& g.value() == v as int
        }

        invariant on writer_pos with (instance) is (v: u64, g: RingState::writer_pos<T>) {
            &&& g.instance_id() == instance@.id()
            &&& g.value() == v as int
        }
    }
}
// ANCHOR_END: impl_queue_struct
// ANCHOR: impl_producer_struct


pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    writer_pos: usize,
    writer_state: Tracked<RingState::writer_state<T>>,
}

impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf() && self.writer_state@.instance_id() == (*self.queue).instance@.id()
            && self.writer_state@.value() == ProducerState::Idle(self.writer_pos as nat) && (
        self.writer_pos as int) < (*self.queue).buffer@.len()
    }
}

// ANCHOR_END: impl_producer_struct
// ANCHOR: impl_consumer_struct
pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    reader_pos: usize,
    reader_state: Tracked<RingState::reader_state<T>>,
}

impl<T> Consumer<T> {
    pub closed spec fn wf(&self) -> bool {
        (*self.queue).wf() && self.reader_state@.instance_id() == (*self.queue).instance@.id()
            && self.reader_state@.value() == ConsumerState::Idle(self.reader_pos as nat) && (
        self.reader_pos as int) < (*self.queue).buffer@.len()
    }
}

// ANCHOR_END: impl_consumer_struct
// ANCHOR: impl_new_queue
pub fn new_queue<T>(len: usize) -> (pc: (Producer<T>, Consumer<T>))
    requires
        len > 0,
    ensures
        pc.0.wf(),
        pc.1.wf(),
{
    // Initialize the vector to store the cells
    let mut backing_cells_vec = Vec::<PCell<T>>::new();
    // Initialize map for the permissions to the cells
    // (keyed by the indices into the vector)
    let tracked mut perms = Map::<nat, cell::PointsTo<T>>::tracked_empty();
    while backing_cells_vec.len() < len
        invariant
            forall|j: nat|
                #![trigger( perms.dom().contains(j) )]
                #![trigger( backing_cells_vec@.index(j as int) )]
                #![trigger( perms.index(j) )]
                0 <= j && j < backing_cells_vec.len() as int ==> perms.dom().contains(j)
                    && backing_cells_vec@.index(j as int).id() == perms.index(j).id()
                    && perms.index(j).is_uninit(),
    {
        let ghost i = backing_cells_vec.len();
        let (cell, cell_perm) = PCell::empty();
        backing_cells_vec.push(cell);
        proof {
            perms.tracked_insert(i as nat, cell_perm.get());
        }
        assert(perms.dom().contains(i as nat));
        assert(backing_cells_vec@.index(i as int).id() == perms.index(i as nat).id());
        assert(perms.index(i as nat).is_uninit());
    }
    // Vector for ids

    let ghost mut backing_cells_ids = Seq::<CellId>::new(
        backing_cells_vec@.len(),
        |i: int| backing_cells_vec@.index(i).id(),
    );
    // Initialize an instance of the FIFO queue
    let tracked (
        Tracked(instance),
        Tracked(head_token),
        Tracked(tail_token),
        Tracked(producer_token),
        Tracked(consumer_token),
    ) = RingState::Instance::initialize(backing_cells_ids, perms, perms);
    // Initialize atomics
    let tracked_inst: Tracked<RingState::Instance<T>> = Tracked(instance.clone());
    let head_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(head_token));
    let tail_atomic = AtomicU64::new(Ghost(tracked_inst), 0, Tracked(tail_token));
    // Initialize the queue
    let queue = Queue::<T> {
        instance: tracked_inst,
        reader_pos: head_atomic,
        writer_pos: tail_atomic,
        buffer: backing_cells_vec,
    };
    // Share the queue between the writer_state and reader_state
    let queue_arc = Arc::new(queue);
    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        writer_pos: 0,
        writer_state: Tracked(producer_token),
    };
    let cons = Consumer::<T> {
        queue: queue_arc,
        reader_pos: 0,
        reader_state: Tracked(consumer_token),
    };
    (prod, cons)
}

// ANCHOR_END: impl_new_queue
// ANCHOR: impl_producer
impl<T> Producer<T> {
    fn enqueue(&mut self, t: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        // Loop: if the queue is full, then block until it is not.
        loop
            invariant
                self.wf(),
        {
            let queue = &*self.queue;
            let len = queue.buffer.len();
            assert(0 <= self.writer_pos && self.writer_pos < len);
            // Calculate the index of the slot right after `writer_pos`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `writer_pos` to this value.
            let next_tail = if self.writer_pos + 1 == len {
                0
            } else {
                self.writer_pos + 1
            };
            let tracked cell_perm: Option<cell::PointsTo<T>>;
            // Get the current `reader_pos` value from the shared atomic.
            let reader_pos =
                atomic_with_ghost!(&queue.reader_pos => load();
                returning reader_pos;
                ghost head_token => {
                    // If `reader_pos != next_tail`, then we proceed with the operation.
                    // We check here, ghostily, in the `open_atomic_invariant` block if that's the case.
                    // If so, we proceed with the `produce_start` transition
                    // and obtain the cell permission.
                    cell_perm = if reader_pos != next_tail as u64 {
                        let tracked cp = queue.instance.borrow().produce_start(&head_token, self.writer_state.borrow_mut());
                        Option::Some(cp)
                    } else {
                        Option::None
                    };
                }
            );
            // Here's where we "actually" do the `reader_pos != next_tail` check:
            if reader_pos != next_tail as u64 {
                // Unwrap the cell_perm from the option.
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };
                // Write the element t into the buffer, updating the cell
                // from uninitialized to initialized (to the value t).
                queue.buffer[self.writer_pos].put(Tracked(&mut cell_perm), t);
                // Store the updated writer_pos to the shared `writer_pos` atomic,
                // while performing the `produce_end` transition.
                atomic_with_ghost!(&queue.writer_pos => store(next_tail as u64); ghost tail_token => {
                    queue.instance.borrow().produce_end(cell_perm,
                        cell_perm, &mut tail_token, self.writer_state.borrow_mut());
                });
                self.writer_pos = next_tail;
                return;
            }
        }
    }
}

// ANCHOR_END: impl_producer
// ANCHOR: impl_consumer
impl<T> Consumer<T> {
    fn dequeue(&mut self) -> (t: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let queue = &*self.queue;
            let len = queue.buffer.len();
            assert(0 <= self.reader_pos && self.reader_pos < len);
            let next_head = if self.reader_pos + 1 == len {
                0
            } else {
                self.reader_pos + 1
            };
            let tracked cell_perm: Option<cell::PointsTo<T>>;
            let writer_pos =
                atomic_with_ghost!(&queue.writer_pos => load();
                returning writer_pos;
                ghost tail_token => {
                    cell_perm = if self.reader_pos as u64 != writer_pos {
                        let tracked (_, Tracked(cp)) = queue.instance.borrow().consume_start(&tail_token, self.reader_state.borrow_mut());
                        Option::Some(cp)
                    } else {
                        Option::None
                    };
                }
            );
            if self.reader_pos as u64 != writer_pos {
                let tracked mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => {
                        assert(false);
                        proof_from_false()
                    },
                };
                let t = queue.buffer[self.reader_pos].take(Tracked(&mut cell_perm));
                atomic_with_ghost!(&queue.reader_pos => store(next_head as u64); ghost head_token => {
                    queue.instance.borrow().consume_end(cell_perm,
                        cell_perm, &mut head_token, self.reader_state.borrow_mut());
                });
                self.reader_pos = next_head;
                return t;
            }
        }
    }
}

fn main() {
    let (mut writer_state, mut reader_state) = new_queue(20);

    // Simple test:

    writer_state.enqueue(5);
    writer_state.enqueue(6);
    writer_state.enqueue(7);

    let x = reader_state.dequeue();
    print_u64(x);

    let x = reader_state.dequeue();
    print_u64(x);

    let x = reader_state.dequeue();
    print_u64(x);

    // Multi-threaded test:

    let writer_state = writer_state;
    let _join_handle = vstd::thread::spawn(
        move ||
            {
                let mut writer_state = writer_state;
                let mut i = 0;
                while i < 100
                    invariant
                        writer_state.wf(),
                {
                    writer_state.enqueue(i);
                    i = i + 1;
                }
            },
    );
    let mut i = 0;
    while i < 100
        invariant
            reader_state.wf(),
    {
        let x = reader_state.dequeue();
        print_u64(x);
        i = i + 1;
    }
}

} // verus!
// ANCHOR_END: impl_consumer
// ANCHOR_END: full
