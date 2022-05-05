#![allow(unused_imports)]

// port of single-producer single-consumer queue from LinearDafny
// https://github.com/vmware-labs/verified-betrfs/tree/concurrency-experiments/concurrency/spsc-queue

use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::vec::*;
use pervasive::option::*;
use pervasive::map::*;
use pervasive::ptr::*;
use pervasive::seq::*;
use pervasive::cell::*;
use pervasive::atomic::*;
use pervasive::modes::*;
use pervasive::invariant::*;
use std::sync::Arc;

use state_machines_macros::tokenized_state_machine;

#[is_variant]
pub enum ProducerState {
    Idle(nat),        // local copy of tail
    Producing(nat),
}

#[is_variant]
pub enum ConsumerState {
    Idle(nat),        // local copy of head
    Consuming(nat),
}

tokenized_state_machine!{FifoQueue<T> {
    fields {
        #[sharding(constant)]
        pub backing_cells: Seq<int>,

        #[sharding(storage_map)]
        pub storage: Map<nat, cell::Permission<T>>,

        #[sharding(variable)]
        pub head: nat,

        #[sharding(variable)]
        pub tail: nat,

        #[sharding(variable)]
        pub producer: ProducerState,

        #[sharding(variable)]
        pub consumer: ConsumerState,
    }

    #[spec]
    fn len(&self) -> nat {
        self.backing_cells.len()
    }

    #[spec] #[verifier(publish)]
    pub fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }

    #[invariant]
    pub fn not_overlapping(&self) -> bool {
        match (self.producer, self.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                head != tail
                && Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                true
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                head != tail
            }
        }
    }

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        0 <= self.head && self.head < self.len() &&
        0 <= self.tail && self.tail < self.len()
        && match self.producer {
            ProducerState::Producing(tail) => {
                self.tail == tail
            }
            ProducerState::Idle(tail) => {
                self.tail == tail
            }
        }
        && match self.consumer {
            ConsumerState::Consuming(head) => {
                self.head == head
            }
            ConsumerState::Idle(head) => {
                self.head == head
            }
        }
    }

    #[spec]
    fn is_active(&self, i: nat) -> bool {
        // Note that self.head = self.tail means empty range
        0 <= i && i < self.len() && (
            if self.head <= self.tail {
                self.head <= i && i < self.tail
            } else {
                i >= self.head || i < self.tail
            }
        )
    }

    #[spec]
    fn is_checked_out(&self, i: nat) -> bool {
        equal(self.producer, ProducerState::Producing(i))
        || equal(self.consumer, ConsumerState::Consuming(i))
    }

    #[invariant]
    pub fn has_items(&self) -> bool {
        forall(|i| 0 <= i && i < self.len() >>=
            self.has_item(i))
    }

    #[spec]
    fn has_item(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            !self.storage.dom().contains(i)
        } else {
            self.storage.dom().contains(i)
            && equal(
                self.storage.index(i).pcell,
                self.backing_cells.index(i)
            )
            &&
            if self.is_active(i) {
                self.storage.index(i).value.is_Some()
            } else {
                self.storage.index(i).value.is_None()
            }
        }
    }

    init!{
        initialize(backing_cells: Seq<int>, storage: Map<nat, cell::Permission<T>>) {
            require(
                forall(|i| 0 <= i && i < backing_cells.len() >>=
                    #[trigger] storage.dom().contains(i)
                    && equal(
                        storage.index(i).pcell,
                        backing_cells.index(i)
                    )
                    && storage.index(i).value.is_None(),
                )
            );
            require(backing_cells.len() > 0);

            init backing_cells = backing_cells;
            init storage = storage;
            init head = 0;
            init tail = 0;
            init producer = ProducerState::Idle(0);
            init consumer = ConsumerState::Idle(0);
        }
    }

    transition!{
        produce_start() {
            // Use the producer's _local_ copy of the tail
            // but use the _shared_ copy of the head.
            require(pre.producer.is_Idle());
            let tail = pre.producer.get_Idle_0();
            assert(0 <= tail && tail < pre.backing_cells.len());
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());
            require(next_tail != pre.head);

            update producer = ProducerState::Producing(tail);

            birds_eye let perm = pre.storage.index(tail);
            withdraw storage -= [tail => perm] by {
                assert(pre.has_item(tail));
            };

            assert(equal(perm.pcell, pre.backing_cells.index(tail))) by {
                assert(pre.has_item(tail));
            };
            assert(perm.value.is_None()) by {
                assert(!pre.is_active(tail));
                assert(pre.has_item(tail));
            };
        }
    }

    transition!{
        produce_end(perm: cell::Permission<T>) {
            require(pre.producer.is_Producing());
            let tail = pre.producer.get_Producing_0();

            assert(0 <= tail && tail < pre.backing_cells.len());
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            update producer = ProducerState::Idle(next_tail);
            update tail = next_tail;

            require(equal(perm.pcell, pre.backing_cells.index(tail))
              && perm.value.is_Some());
            deposit storage += [tail => perm] by { assert(pre.has_item(tail)); };
        }
    }

    transition!{
        consume_start() {
            require(pre.consumer.is_Idle());
            let head = pre.consumer.get_Idle_0();
            assert(0 <= head && head < pre.backing_cells.len());
            require(head != pre.tail);

            update consumer = ConsumerState::Consuming(head);

            birds_eye let perm = pre.storage.index(head);
            withdraw storage -= [head => perm] by {
                assert(pre.has_item(head));
            };

            assert(equal(perm.pcell, pre.backing_cells.index(head))) by {
                assert(pre.has_item(head));
            };
            assert(perm.value.is_Some()) by {
                assert(pre.is_active(head));
                assert(pre.has_item(head));
            };
        }
    }

    transition!{
        consume_end(perm: cell::Permission<T>) {
            require(pre.consumer.is_Consuming());
            let head = pre.consumer.get_Consuming_0();

            assert(0 <= head && head < pre.backing_cells.len());
            let next_head = Self::inc_wrap(head, pre.backing_cells.len());

            update consumer = ConsumerState::Idle(next_head);
            update head = next_head;

            require(equal(perm.pcell, pre.backing_cells.index(head))
              && perm.value.is_None());
            deposit storage += [head => perm] by { assert(pre.has_item(head)); };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, backing_cells: Seq<int>, storage: Map<nat, cell::Permission<T>>) {
        assert_forall_by(|i| {
            requires(0 <= i && i < post.len());
            ensures(post.has_item(i));

            assert(post.storage.dom().contains(i));
            /*
            assert(equal(
                post.storage.index(i).pcell,
                post.backing_cells.index(i)
            ));
            assert(if post.is_active(i) {
                post.storage.index(i).value.is_Some()
            } else {
                post.storage.index(i).value.is_None()
            });*/
        });
    }

    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        let tail = pre.producer.get_Idle_0();
        assert(!pre.is_active(tail));
        match (post.producer, post.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
            }
        }
        assert(forall(|i| pre.has_item(i) >>= post.has_item(i)));
    }

    #[inductive(produce_end)]
    fn produce_end_inductive(pre: Self, post: Self, perm: cell::Permission<T>) {
        assert_forall_by(|i| {
            requires(pre.has_item(i));
            ensures(post.has_item(i));

            /*if post.is_checked_out(i) {
                assert(!post.storage.dom().contains(i));
            } else {
                assert(post.storage.dom().contains(i));
                assert(equal(
                    post.storage.index(i).pcell,
                    post.backing_cells.index(i)
                ));
                assert(if post.is_active(i) {
                    post.storage.index(i).value.is_Some()
                } else {
                    post.storage.index(i).value.is_None()
                });
            }*/
        });
    }

    #[inductive(consume_start)]
    fn consume_start_inductive(pre: Self, post: Self) {
        assert_forall_by(|i| {
            requires(pre.has_item(i));
            ensures(post.has_item(i));
        });
    }
   
    #[inductive(consume_end)]
    fn consume_end_inductive(pre: Self, post: Self, perm: cell::Permission<T>) {
        let head = pre.consumer.get_Consuming_0();
        assert(post.storage.dom().contains(head));
        assert(equal(
                post.storage.index(head).pcell,
                post.backing_cells.index(head)
            ));
        assert(if post.is_active(head) {
                post.storage.index(head).value.is_Some()
            } else {
                post.storage.index(head).value.is_None()
            });

        match (pre.producer, pre.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
        };

        assert(pre.head != pre.tail);
        assert(!post.is_checked_out(head));
        assert(post.has_item(head));

        assert_forall_by(|i| {
            requires(pre.has_item(i));
            ensures(post.has_item(i));
        });
    }
}}

struct HeadTailTokens<T> {
    #[proof] head: FifoQueue::head<T>,
    #[proof] tail: FifoQueue::tail<T>,

    #[proof] head_perm: PermissionU64,
    #[proof] tail_perm: PermissionU64,
}

impl<T> HeadTailTokens<T> {
    #[spec]
    pub fn wf(&self, instance: FifoQueue::Instance<T>,
            head_id: int, tail_id: int) -> bool {
           equal(self.head.instance, instance)
        && equal(self.tail.instance, instance)
        && equal(self.head_perm.patomic, head_id)
        && equal(self.tail_perm.patomic, tail_id)
        && equal(self.head_perm.value as nat, self.head.value)
        && equal(self.tail_perm.value as nat, self.tail.value)
    }
}

struct Queue<T> {
    #[proof] instance: FifoQueue::Instance<T>,
    buffer: Vec<PCell<T>>,
    head: PAtomicU64,
    tail: PAtomicU64,
    #[proof] inv: Invariant<HeadTailTokens<T>>,
}

impl<T> Queue<T> {
    #[spec]
    pub fn wf(&self) -> bool {
        self.instance.backing_cells().len() == self.buffer.view().len()
        && forall(|i: int| 0 <= i && i < self.buffer.view().len() as int >>=
            self.instance.backing_cells().index(i) ==
                self.buffer.view().index(i).view())
        && forall(|v| self.inv.inv(v) == v.wf(self.instance, self.head.view(), self.tail.view()))
    }
}

pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    tail: usize,
    #[proof] producer: FifoQueue::producer<T>
}

impl<T> Producer<T> {
    #[spec]
    pub fn wf(&self) -> bool {
           (*self.queue).wf()
        && equal(self.producer.instance, (*self.queue).instance)
        && equal(self.producer.value, ProducerState::Idle(self.tail as nat))
        && ((self.tail as int) < (*self.queue).buffer.view().len())
    }
}

pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    head: usize,
    #[proof] consumer: FifoQueue::consumer<T>
}

impl<T> Consumer<T> {
    #[spec]
    pub fn wf(&self) -> bool {
           (*self.queue).wf()
        && equal(self.consumer.instance, (*self.queue).instance)
        && equal(self.consumer.value, ConsumerState::Idle(self.head as nat))
        && (self.head as int) < (*self.queue).buffer.view().len()
    }
}

pub fn new_queue<T>(len: usize) -> (Producer<T>, Consumer<T>) {
    requires(len > 0);
    ensures(|pc: (Producer<T>, Consumer<T>)| [
        pc.0.wf(),
        pc.1.wf(),
    ]);

    #[spec] let mut backing_cells_ids = Seq::<int>::empty();
    #[proof] let mut perms = Map::<nat, cell::Permission<T>>::proof_empty();
    let mut backing_cells_vec = Vec::<PCell<T>>::empty();

    while backing_cells_vec.len() < len {
        invariant(
            backing_cells_vec.len() == backing_cells_ids.len()
            &&
            forall(|j: int| 0 <= j && j < backing_cells_vec.len() as int >>=
                backing_cells_vec.index(j).view() == backing_cells_ids.index(j)
                &&
                perms.dom().contains(j as nat)
                &&
                backing_cells_vec.index(j as nat).view() == perms.index(j as nat).pcell
                &&
                perms.index(j as nat).value.is_None()
            )
        );

        #[spec] let i = backing_cells_vec.len();
        
        let (cell, Proof(cell_perm)) = PCell::empty();
        backing_cells_vec.push(cell);

        perms.proof_insert(i, cell_perm);
        backing_cells_ids = backing_cells_ids.push(cell_perm.pcell);
    }

    #[proof] let (instance, head_token, tail_token, producer_token, consumer_token)
        = FifoQueue::Instance::initialize(backing_cells_ids, perms, perms);

    let (head_atomic, Proof(head_perm)) = PAtomicU64::new(0);
    let (tail_atomic, Proof(tail_perm)) = PAtomicU64::new(0);

    #[proof] let inv = Invariant::new(
        HeadTailTokens {
            head: head_token,
            tail: tail_token,
            head_perm,
            tail_perm,
        },
        |v| v.wf(instance, head_atomic.view(), tail_atomic.view()),
        0,
    );

    let queue = Queue::<T> {
        instance,
        head: head_atomic,
        tail: tail_atomic,
        inv: inv,
        buffer: backing_cells_vec,
    };

    let queue_arc = Arc::new(queue);

    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        tail: 0,
        producer: producer_token,
    };

    let cons = Consumer::<T> {
        queue: queue_arc,
        head: 0,
        consumer: consumer_token,
    };

    (prod, cons)
}

impl<T> Producer<T> {
    fn enqueue(&mut self, t: T) {
        requires(old(self).wf());
        ensures(self.wf());

        loop {
            invariant(self.wf());

            let queue = &*self.queue;
            let len = queue.buffer.len();

            assert(0 <= self.tail && self.tail < len);

            let next_tail = if self.tail + 1 == len { 0 } else { self.tail + 1 };

            let head;
            #[proof] let cell_perm;
            open_invariant!(&queue.inv => htt => {
                head = queue.head.load(&htt.head_perm);

                cell_perm = if head != next_tail as u64 {
                    #[proof] let (_, cp) = queue.instance.produce_start(&htt.head, &mut self.producer);
                    Option::Some(cp)
                } else {
                    Option::None
                };
            });


            if head != next_tail as u64 {
                #[proof] let mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => { assert(false); proof_from_false() }
                };
                queue.buffer.index(self.tail).put(&mut cell_perm, t);

                open_invariant!(&queue.inv => htt => {
                    queue.tail.store(&mut htt.tail_perm, next_tail as u64);
                    queue.instance.produce_end(cell_perm,
                        cell_perm, &mut htt.tail, &mut self.producer);
                });

                self.tail = next_tail;
                
                return;
            }
        }
    }
}

impl<T> Consumer<T> {
    fn deque(&mut self) -> T {
        requires(old(self).wf());
        ensures(|t: T| self.wf());

        loop {
            invariant(self.wf());

            let queue = &*self.queue;
            let len = queue.buffer.len();

            assert(0 <= self.head && self.head < len);

            let next_head = if self.head + 1 == len { 0 } else { self.head + 1 };

            let tail;
            #[proof] let cell_perm;
            open_invariant!(&queue.inv => htt => {
                tail = queue.tail.load(&htt.tail_perm);

                cell_perm = if self.head as u64 != tail {
                    #[proof] let (_, cp) = queue.instance.consume_start(&htt.tail, &mut self.consumer);
                    Option::Some(cp)
                } else {
                    Option::None
                };
            });

            if self.head as u64 != tail {
                #[proof] let mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => { assert(false); proof_from_false() }
                };
                let t = queue.buffer.index(self.head).take(&mut cell_perm);

                open_invariant!(&queue.inv => htt => {
                    queue.head.store(&mut htt.head_perm, next_head as u64);
                    queue.instance.consume_end(cell_perm,
                        cell_perm, &mut htt.head, &mut self.consumer);
                });

                self.head = next_head;
                
                return t;
            }
        }
    }
}

fn main() { }
