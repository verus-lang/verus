// rust_verify/tests/example.rs ignore

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{*, pervasive::*};
use vstd::seq::*;
use vstd::set::*;
use vstd::map::*;

use state_machines_macros::*;

// for a finite set, returns a new int not in the 
#[verifier::spec]
pub fn get_new_nat(s: Set<nat>) -> nat {
    arbitrary() // TODO
}

#[verifier::proof]
pub fn get_new_nat_not_in(s: Set<nat>) {
    requires(s.finite());
    ensures(!s.contains(get_new_nat(s)));
    assume(false); // TODO
}

// These are all arbitrary for now:

pub struct ReadonlyOp {
    u: u8,
}

pub struct UpdateOp {
    u: u8,
}

pub struct ReturnType {
    u: u8,
}

pub struct NRState {
    u: u8,
}

#[verifier::spec]
#[verifier(opaque)]
pub fn read(state: NRState, op: ReadonlyOp) -> ReturnType {
    ReturnType { u: 0 }
}

#[verifier::spec]
#[verifier(opaque)]
pub fn update_state(state: NRState, op: UpdateOp) -> (NRState, ReturnType) {
    (state, ReturnType { u: 0 })
}

#[verifier::spec]
#[verifier(opaque)]
pub fn init_state() -> NRState {
    NRState { u: 0 }
}

////////// ReadonlyState: used to track the progress of a read-only query.
//
// A readonly query, which takes place on a given node `nodeId`,
// follows the following algorithm:
//
//  1. Read the global value 'version_upper_bound'.
//  2. Wait until node-local value 'local_head' is greater than the value
//     of 'version_upper_bound' that was read in step 1.
//  3. Execute the query against the node-local replica and return the result.
//
// (In real life, the thread does not just sit around 'waiting' in step 2;
// it might run a combiner phase in order to advance the local_head.)
//
// These 3 steps progress the status of the request through the cycle
//    Init -> VersionUpperBound -> ReadyToRead -> Done
//
// Note that the request itself does not "care" which nodeId it takes place on;
// we only track the nodeId to make sure that steps 2 and 3 use the same node.

pub enum ReadonlyState {
    Init{op: ReadonlyOp},
    VersionUpperBound{op: ReadonlyOp, version_upper_bound: nat},
    ReadyToRead{op: ReadonlyOp, node_id: nat, version_upper_bound: nat},
    Done{op: ReadonlyOp, ret: ReturnType, node_id: nat, version_upper_bound: nat},
}

////////// Updates and the combiner phase
//
// This part is a lot more complex; the lifecycle of an "update" is inherently
// tied to the lifecycle of the combiner, so I have to explain the entire combiner
// cycle for this to make sense.
//
// In particular, the combiner cycle starts with some (potentially empty) bulk collection
// of Update requests, which all start in UpdateState::Init.
// By the end of the combiner cycle (when it has gone back to 'Ready'), all the updates
// in that collection will be in UpdateState::Done.
//
// The combiner works as follows (keep in mind this is abstracted a bit from the
// real implementation).
//
//  1. Advance the 'global_tail' value by 1 for each update in the collection.
//     This creates a "LogEntry" for the given op at the given index.
//     It also updates the update from UpdateState::Init to UpdateState::Placed.
//
//      Note: This always appends to the log; there are never any "holes" in the log,
//      and the 'global_tail' always marks the end of the log. The log is unbounded
//      and not garbage-collected.
//      Keep in mind that the 'log' here is just an abstraction, and the "cyclic buffer"
//      that physically stores the log entries in real life has additional complexities.
//      We do not handle those complexities at this level of abstraction.
//
//      Note: Even when we have a bulk collection of updates, we still append the log
//      entries one at a time, once for each update. This means the log entries might
//      interleave with those of another thread.
//      This is more permissive than the real implementation, which advances the
//      'global_tail' with a single CAS operation, meaning that all the log entries
//      for the cycle will be contiguous in the log.
//      In the original Linear Dafny NR project, we modeled this step as a bulk update,
//      matching the implemenation. However, it turned out that:
//          (i) modeling 'bulk update' steps is kind of annoying
//          (ii) we never took advantage of the contiguity in the invariants
//      Since the single-step version is easier to model, and we don't lose anything for it,
//      that's what we do here.
//
//  2. Read the 'local_head' value for the given node.
//
//  3. Read the global 'global_tail' value.
//
//  4. Process all log entries in the range local_head..global_tail.
//     (This should include both the log entries we just creates, plus maybe some other
//     log entries from other nodes.)
//
//      NOTE: the global 'global_tail' value might change over the course of execution,
//      but we're going to stick with the local copy that we just read
//      (i.e., the value on the stack).
//
//     To process a log entry, we first apply the operation to the replica, and get
//     back a "return value". Next, we check if the log entry is for the given nodeId,
//     classifying it as "remote" or "local".
//      - If it's remote, we're done.
//      - If it's local, then we find the Update object in our bulk collection, and
//        update it from UpdateState::Placed to UpdateState::Applied, recording the
//        return value.
//
//  5. Update the global value of 'version_upper_bound'.
//     This step lets us move all the updates to UpdateState::Done.
//
//  6. Update the value of 'local_head'.
//
// Now, there are a bunch of things we need to prove so that the whole thing makes sense
// and so that the implementation can actually follow along and return data to the clients.
//
// Specifically, we have a sequence of "return ids" (recorded in the 'queued_ops' field)
// that need to get processed. When the implementation handles a "local" operation off the
// log, it appends the return value into a buffer; when it's done, it expects the buffer
// of return values to line up with all the update requests that it started with.
//
// What this means is that we need to show:
//   - When we process a "local" operation, its RequestId corresponds to the next
//     RequestId recorded in the queued_ops (i.e., the one at 'queue_index'.)
//   - When we have finished the entire loop, we have finished processing all
//     the RequestIds we expected (i.e., `queue_index == queued_ops.len()`).
//
// This means we need to establish an invariant between the combiner state and the
// log state at all times. Specifically, we need an invariant that relates the combiner
// state to the log entries whose node_ids match the combiner's node, describing where
// they are and in what order.
//
// The invariant roughly says that during step (4), (the "Loop" state):
//   The RequestIds in `queued_ops`, sliced from queue_index .. queued_ops.len()
//   match
//   The RequestIds in the log that are local, sliced from
//          local_head .. global_tail
// (Note that queue_index and local_head are the cursors that advance throughout the loop,
// while global_tail is the one recorded in step 3, so it's fixed.)
// Furthermore:
//   There are no local operations in the log between
//   the recorded global_tail and the global global_tail.
// See the invariant `wf_combiner_for_node_id`, as well as the predicates
// `LogRangeMatchesQueue` and `LogRangeNoNodeId`.
//
// Example: suppose N is the local node_id, and [a, b, c, d] are the request ids.
// We might be in a state that looks like this: (Here, '...' indicates remote entries,
// and '(N, x)' means a log entry with node id N that corresponds to request id x.)
//
//       CombinerState                                           CombinerState   global
//       local_head                                              global_tail     global_tail
//          |                                                              |               |
//       ===================================================================================
//          |          |       |       |        |       |          |       |       |       |
//  Log:    |  (N, b)  |  ...  |  ...  | (N, c) |  ...  |  (N, d)  |  ...  |  ...  |  ...  |
//          |          |       |       |        |       |          |       |       |       |
//       ===================================================================================
//
//  ---- Combiner state (in `CombinerState::Loop` phase).
//
//      queued_ops =  [  a,   b,   c,   d   ]
//                          ^
//                          |
//                  queue_index = 1
//
// ---- Update state:
//
//    a => UpdateState::Applied { ... }
//    b => UpdateState::Placed { ... }
//    c => UpdateState::Placed { ... }
//    d => UpdateState::Placed { ... }
//
// In the example, `LogRangeMatchesQueue` is the relation that shows that (b, c, d)
// agree between the queued_ops and the log; whereas `LogRangeNoNodeId` shows that there
// are no more local entries between the Combiner global_tail and the global global_tail.
//
// And again, in the real implementation, b, c, d will actually be contiguous in the log,
// but the state shown above is permitted by the model here.
// If we _were_ going to make use of contiguity, then the place to do it would probably
// be the definition of `LogRangeMatchesQueue`, but as I explained earlier, I didn't
// find it helpful.
//
// Another technical note: the LogEntry doesn't actually store the RequestId on it;
// `LogRangeMatchesQueue` has to connect the request id to the UpdateState, which then
// has a pointer into the log via `idx`. (It's possible that this could be simplified.)

#[is_variant]
pub enum UpdateState {
    Init{op: UpdateOp},
    Placed{op: UpdateOp, idx: nat},
    Applied{ret: ReturnType, idx: nat},
    Done{ret: ReturnType, idx: nat},
}

#[is_variant]
pub enum CombinerState {
    Ready,
    Placed{queued_ops: Seq<nat>},
    LoadedHead{queued_ops: Seq<nat>, lhead: nat},
    Loop{queued_ops: Seq<nat>, lhead: nat, queue_index: nat, global_tail: nat},
    UpdatedVersion{queued_ops: Seq<nat>, global_tail: nat},
}

pub struct LogEntry {
    pub op: UpdateOp,
    pub node_id: nat,
}

tokenized_state_machine!{
    UnboundedLog {
        fields {
            #[sharding(constant)]
            pub num_nodes: nat,

            #[sharding(map)]
            pub log: Map<nat, LogEntry>,

            #[sharding(variable)]
            pub global_tail: nat,

            #[sharding(map)]
            pub replicas: Map<nat, NRState>,

            #[sharding(map)]
            pub local_heads: Map<nat, nat>, // previously called "local tails"

            #[sharding(variable)]
            pub version_upper_bound: nat, // previously called "ctail"

            #[sharding(map)]
            pub local_reads: Map<nat, ReadonlyState>,

            #[sharding(map)]
            pub local_updates: Map<nat, UpdateState>,

            #[sharding(map)]
            pub combiner: Map<nat, CombinerState>
        }

        //// Lifecycle of a Readonly operation

        transition!{
            readonly_new(op: ReadonlyOp) {
                birds_eye let rid = get_new_nat(pre.local_reads.dom());
                add local_reads += [ rid => ReadonlyState::Init {op} ] by {
                    get_new_nat_not_in(pre.local_reads.dom());
                };
            }
        }

        transition!{
            readonly_read_ctail(rid: nat) {
                remove local_reads -= [ rid => let ReadonlyState::Init {op} ];
                add local_reads += [ rid => ReadonlyState::VersionUpperBound {op, version_upper_bound: pre.version_upper_bound} ];
            }
        }

        transition!{
            readonly_ready_to_read(rid: nat, node_id: nat) {
                have local_heads >= [ node_id => let local_head ];
                remove local_reads -= [ rid => let ReadonlyState::VersionUpperBound {op, version_upper_bound} ];

                require(local_head >= version_upper_bound);

                add local_reads += [ rid => ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} ];
            }
        }

        transition!{
            readonly_apply(rid: nat) {
                remove local_reads -= [ rid => let ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} ];
                have combiner >= [ node_id => CombinerState::Ready ];
                have replicas >= [ node_id => let state ];

                let ret = read(state, op);

                add local_reads += [ rid => ReadonlyState::Done{op, node_id, version_upper_bound, ret} ];
            }
        }

        transition!{
            readonly_finish(rid: nat, op: ReadonlyOp, version_upper_bound: nat, node_id: nat, ret: ReturnType) {
                remove local_reads -= [ rid => ReadonlyState::Done{op, node_id, version_upper_bound, ret} ];
            }
        }

        //// Updates, init and finish

        /*transition!{
            update_new(op: UpdateOp) {
                birds_eye let rid = get_new_nat(
                    pre.local_reads.dom().union(
                    ));
                add local_reads += [ rid => ReadonlyState::Init {op} ] by {
                    get_new_nat_not_in(pre.local_reads.dom());
                };
            }
        }*/

        //// Lifecycle of the combiner and updates

        /*
        transition!{
            advance_tail(
                node_id: nat,
                request_ids: Seq<nat>,
                old_updates: Map<nat, UpdateState>,
            ) {
                require(Seq::unique(request_ids));

                let old_updates = Map::<nat, UpdateState>::new(
                    |rid| request_ids.contains(rid),

                require(forall(|rid|
                    old_updates.dom().contains(rid) >>= 
                        old_updates.index(rid).is_Init() && request_ids.contains(rid)));
                require(forall(|i|
                    0 <= i && i < request_ids.len() >>=
                        old_updates.dom().contains(request_ids.index(i))));

                remove updates -= (old_updates);
                remove combiner -= [node_id => Combiner::Ready];

                let new_log = Map::<nat, LogEntry>::new(
                    |n| pre.global_tail <= n && n < pre.global_tail + request_ids.len(),
                    |n| LogEntry{
                        op: old_updates.index(request_ids.index(n)).get_Init_op(),
                        node_id: node_id,
                    },
                );
                let new_updates = Map::<nat, UpdateState>::new(
                    |rid| old_updates.dom().contains(rid),
                    |rid| UpdateState::Placed{
                        op: old_updates.index(rid).get_Init_op(),
                        idx: idx_of(request_ids, rid),
                    }
                );

                add log += (new_log);
                add local_updates += (new_updates);
                add combiner += [node_id => Combiner::Placed{queued_ops: request_ids}];
                update global_tail = pre.global_tail + request_ids.len();
            }
        }
        */

        transition!{
            exec_trivial_start(node_id: nat) {
                remove combiner -= [node_id => CombinerState::Ready];
                add combiner += [node_id => CombinerState::Placed{queued_ops: Seq::empty()}];
            }
        }

        transition!{
            advance_tail_one(
                node_id: nat,
                rid: nat,
            ) {
                // Only allowing a single request at a time
                // (in contrast to the seagull one which does it in bulk).
                // Hopefully this leads to some easier proofs.

                remove combiner -= [node_id => let CombinerState::Placed{queued_ops}];
                add combiner += [node_id => CombinerState::Placed{
                    queued_ops: queued_ops.push(rid)
                }];

                remove local_updates -= [rid => let UpdateState::Init{op}];
                add local_updates += [rid => UpdateState::Placed{ op, idx: pre.global_tail }];

                update global_tail = pre.global_tail + 1;

                add log += [pre.global_tail => LogEntry{ op, node_id }];
            }
        }

        transition!{
            exec_load_tail(node_id: nat) {
                remove combiner -= [node_id => let CombinerState::Placed{queued_ops}];
                have local_heads >= [node_id => let lhead];
                add combiner += [node_id => CombinerState::LoadedHead{queued_ops, lhead}];
            }
        }

        transition!{
            exec_load_local_head(node_id: nat) {
                remove combiner -= [node_id => let CombinerState::Placed{queued_ops}];
                have local_heads >= [node_id => let lhead];
                add combiner += [node_id => CombinerState::LoadedHead{queued_ops, lhead}];
            }
        }

        transition!{
            exec_load_global_head(node_id: nat) {
                remove combiner -= [node_id => let CombinerState::LoadedHead{queued_ops, lhead}];
                add combiner += [node_id => CombinerState::Loop{
                    queued_ops,
                    lhead,
                    global_tail: pre.global_tail,
                    queue_index: 0
                }];
            }
        }

        property!{
            pre_exec_dispatch_local(
                  node_id: nat,
            ) {
                have combiner >= [node_id => let CombinerState::Loop{
                    queued_ops,
                    lhead,
                    global_tail,
                    queue_index,
                }];
                have log >= [lhead => let log_entry];

                require(log_entry.node_id == node_id);
                require(lhead < global_tail);
                assert(queue_index < queued_ops.len()) by {
                    //assert(pre.wf_combiner_for_node_id(node_id));
                    //assert(lhead < global_tail);
                    //assert(pre.log.index(lhead).node_id == node_id);
                };
            }
        }

        transition!{
            exec_dispatch_local(
                  node_id: nat,
            ) {
                remove combiner -= [node_id => let CombinerState::Loop{
                    queued_ops,
                    lhead,
                    global_tail,
                    queue_index,
                }];

                require(lhead < global_tail);
                require(queue_index < queued_ops.len());

                have log >= [lhead => let log_entry];
                remove replicas -= [node_id => let old_nr_state];
                let rid = queued_ops.index(queue_index);
                remove local_updates -= [rid => let u];

                require(log_entry.node_id == node_id);

                //assert(u == UpdateState::Placed{node_id, idx: lhead};
                let (new_nr_state, ret) = update_state(old_nr_state, log_entry.op);

                add combiner += [node_id => CombinerState::Loop{
                    queued_ops,
                    lhead: lhead + 1,
                    global_tail,
                    queue_index: queue_index + 1,
                }];
                add replicas += [node_id => new_nr_state];
                add local_updates += [rid => UpdateState::Applied{ret, idx: lhead}];
            }
        }

        transition!{
            exec_dispatch_remote(
                  node_id: nat,
            ) {
                remove combiner -= [node_id => let CombinerState::Loop{
                    queued_ops,
                    lhead,
                    global_tail,
                    queue_index,
                }];
                have log >= [lhead => let log_entry];
                remove replicas -= [node_id => let old_nr_state];
                let rid = queued_ops.index(queue_index);

                require(lhead < global_tail);
                require(log_entry.node_id != node_id);

                assert(lhead < global_tail);
                //assert(u == UpdateState::Placed{node_id, idx: lhead};
                let (new_nr_state, ret) = update_state(old_nr_state, log_entry.op);

                add combiner += [node_id => CombinerState::Loop{
                    queued_ops,
                    lhead: lhead + 1,
                    global_tail,
                    queue_index,
                }];
                add replicas += [node_id => new_nr_state];
            }
        }

        transition!{
            exec_update_version_upper_bound(
                  node_id: nat,
            ) {
                remove combiner -= [node_id => let CombinerState::Loop{
                    queued_ops,
                    lhead,
                    global_tail,
                    queue_index,
                }];
                require(lhead == global_tail);

                assert(queue_index == queued_ops.len()) by {
                    //assert(pre.wf_combiner_for_node_id(node_id));
                };


                add combiner += [node_id => CombinerState::UpdatedVersion{
                    queued_ops, global_tail
                }];
                update version_upper_bound = if pre.version_upper_bound >= global_tail {
                    pre.version_upper_bound
                } else {
                    global_tail
                };
            }
        }

        transition!{
            exec_goto_ready(
                  node_id: nat,
            ) {
                remove combiner -= [node_id => let CombinerState::UpdatedVersion{
                    queued_ops, global_tail
                }];
                remove local_heads -= [node_id => let old_local_head];

                add combiner += [node_id => CombinerState::Ready];
                add local_heads += [node_id => global_tail];
            }
        }

        ////// Invariants

        #[invariant]
        pub fn rids_finite(&self) -> bool {
            &&& self.local_reads.dom().finite()
            &&& self.local_updates.dom().finite()
        }

        #[invariant]
        pub fn combiner_local_heads_domains(&self) -> bool {
            forall |k| self.local_heads.dom().contains(k) <==>
                self.combiner.dom().contains(k)
        }

        #[invariant]
        pub fn combiner_replicas_domains(&self) -> bool {
            forall |k| self.replicas.dom().contains(k) <==>
                self.combiner.dom().contains(k)
        }



        #[invariant]
        pub fn version_in_range(&self) -> bool {
            self.global_tail >= self.version_upper_bound
        }

        #[invariant]
        pub fn version_upper_bound_heads(&self) -> bool {
            forall |node_id| #[trigger] self.local_heads.dom().contains(node_id) ==>
                self.local_heads.index(node_id) <= self.version_upper_bound
        }

        #[invariant]
        pub fn log_entries_up_to_global_tail(&self) -> bool {
            forall |idx: nat| (idx < self.global_tail) == self.log.dom().contains(idx)
        }

        #[invariant]
        pub fn read_requests_wf(&self) -> bool {
            forall |rid| #[trigger] self.local_reads.dom().contains(rid) ==>
                self.wf_read(self.local_reads.index(rid))
        }

        #[verifier::spec]
        pub fn wf_read(&self, rs: ReadonlyState) -> bool {
            match rs {
                ReadonlyState::Init{op} => {
                    true
                }
                ReadonlyState::VersionUpperBound{op, version_upper_bound} => {
                    version_upper_bound <= self.version_upper_bound
                }
                ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                    &&& self.combiner.dom().contains(node_id)
                    &&& self.local_heads.dom().contains(node_id)
                    &&& self.replicas.dom().contains(node_id)
                    &&& version_upper_bound <= self.version_upper_bound
                    &&& version_upper_bound <= self.exec_local_head(node_id)
                }
                ReadonlyState::Done{op, ret, node_id, version_upper_bound} => {
                    &&& self.combiner.dom().contains(node_id)
                    &&& self.local_heads.dom().contains(node_id)
                    &&& self.replicas.dom().contains(node_id)
                    &&& version_upper_bound <= self.version_upper_bound
                    &&& version_upper_bound <= self.exec_local_head(node_id)
                }
            }
        }

        #[verifier::spec]
        fn exec_local_head(&self, node_id: nat) -> nat {
            match self.combiner.index(node_id) {
                CombinerState::Ready => {
                    self.local_heads.index(node_id)
                }
                CombinerState::Placed{queued_ops} => {
                    self.local_heads.index(node_id)
                }
                CombinerState::LoadedHead{queued_ops, lhead} => {
                    lhead
                }
                CombinerState::Loop{queued_ops, lhead, queue_index, global_tail} => {
                    lhead
                }
                CombinerState::UpdatedVersion{queued_ops, global_tail} => {
                    global_tail
                }
            }
        }

        #[invariant]
        pub fn combiner_states_wf(&self) -> bool {
            forall |node_id| #[trigger] self.combiner.dom().contains(node_id) ==>
                self.wf_combiner_for_node_id(node_id)
        }

        #[verifier::spec]
        pub fn wf_combiner_for_node_id(&self, node_id: nat) -> bool {
          match self.combiner.index(node_id) {
            CombinerState::Ready => {
              &&& self.local_heads.dom().contains(node_id)
              &&& self.local_heads.index(node_id) <= self.global_tail
              &&& LogRangeNoNodeId(self.log, self.local_heads.index(node_id), self.global_tail, node_id)
            }
            CombinerState::Placed{queued_ops} => {
              &&& self.local_heads.dom().contains(node_id)
              &&& self.local_heads.index(node_id) <= self.global_tail
              &&& LogRangeMatchesQueue(queued_ops, self.log, 0, self.local_heads.index(node_id), self.global_tail, node_id, self.local_updates)
              &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
              &&& seq_unique(queued_ops)
            }
            CombinerState::LoadedHead{queued_ops, lhead} => {
              // we've just read the local tail value, and no-one else should modify that
              &&& lhead == self.local_heads.index(node_id)
              // the local tail should be smaller or equal than the ctail
              &&& lhead <= self.version_upper_bound
              &&& lhead <= self.global_tail
              &&& LogRangeMatchesQueue(queued_ops, self.log, 0, lhead, self.global_tail, node_id, self.local_updates)
              &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, 0)
              &&& seq_unique(queued_ops)
            }
            CombinerState::Loop{queued_ops, queue_index, lhead, global_tail} => {
              // the global tail may have already advanced...
              &&& global_tail <= self.global_tail
              // we're advancing the local tail here
              &&& lhead >= self.local_heads.index(node_id)
              // the local tail should always be smaller or equal to the global tail
              &&& lhead <= global_tail
              // the log now contains all entries up to localtail
              &&& LogContainsEntriesUpToHere(self.log, lhead)
              &&& 0 <= queue_index <= queued_ops.len()
              &&& LogRangeMatchesQueue(queued_ops, self.log, queue_index, lhead, global_tail, node_id, self.local_updates)
              &&& LogRangeNoNodeId(self.log, global_tail, self.global_tail, node_id)
              &&& QueueRidsUpdatePlaced(queued_ops, self.local_updates, queue_index)
              &&& QueueRidsUpdateDone(queued_ops, self.local_updates, queue_index)
              &&& seq_unique(queued_ops)
            }
            CombinerState::UpdatedVersion{queued_ops, global_tail} => {
              // the global tail may have already advanced...
              &&& global_tail <= self.global_tail
              // update the ctail value
              &&& global_tail <= self.version_upper_bound
              // the local tail should be smaller than this one here
              &&& self.local_heads.index(node_id) <= global_tail
              // the log now contains all entries up to global_tail
              &&& LogContainsEntriesUpToHere(self.log, global_tail)
              &&& LogRangeNoNodeId(self.log, global_tail, self.global_tail, node_id)
              &&& QueueRidsUpdateDone(queued_ops, self.local_updates, queued_ops.len())
              &&& seq_unique(queued_ops)
            }
          }
        }

        #[invariant]
        pub fn inv_combiner_rids_distinct(&self) -> bool
        {
          forall |node_id1, node_id2|
              (#[trigger] self.combiner.dom().contains(node_id1)
              && #[trigger] self.combiner.dom().contains(node_id2)
              && node_id1 != node_id2) ==>
                CombinerRidsDistinctTwoNodes(self.combiner.index(node_id1), self.combiner.index(node_id2))
        }

        ////// Inductiveness proof

        #[inductive(readonly_new)]
        fn readonly_new_inductive(pre: Self, post: Self, op: ReadonlyOp) { }
       
        #[inductive(readonly_read_ctail)]
        fn readonly_read_ctail_inductive(pre: Self, post: Self, rid: nat) { }
       
        #[inductive(readonly_ready_to_read)]
        fn readonly_ready_to_read_inductive(pre: Self, post: Self, rid: nat, node_id: nat) {
            match post.local_reads.index(rid) {
                ReadonlyState::ReadyToRead{op, node_id, version_upper_bound} => {
                    assert(post.combiner.dom().contains(node_id));
                    assert(post.local_heads.dom().contains(node_id));
                    assert(post.replicas.dom().contains(node_id));
                    assert(version_upper_bound <= post.version_upper_bound);
                    assert(version_upper_bound <= post.exec_local_head(node_id));
                }
                _ => { }
            };
            assert(post.wf_read(post.local_reads.index(rid)));
        }
       
        #[inductive(readonly_apply)]
        fn readonly_apply_inductive(pre: Self, post: Self, rid: nat) { }
       
        #[inductive(readonly_finish)]
        fn readonly_finish_inductive(pre: Self, post: Self, rid: nat, op: ReadonlyOp, version_upper_bound: nat, node_id: nat, ret: ReturnType) { }
       
        #[inductive(exec_trivial_start)]
        fn exec_trivial_start_inductive(pre: Self, post: Self, node_id: nat) {
            concat_LogRangeNoNodeId_LogRangeMatchesQueue(
                Seq::empty(), post.log, 0,
                pre.local_heads.index(node_id),
                pre.global_tail,
                post.global_tail,
                node_id,
                post.local_updates);

            /*match post.combiner.index(node_id) {
              CombinerState::Placed{queued_ops} => {
                assert(post.local_heads.dom().contains(node_id));
                assert(post.local_heads.index(node_id) <= post.global_tail);
                assert(LogRangeMatchesQueue(queued_ops, post.log, 0, post.local_heads.index(node_id), post.global_tail, node_id, post.local_updates));
                assert(QueueRidsUpdatePlaced(queued_ops, post.local_updates, 0));
                assert(seq_unique(queued_ops));
              }
              _ => { }
            }*/
            assert(post.wf_combiner_for_node_id(node_id));
        }

        #[inductive(advance_tail_one)]
        fn advance_tail_one_inductive(pre: Self, post: Self, node_id: nat, rid: nat) {
            let old_queued_ops = pre.combiner.index(node_id).get_Placed_queued_ops();

            let op = pre.local_updates.index(rid).get_Init_op();
            assert(post.wf_combiner_for_node_id(node_id)) by {
              //LogRangeMatchesQueue_for_AdvanceTail(m, m', nodeId, request_ids, 0);
              /*assert(LogRangeMatchesQueue(request_ids,
                  post.log, 0, pre.global_tail.value, post.global_tail.value, nodeId, post.localUpdates));
              LogRangeNoNodeId_preserved_AdvanceTail(m, m', nodeId, request_ids,
                  m.localTails[nodeId], m.global_tail.value, nodeId);
              concat_LogRangeNoNodeId_LogRangeMatchesQueue(
                  request_ids, m'.log, 0,
                  m.localTails[nodeId],
                  m.global_tail.value, m'.global_tail.value, nodeId, m'.localUpdates);*/

                match post.combiner.index(node_id) {
                  CombinerState::Placed{queued_ops} => {
                    assert(post.local_heads.dom().contains(node_id));
                    assert(post.local_heads.index(node_id) <= post.global_tail);

                    append_LogRangeMatchesQueue(old_queued_ops, pre.log, post.log,
                        0,
                        post.local_heads.index(node_id),
                        pre.global_tail,
                        node_id,
                        pre.local_updates,
                        post.local_updates,
                        rid,
                        LogEntry{ op, node_id });

                    assert(LogRangeMatchesQueue(queued_ops, post.log, 0, post.local_heads.index(node_id), post.global_tail, node_id, post.local_updates));
                    assert(QueueRidsUpdatePlaced(queued_ops, post.local_updates, 0));
                    assert(seq_unique(queued_ops));
                  }
                  _ => { }
                }

            }

            assert forall |node_id1| #[trigger] post.combiner.dom().contains(node_id1)
                && node_id1 != node_id
                implies post.wf_combiner_for_node_id(node_id1)
            by {
                assert(pre.combiner.index(node_id1) === post.combiner.index(node_id1));
                assert(pre.wf_combiner_for_node_id(node_id1));
                match pre.combiner.index(node_id1) {
                    CombinerState::Ready => {
                        append_LogRangeNoNodeId_other(pre.log, post.log,
                            post.local_heads.index(node_id1), pre.global_tail, node_id1, LogEntry{ op, node_id });
                    }
                    CombinerState::Placed{queued_ops} => {
                        append_LogRangeMatchesQueue_other_augment(queued_ops, pre.log, post.log,
                            0, post.local_heads.index(node_id1), pre.global_tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                    }
                    CombinerState::LoadedHead{queued_ops, lhead} => {
                        append_LogRangeMatchesQueue_other_augment(queued_ops, pre.log, post.log,
                            0, lhead, pre.global_tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                    }
                    CombinerState::Loop{queued_ops, lhead, queue_index, global_tail} => {
                        append_LogRangeMatchesQueue_other(queued_ops, pre.log, post.log,
                            queue_index, lhead, global_tail, pre.global_tail, node_id1, pre.local_updates, post.local_updates, rid, LogEntry{ op, node_id });
                        append_LogRangeNoNodeId_other(pre.log, post.log,
                            global_tail, pre.global_tail,
                            node_id1, LogEntry{ op, node_id });
                    }
                    CombinerState::UpdatedVersion{queued_ops, global_tail} => {
                        append_LogRangeNoNodeId_other(pre.log, post.log,
                            global_tail, pre.global_tail, node_id1, LogEntry{ op, node_id });
                    }
                }
            }

            assert forall |node_id1|
              (#[trigger] post.combiner.dom().contains(node_id1)
              && node_id1 != node_id) implies
                CombinerRidsDistinctTwoNodes(post.combiner.index(node_id1), post.combiner.index(node_id))
            by {
                assert(pre.wf_combiner_for_node_id(node_id1));

                /*let c1 = post.combiner.index(node_id1);
                let c2 = post.combiner.index(node_id);

                if !c1.is_Ready() && !c2.is_Ready() {
                    let queued_ops1 = match c1 {
                      CombinerState::Ready => arbitrary(),
                      CombinerState::Placed{queued_ops} => queued_ops,
                      CombinerState::LoadedHead{queued_ops, ..} => queued_ops,
                      CombinerState::Loop{queued_ops, ..} => queued_ops,
                      CombinerState::UpdatedVersion{queued_ops, ..} => queued_ops,
                    };

                    /*let queued_ops2 = match c2 {
                      CombinerState::Ready => arbitrary(),
                      CombinerState::Placed{queued_ops} => queued_ops,
                      CombinerState::LoadedHead{queued_ops, ..} => queued_ops,
                      CombinerState::Loop{queued_ops, ..} => queued_ops,
                      CombinerState::UpdatedVersion{queued_ops, ..} => queued_ops,
                    };*/

                    assert forall |j| 0 <= j < queued_ops1.len()
                        && queued_ops1.index(j) == rid implies false
                    by {
                      // should follow from QueueRidsUpdatePlaced, QueueRidsUpdateDone
                      assert(pre.local_updates.index(queued_ops1.index(j)).is_Placed()
                          || pre.local_updates.index(queued_ops1.index(j)).is_Applied()
                          || pre.local_updates.index(queued_ops1.index(j)).is_Done());
                    }

                    assert(!queued_ops1.contains(rid));

                    /*assert forall |i, j| 0 <= i < queued_ops1.len() && 0 <= j < queued_ops2.len()
                        implies #[trigger] queued_ops1.index(i) !== #[trigger] queued_ops2.index(j)
                    by {
                    }*/

                    //assert(seqs_disjoint(queued_ops1, queued_ops2));
                }*/

                //assert(CombinerRidsDistinctTwoNodes(c1, c2));

                //assert(CombinerRidsDistinctTwoNodes(pre.combiner.index(node_id1), pre.combiner.index(node_id)));
                //assert(CombinerRidsDistinctTwoNodes(post.combiner.index(node_id1), pre.combiner.index(node_id)));
                assert(CombinerRidsDistinctTwoNodes(post.combiner.index(node_id1), post.combiner.index(node_id)));
            }

        }

        #[inductive(exec_load_tail)]
        fn exec_load_tail_inductive(pre: Self, post: Self, node_id: nat) { }
       
        #[inductive(exec_load_local_head)]
        fn exec_load_local_head_inductive(pre: Self, post: Self, node_id: nat) { }
       
        #[inductive(exec_load_global_head)]
        fn exec_load_global_head_inductive(pre: Self, post: Self, node_id: nat) {

            /*match post.combiner.index(node_id) {
              CombinerState::Loop{queued_ops, queue_index, lhead, global_tail} => {
                // the global tail may have already advanced...
                assert(global_tail <= post.global_tail);
                // we're advancing the local tail here
                assert(lhead >= post.local_heads.index(node_id));
                // the local tail should always be smaller or equal to the global tail
                assert(lhead <= global_tail);
                // the log now contains all entries up to localtail
                assert(LogContainsEntriesUpToHere(post.log, lhead));
                assert(0 <= queue_index <= queued_ops.len());
                assert(LogRangeMatchesQueue(queued_ops, post.log, queue_index, lhead, global_tail, node_id, post.local_updates));
                assert(LogRangeNoNodeId(post.log, global_tail, post.global_tail, node_id));
                assert(QueueRidsUpdatePlaced(queued_ops, post.local_updates, queue_index));
                assert(QueueRidsUpdateDone(queued_ops, post.local_updates, queue_index));
                assert(seq_unique(queued_ops));
              }
              _ => { }
            }*/

            assert(post.wf_combiner_for_node_id(node_id));
        }
       
        #[inductive(exec_dispatch_local)]
        fn exec_dispatch_local_inductive(pre: Self, post: Self, node_id: nat) {
            assert(post.wf_combiner_for_node_id(node_id)) by {
              LogRangeMatchesQueue_update_change(
                  post.combiner.index(node_id).get_Loop_queued_ops(),
                  post.log, post.combiner.index(node_id).get_Loop_queue_index(), post.combiner.index(node_id).get_Loop_lhead(),
                  pre.combiner.index(node_id).get_Loop_global_tail(), node_id, pre.local_updates, post.local_updates);
            }
            let c = pre.combiner.index(node_id);
            let rid = c.get_Loop_queued_ops().index(c.get_Loop_queue_index());
            assert forall |node_id0| #[trigger] post.combiner.dom().contains(node_id0) && node_id0 != node_id
                implies post.wf_combiner_for_node_id(node_id0)
            by {
              match pre.combiner.index(node_id0) {
                CombinerState::Ready => {
                }
                CombinerState::Placed{queued_ops} => {
                  assert(!queued_ops.contains(rid));
                  LogRangeMatchesQueue_update_change_2(
                    queued_ops, post.log, 0, post.local_heads.index(node_id0), post.global_tail, node_id0, pre.local_updates, post.local_updates);
                }
                CombinerState::LoadedHead{queued_ops, lhead} => {
                  assert(!queued_ops.contains(rid));
                  LogRangeMatchesQueue_update_change_2(
                    queued_ops, post.log, 0, lhead, post.global_tail, node_id0, pre.local_updates, post.local_updates);
                }
                CombinerState::Loop{queued_ops, queue_index, lhead, global_tail} => {
                  assert(!queued_ops.contains(rid));
                  LogRangeMatchesQueue_update_change_2(
                    queued_ops, post.log, queue_index, lhead, global_tail, node_id0, pre.local_updates, post.local_updates);
                }
                CombinerState::UpdatedVersion{queued_ops, global_tail} => {
                }
              }
            }
        }
       
        #[inductive(exec_dispatch_remote)]
        fn exec_dispatch_remote_inductive(pre: Self, post: Self, node_id: nat) { }
       
        #[inductive(exec_update_version_upper_bound)]
        fn exec_update_version_upper_bound_inductive(pre: Self, post: Self, node_id: nat) { }
       
        #[inductive(exec_goto_ready)]
        fn exec_goto_ready_inductive(pre: Self, post: Self, node_id: nat) { }


    }
}

verus!{

#[verifier::spec]
fn LogRangeMatchesQueue(queue: Seq<nat>, log: Map<nat, LogEntry>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat, updates: Map<nat, UpdateState>) -> bool
  {
    recommends(0 <= queueIndex <= queue.len());
    decreases_when(logIndexLower <= logIndexUpper);
    decreases(logIndexUpper - logIndexLower);

    &&& (logIndexLower == logIndexUpper ==>
      queueIndex == queue.len()
    )
    &&& (logIndexLower < logIndexUpper ==> {
      &&& log.dom().contains(logIndexLower)
      &&& (log.index(logIndexLower).node_id == nodeId ==> {
        &&& queueIndex < queue.len()
        &&& updates.dom().contains(queue.index(queueIndex))
        &&& updates.index(queue.index(queueIndex)).is_Placed()
        &&& updates.index(queue.index(queueIndex)).get_Placed_idx() == logIndexLower
        &&& LogRangeMatchesQueue(queue, log, queueIndex+1, logIndexLower+1, logIndexUpper, nodeId, updates)
      })
      &&& (log.index(logIndexLower).node_id != nodeId ==>
        LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower+1, logIndexUpper, nodeId, updates)
      )
    })
  }

#[verifier::spec]
fn LogRangeNoNodeId(log: Map<nat, LogEntry>,
      logIndexLower: nat, logIndexUpper: nat, nodeId: nat) -> bool
{
  decreases_when(logIndexLower <= logIndexUpper);
  decreases(logIndexUpper - logIndexLower);

  (logIndexLower < logIndexUpper ==> {
    &&& log.dom().contains(logIndexLower)
    &&& log.index(logIndexLower).node_id != nodeId
    &&& LogRangeNoNodeId(log, logIndexLower+1, logIndexUpper, nodeId)
  })
}

proof fn concat_LogRangeNoNodeId_LogRangeMatchesQueue(
    queue: Seq<nat>, log: Map<nat, LogEntry>,
    queueIndex: nat, a: nat, b: nat, c: nat, nodeId: nat, updates: Map<nat, UpdateState>)
requires
    a <= b <= c,
    0 <= queueIndex <= queue.len(),
    LogRangeNoNodeId(log, a, b, nodeId),
    LogRangeMatchesQueue(queue, log, queueIndex, b, c, nodeId, updates),
ensures LogRangeMatchesQueue(queue, log, queueIndex, a, c, nodeId, updates)
decreases b - a
{
  if a == b {
  } else {
    concat_LogRangeNoNodeId_LogRangeMatchesQueue(
        queue, log, queueIndex,
        a+1, b, c,
        nodeId, updates);
  }
}

proof fn append_LogRangeMatchesQueue(
      queue: Seq<nat>,
      log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: nat,
      updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
      new_rid: nat, log_entry: LogEntry)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id == node_id,
        new_updates.dom().contains(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
            new_updates.dom().contains(rid)
            && new_updates.index(rid) === updates.index(rid),
        LogRangeMatchesQueue(queue, log,
            queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logIndexUpper, log_entry),

    ensures LogRangeMatchesQueue(
        queue.push(new_rid),
        new_log,
        queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.dom().contains(logIndexLower) );
     if new_log.index(logIndexLower).node_id == node_id {
        assert( queueIndex < queue.push(new_rid).len());
        assert( new_updates.dom().contains(queue.push(new_rid).index(queueIndex)));
        assert( new_updates.index(queue.push(new_rid).index(queueIndex)).is_Placed());
        assert( new_updates.index(queue.push(new_rid).index(queueIndex)).get_Placed_idx() == logIndexLower);
        assert( LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex+1, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
      }
      if new_log.index(logIndexLower).node_id != node_id {
        assert(LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
      }
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        append_LogRangeMatchesQueue(queue, log, new_log, queueIndex + 1,
            logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);

        /*assert( queueIndex < queue.push(new_rid).len());

        assert( updates.dom().contains(queue.index(queueIndex)));
        let q = queue.push(new_rid).index(queueIndex);
        assert( updates.dom().contains(q));
        assert(q != new_rid);
        assert( new_updates.dom().contains(q));

        assert( new_updates.index(queue.push(new_rid).index(queueIndex)).is_Placed());
        assert( new_updates.index(queue.push(new_rid).index(queueIndex)).get_Placed_idx() == logIndexLower);
        assert( LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex+1, logIndexLower+1, logIndexUpper+1, node_id, new_updates));*/

        assert(LogRangeMatchesQueue(
            queue.push(new_rid),
            new_log,
            queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
    } else {
      append_LogRangeMatchesQueue(queue, log, new_log, queueIndex,
        logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
        /*assert (log.index(logIndexLower).node_id != node_id ==>
          LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower+1, logIndexUpper, node_id, updates)
        );
        assert (new_log.index(logIndexLower).node_id != node_id ==>
          LogRangeMatchesQueue(queue.push(new_rid), new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates)
        );
        return;*/
    }
  }
}

proof fn append_LogRangeMatchesQueue_other_augment(
      queue: Seq<nat>,
      log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, node_id: nat,
      updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
      new_rid: nat, log_entry: LogEntry)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        new_updates.dom().contains(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{
            op: log_entry.op,
            idx: logIndexUpper,
        }),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
            new_updates.dom().contains(rid)
            && new_updates.index(rid) === updates.index(rid),
        LogRangeMatchesQueue(queue, log,
            queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logIndexUpper, log_entry),

    ensures LogRangeMatchesQueue(
        queue,
        new_log,
        queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.dom().contains(logIndexLower) );
     assert(new_log.index(logIndexLower).node_id != node_id);
     assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        append_LogRangeMatchesQueue_other_augment(queue, log, new_log, queueIndex + 1,
            logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);

        assert(LogRangeMatchesQueue(
            queue,
            new_log,
            queueIndex, logIndexLower, logIndexUpper + 1, node_id, new_updates));
    } else {
      append_LogRangeMatchesQueue_other_augment(queue, log, new_log, queueIndex,
        logIndexLower + 1, logIndexUpper, node_id, updates, new_updates, new_rid, log_entry);
    }
  }
}

proof fn append_LogRangeMatchesQueue_other(
      queue: Seq<nat>,
      log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
      queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, logLen: nat, node_id: nat,
      updates: Map<nat, UpdateState>, new_updates: Map<nat, UpdateState>,
      new_rid: nat, log_entry: LogEntry)
    requires
        0 <= queueIndex <= queue.len(),
        logIndexLower <= logIndexUpper <= logLen,
        log_entry.node_id != node_id,
        new_updates.dom().contains(new_rid),
        new_updates.index(new_rid) === (UpdateState::Placed{
            op: log_entry.op,
            idx: logLen,
        }),
        !queue.contains(new_rid),
        forall |rid| #[trigger] updates.dom().contains(rid) && rid != new_rid ==>
            new_updates.dom().contains(rid)
            && new_updates.index(rid) === updates.index(rid),
        LogRangeMatchesQueue(queue, log,
            queueIndex, logIndexLower, logIndexUpper, node_id, updates),
        new_log === log.insert(logLen, log_entry),

    ensures LogRangeMatchesQueue(
        queue,
        new_log,
        queueIndex, logIndexLower, logIndexUpper, node_id, new_updates),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper {
     //assert( new_log.dom().contains(logIndexLower) );
     //assert(new_log.index(logIndexLower).node_id != node_id);
     //assert(LogRangeMatchesQueue(queue, new_log, queueIndex, logIndexLower+1, logIndexUpper+1, node_id, new_updates));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        append_LogRangeMatchesQueue_other(queue, log, new_log, queueIndex + 1,
            logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
    } else {
      append_LogRangeMatchesQueue_other(queue, log, new_log, queueIndex,
        logIndexLower + 1, logIndexUpper, logLen, node_id, updates, new_updates, new_rid, log_entry);
    }
  }
}

proof fn append_LogRangeNoNodeId_other(
      log: Map<nat, LogEntry>, new_log: Map<nat, LogEntry>,
      logIndexLower: nat, logIndexUpper: nat, node_id: nat,
      log_entry: LogEntry)
    requires
        logIndexLower <= logIndexUpper,
        log_entry.node_id != node_id,
        LogRangeNoNodeId(log, logIndexLower, logIndexUpper, node_id),
        new_log === log.insert(logIndexUpper, log_entry),
    ensures LogRangeNoNodeId(new_log, logIndexLower, logIndexUpper + 1, node_id),

    decreases(logIndexUpper - logIndexLower),
{
  if logIndexLower == logIndexUpper + 1 {
  } else if logIndexLower == logIndexUpper {
     assert( new_log.dom().contains(logIndexLower) );
     assert(new_log.index(logIndexLower).node_id != node_id);
     assert(LogRangeNoNodeId(new_log, logIndexLower+1, logIndexUpper+1, node_id));
  } else {
    assert(new_log.index(logIndexLower) === log.index(logIndexLower));
    if new_log.index(logIndexLower).node_id == node_id {
        append_LogRangeNoNodeId_other(log, new_log,
            logIndexLower + 1, logIndexUpper, node_id, log_entry);

        assert(LogRangeNoNodeId(
            new_log,
            logIndexLower, logIndexUpper + 1, node_id));
    } else {
      append_LogRangeNoNodeId_other(log, new_log,
        logIndexLower + 1, logIndexUpper, node_id, log_entry);
    }
  }
}



proof fn LogRangeMatchesQueue_update_change(queue: Seq<nat>, log: Map<nat, LogEntry>,
    queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
    updates1: Map<nat, UpdateState>,
    updates2: Map<nat, UpdateState>)
requires
    0 <= queueIndex <= queue.len(),
    logIndexLower <= logIndexUpper,
    LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
    forall |rid| #[trigger] updates1.dom().contains(rid) ==>
      updates1.index(rid).is_Placed() && logIndexLower <= updates1.index(rid).get_Placed_idx() < logIndexUpper ==>
          updates2.dom().contains(rid) && updates2.index(rid) === updates1.index(rid),
ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2)
decreases logIndexUpper - logIndexLower
{
  if logIndexLower == logIndexUpper {
  } else {
    if log.index(logIndexLower).node_id == nodeId {
      LogRangeMatchesQueue_update_change(queue, log, queueIndex + 1,
        logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    } else {
      LogRangeMatchesQueue_update_change(queue, log, queueIndex,
        logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    }
  }
}

proof fn LogRangeMatchesQueue_update_change_2(queue: Seq<nat>, log: Map<nat, LogEntry>,
    queueIndex: nat, logIndexLower: nat, logIndexUpper: nat, nodeId: nat,
    updates1: Map<nat, UpdateState>,
    updates2: Map<nat, UpdateState>)
requires
    0 <= queueIndex <= queue.len(),
    logIndexLower <= logIndexUpper,
    LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates1),
    forall |rid| #[trigger] updates1.dom().contains(rid) ==> queue.contains(rid) ==>
          updates2.dom().contains(rid) && updates2.index(rid) === updates1.index(rid),
ensures LogRangeMatchesQueue(queue, log, queueIndex, logIndexLower, logIndexUpper, nodeId, updates2),
decreases logIndexUpper - logIndexLower,
{
  if logIndexLower == logIndexUpper {
  } else {
    if log.index(logIndexLower).node_id == nodeId {
      LogRangeMatchesQueue_update_change_2(queue, log, queueIndex + 1,
        logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    } else {
      LogRangeMatchesQueue_update_change_2(queue, log, queueIndex,
        logIndexLower + 1, logIndexUpper, nodeId, updates1, updates2);
    }
  }
}


pub open spec fn QueueRidsUpdatePlaced(queued_ops: Seq<nat>,
    localUpdates: Map<nat, UpdateState>, bound: nat) -> bool
recommends 0 <= bound <= queued_ops.len(),
{
  forall |j| bound <= j < queued_ops.len() ==>
      localUpdates.dom().contains(#[trigger] queued_ops.index(j))
      && localUpdates.index(queued_ops.index(j)).is_Placed()
}

pub open spec fn QueueRidsUpdateDone(queued_ops: Seq<nat>,
    localUpdates: Map<nat, UpdateState>, bound: nat) -> bool
recommends 0 <= bound <= queued_ops.len(),
{
  // Note that use localUpdates.dom().contains(queued_ops.index(j)) as a *hypothesis*
  // here. This is because the model actually allows an update to "leave early"
  // before the combiner phase completes. (This is actually an instance of our
  // model being overly permissive.)
  forall |j| 0 <= j < bound ==>
      localUpdates.dom().contains(#[trigger] queued_ops.index(j)) ==>
              (localUpdates.index(queued_ops.index(j)).is_Applied()
          ||| localUpdates.index(queued_ops.index(j)).is_Done())
}


pub open spec fn seq_unique<V>(rids: Seq<V>) -> bool {
  forall |i, j| 0 <= i < rids.len() && 0 <= j < rids.len() && i != j ==>
      rids.index(i) !== rids.index(j)
}

pub open spec fn LogContainsEntriesUpToHere(log: Map<nat, LogEntry>, end: nat) -> bool {
    forall |i: nat| 0 <= i < end ==> log.dom().contains(i)
}

pub open spec fn seqs_disjoint(s: Seq<nat>, t: Seq<nat>) -> bool
{
  forall |i, j| 0 <= i < s.len() && 0 <= j < t.len() ==> s.index(i) !== t.index(j)
}

pub open spec fn CombinerRidsDistinctTwoNodes(c1: CombinerState, c2: CombinerState) -> bool
{
  !c1.is_Ready() ==> !c2.is_Ready() ==> {
    let queued_ops1 = match c1 {
      CombinerState::Ready => arbitrary(),
      CombinerState::Placed{queued_ops} => queued_ops,
      CombinerState::LoadedHead{queued_ops, ..} => queued_ops,
      CombinerState::Loop{queued_ops, ..} => queued_ops,
      CombinerState::UpdatedVersion{queued_ops, ..} => queued_ops,
    };

    let queued_ops2 = match c2 {
      CombinerState::Ready => arbitrary(),
      CombinerState::Placed{queued_ops} => queued_ops,
      CombinerState::LoadedHead{queued_ops, ..} => queued_ops,
      CombinerState::Loop{queued_ops, ..} => queued_ops,
      CombinerState::UpdatedVersion{queued_ops, ..} => queued_ops,
    };

    seqs_disjoint(queued_ops1, queued_ops2)
  }
}

pub enum ReadReq {
    Init{op: ReadonlyOp},
    Req{ctail_at_start: nat, op: ReadonlyOp},
}

pub struct UpdateResp {
    pub idx_in_log: nat,
}

spec fn state_at_version(log: Seq<UpdateOp>, version: nat) -> NRState
recommends 0 <= version <= log.len()
decreases version
{
  if version == 0 {
    init_state()
  } else {
    update_state(state_at_version(log, (version - 1) as nat), log.index(version as int - 1)).0
  }
}


state_machine!{
    SimpleLog {
        fields {
            pub log: Seq<UpdateOp>,
            pub ctail: nat,
            pub readonly_reqs: Map<nat, ReadReq>,
            pub update_reqs: Map<nat, UpdateOp>,
            pub update_resps: Map<nat, UpdateResp>,
        }

        init!{
            initialize() {
                init log = Seq::empty();
                init ctail = 0;
                init readonly_reqs = Map::empty();
                init update_reqs = Map::empty();
                init update_resps = Map::empty();
            }
        }

        transition!{
            increase_ctail(new_ctail: nat) {
                require(pre.ctail <= new_ctail <= pre.log.len());
                update ctail = new_ctail;
            }
        }

        transition!{
            start_readonly(rid: nat, op: ReadonlyOp) {
                require(!pre.readonly_reqs.dom().contains(rid));
                require(!pre.update_reqs.dom().contains(rid));
                require(!pre.update_resps.dom().contains(rid));

                update readonly_reqs[rid] = ReadReq::Init{ op };
            }
        }

        transition!{
            read_ctail(rid: nat) {
                require(pre.readonly_reqs.dom().contains(rid));
                require let ReadReq::Init { op } = pre.readonly_reqs.index(rid);

                update readonly_reqs[rid] = ReadReq::Req{ op, ctail_at_start: pre.ctail };
            }
        }

        transition!{
            finish_readonly(rid: nat, version: nat) {
                require(pre.readonly_reqs.dom().contains(rid));

                require let ReadReq::Req { op, ctail_at_start } = pre.readonly_reqs.index(rid);

                require(ctail_at_start <= version <= pre.log.len());
                require(version <= pre.ctail);
                update readonly_reqs = pre.readonly_reqs.remove(rid);
            }
        }

        transition!{
            start_update(rid: nat, op: UpdateOp) {
                require(!pre.readonly_reqs.dom().contains(rid));
                require(!pre.update_reqs.dom().contains(rid));
                require(!pre.update_resps.dom().contains(rid));

                update update_reqs[rid] = op;
            }
        }

        /*transition!{
            add_update_to_log(rid: nat) {
                
            }
        }*/

        transition!{
            end_update(rid: nat) {
                require(pre.update_resps.dom().contains(rid));
                let idx = pre.update_resps.index(rid).idx_in_log;

                require(pre.ctail > idx);
                require(pre.log.len() > idx);

                update update_resps = pre.update_resps.remove(rid);
            }
        }

        transition!{
            no_op() { }
        }

    }
}

spec fn interp_log(global_tail: nat, log: Map<nat, LogEntry>) -> Seq<UpdateOp> {
    Seq::new(global_tail, |i| log.index(i as nat).op)
}

spec fn interp_readonly_reqs(local_reads: Map<nat, ReadonlyState>) -> Map<nat, ReadReq> {
    Map::new(
        |rid| local_reads.dom().contains(rid),
        |rid| match local_reads.index(rid) {
            ReadonlyState::Init { op } => ReadReq::Init { op },
            ReadonlyState::VersionUpperBound { version_upper_bound: idx, op } => ReadReq::Req { op, ctail_at_start: idx },
            ReadonlyState::ReadyToRead { version_upper_bound: idx, op, .. } => ReadReq::Req { op, ctail_at_start: idx },
            ReadonlyState::Done { version_upper_bound: idx, op, .. } => ReadReq::Req { op, ctail_at_start: idx },
        },
    )
}

spec fn interp_update_reqs(local_updates: Map<nat, UpdateState>) -> Map<nat, UpdateOp> {
    Map::new(
        |rid| local_updates.dom().contains(rid) && local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => op,
            _ => arbitrary(),
        }
    )
}

spec fn interp_update_resps(local_updates: Map<nat, UpdateState>) -> Map<nat, UpdateResp> {
    Map::new(
        |rid| local_updates.dom().contains(rid) && !local_updates.index(rid).is_Init(),
        |rid| match local_updates.index(rid) {
            UpdateState::Init{op} => arbitrary(),
            UpdateState::Placed{op, idx} => UpdateResp { idx_in_log: idx },
            UpdateState::Applied{ret, idx} => UpdateResp { idx_in_log: idx },
            UpdateState::Done{ret, idx} => UpdateResp { idx_in_log: idx },
        },
    )
}

spec fn interp(s: UnboundedLog::State) -> SimpleLog::State {
    SimpleLog::State {
        log: interp_log(s.global_tail, s.log),
        ctail: s.version_upper_bound,
        readonly_reqs: interp_readonly_reqs(s.local_reads),
        update_reqs: interp_update_reqs(s.local_updates),
        update_resps: interp_update_resps(s.local_updates),
    }
}


#[verifier::proof]
fn refinement(pre: UnboundedLog::State, post: UnboundedLog::State)
    requires
        pre.invariant(),
        post.invariant(),
        interp(pre).invariant(),
        UnboundedLog::State::next_strong(pre, post),
    ensures
        SimpleLog::State::next(interp(pre), interp(post)),
{
    case_on_next_strong!{pre, post, UnboundedLog => {
        readonly_new(op) => {
            let rid = get_new_nat(pre.local_reads.dom());
            assert_maps_equal!(
                pre.local_reads.insert(rid, ReadonlyState::Init {op}),
                post.local_reads
            );
            assert_maps_equal!(
                interp(pre).readonly_reqs.insert(rid, ReadReq::Init{op}),
                interp(post).readonly_reqs
            );
            SimpleLog::show::start_readonly(interp(pre), interp(post), rid, op);
        }
        readonly_read_ctail(rid) => {
            SimpleLog::show::read_ctail(interp(pre), interp(post), rid);
        }
        readonly_ready_to_read(rid, node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        readonly_apply(rid) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        readonly_finish(rid, op, version_upper_bound, node_id, ret) => {
            assume(false);
            //SimpleLog::show::finish_readonly(interp(pre), interp(post), rid, );
        }
        exec_trivial_start(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        advance_tail_one(node_id, rid) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_load_tail(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_load_local_head(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_load_global_head(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_dispatch_local(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_dispatch_remote(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_update_version_upper_bound(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
        exec_goto_ready(node_id) => {
            SimpleLog::show::no_op(interp(pre), interp(post));
        }
    }}
}

fn main() { }

}
