#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::map::*;
use pervasive::seq::*;
use pervasive::option::*;

use state_machines_macros::tokenized_state_machine;

// Based off of the FlatCombine system from Seagull-NR.
// A major difference is that one didn't make any use of storage, because storage was
// rather complicated to use, and it wasn't necessary.
// Now, I expect storage to be a lot easier to use, easier than the alternative.

struct Request {
    pub rid: int,
    pub req: int,
}

struct Response {
    pub rid: int,
    pub resp: int,
}

#[is_variant]
enum Client {
    Idle,
    Waiting {rid: int},
}

#[is_variant]
enum Combiner {
    Collecting {elems: Seq<Option<int>>},
    Responding {elems: Seq<Option<int>>, idx: nat},
}

tokenized_state_machine!{
    FlatCombiner {
        fields {
            #[sharding(constant)]
            pub num_clients: nat,

            #[sharding(map)]
            pub clients: Map<nat, Client>,

            #[sharding(map)]
            pub slots: Map<nat, bool>,

            #[sharding(variable)]
            pub combiner: Combiner,

            #[sharding(storage_map)]
            pub requests: Map<nat, Request>,

            #[sharding(storage_map)]
            pub responses: Map<nat, Response>,
        }

        #[spec]
        fn valid_idx(self, i: nat) -> bool {
            0 <= i && i < self.num_clients
        }

        #[invariant]
        fn clients_complete(self) -> bool {
            forall(|i: nat| (0 <= i && i < self.num_clients) ==
                self.clients.dom().contains(i))
        }

        #[invariant]
        fn slots_complete(self) -> bool {
            forall(|i: nat| (0 <= i && i < self.num_clients) ==
                self.slots.dom().contains(i))
        }

        #[invariant]
        fn clients_size(self) -> bool {
            match self.combiner {
                Combiner::Collecting{elems} => elems.len() <= self.num_clients,
                Combiner::Responding{elems, idx} => elems.len() == self.num_clients &&
                    0 <= idx && idx <= self.num_clients,
            }
        }

        /*
        #[spec]
        fn should_have_req_stored(self, i: nat) -> bool {
            0 <= i
            && i < self.slots
            && self.slots.index(i)
            && match self.combiner {
                Combiner::Collecting{elems} => elems.len() < i || elems.index(i).is_None()
                Combiner::Responding{elems, idx} => idx >= i || elems.index(i).is_None()
            }
        }
        */

        #[spec]
        fn client_waiting(self, i: nat) -> bool {
            self.valid_idx(i)
            && self.clients.index(i).is_Waiting()
        }

        #[spec]
        fn combiner_has(self, i: nat) -> bool {
            self.valid_idx(i)
            && match self.combiner {
                Combiner::Collecting{elems} => i < elems.len() && elems.index(i).is_Some(),
                Combiner::Responding{elems, idx} => i >= idx && elems.index(i).is_Some(),
            }
        }

        #[spec]
        fn combiner_rid(self, i: nat) -> int {
            match self.combiner {
                Combiner::Collecting{elems} => elems.index(i).get_Some_0(),
                Combiner::Responding{elems, idx} => elems.index(i).get_Some_0(),
            }
        }

        #[spec]
        fn request_stored(self, i: nat) -> bool {
            self.requests.dom().contains(i)
        }

        #[spec]
        fn response_stored(self, i: nat) -> bool {
            self.responses.dom().contains(i)
        }

        #[invariant]
        fn not_waiting_inv(self) -> bool {
            forall(|i: nat| #[trigger] self.valid_idx(i) && self.clients.index(i).is_Idle() >>=
                !self.slots.index(i))
        }

        #[invariant]
        fn waiting_inv(self) -> bool {
            forall(|i: nat| #[trigger] self.client_waiting(i) >>=
                self.request_stored(i) || self.response_stored(i) || self.combiner_has(i))
        }

        #[invariant]
        fn request_stored_inv(self) -> bool {
            forall(|i: nat| #[trigger] self.request_stored(i) >>=
                self.client_waiting(i)
                && self.requests.index(i).rid == self.clients.index(i).get_Waiting_rid()
                && self.slots.index(i))
        }

        #[invariant]
        fn response_stored_inv(self) -> bool {
            forall(|i: nat| #[trigger] self.response_stored(i) >>=
                self.client_waiting(i)
                && self.responses.index(i).rid == self.clients.index(i).get_Waiting_rid()
                && !self.slots.index(i))
        }


        #[invariant]
        fn combiner_has_inv(self) -> bool {
            forall(|i: nat| #[trigger] self.combiner_has(i) >>=
                self.client_waiting(i)
                && self.slots.index(i)
                && self.combiner_rid(i) == self.clients.index(i).get_Waiting_rid()
                && !self.request_stored(i)
            )
        }

        init!{
            init(num_clients: nat) {
                init num_clients = num_clients;
                init clients = Map::new(
                    |i| 0 <= i && i < num_clients,
                    |i| Client::Idle);
                init slots = Map::new(
                    |i| 0 <= i && i < num_clients,
                    |i| false);
                init combiner = Combiner::Collecting { elems: Seq::empty() };
                init requests = Map::empty();
                init responses = Map::empty();
            }
        }

        #[inductive(init)]
        fn init_inductive(post: FlatCombiner, num_clients: nat) { }

        ///// Client transitions

        transition!{
            client_send(j: nat, request: Request, cur_slot: bool) {
                require(0 <= j && j < self.num_clients);

                // Move client to 'waiting' state
                remove clients -= [j => Client::Idle];
                add    clients += [j => Client::Waiting{rid: request.rid}];

                // Set the slot
                remove slots -= [j => cur_slot];
                add    slots += [j => true];

                // deposit the request
                deposit requests += [j => request] by {
                    assert(!self.request_stored(j));
                };
            }
        }

        #[inductive(client_send)]
        fn client_send_inductive(self: FlatCombiner,
            post: FlatCombiner, j: nat, request: Request, cur_slot: bool)
        {
            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(self.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) && i != j >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) && i != j >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) >>= self.response_stored(i)));

            assert(post.request_stored(j));
            assert(post.client_waiting(j));

            /*assert_forall_by(|i: nat| {
                requires(post.client_waiting(i));
                ensures(post.request_stored(i) || post.response_stored(i) || post.combiner_has(i));
                if i == j {
                    assert(post.request_stored(i));
                } else {
                    assert(self.client_waiting(i));
                    assert(post.request_stored(i) || post.response_stored(i) || post.combiner_has(i));
                }
            });*/
        }
            
        transition!{
            client_recv(j: nat, rid: int) {
                require(0 <= j && j < self.num_clients);

                // Move client to 'idle' state
                remove clients -= [j => Client::Waiting{rid}];
                add    clients += [j => Client::Idle];

                // Check that the slot has been set back to 'false'
                have slots >= [j => false];

                // withdraw the response
                birds_eye let response = self.responses.index(j);
                withdraw responses -= [j => response] by {
                    assert(self.client_waiting(j));
                    //assert(!self.request_stored(j));
                    //assert(!self.combiner_has(j));
                    //assert(self.response_stored(j));
                };

                // make sure we get back the response for the correct request id:
                assert(response.rid == rid) by {
                    assert(self.client_waiting(j));
                };
            }
        }

        #[inductive(client_recv)]
        fn client_recv_inductive(self: FlatCombiner, post: FlatCombiner, j: nat, rid: int) {
            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(self.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) && i != j >>= self.response_stored(i)));

            assert(!post.client_waiting(j));
        }

        ///// Combiner transitions

        transition!{
            combiner_recv() {
                require(self.combiner.is_Collecting());
                let j = self.combiner.get_Collecting_elems().len();
                require(0 <= j && j < self.num_clients);

                // Observe that the slot has been set to 'true'
                have slots >= [j => true];

                // Withdraw a request
                birds_eye let request = self.requests.index(j);
                withdraw requests -= [j => request] by {
                    assert(self.valid_idx(j));
                    assert(self.client_waiting(j));
                    assert(self.request_stored(j));
                };

                // Update combiner's local state to remember we withdrew a request with this ID
                update combiner = Combiner::Collecting{
                    elems: self.combiner.get_Collecting_elems().push(Option::Some(request.rid)),
                };
            }
        }

        #[inductive(combiner_recv)]
        fn combiner_recv_inductive(self: FlatCombiner, post: FlatCombiner) {
            let j = self.combiner.get_Collecting_elems().len();
            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(post.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) && i != j >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) >>= self.response_stored(i)));

            assert(post.combiner_has(j));
        }

        transition!{
            combiner_skip() {
                require(self.combiner.is_Collecting());
                let j = self.combiner.get_Collecting_elems().len();
                require(0 <= j && j < self.num_clients);

                // In practice, this happens when slot j is set to false, so we could add this:
                //    have slots >= [j => false];
                // but it's not necessary

                // Update combiner's local state to remember that we didn't withdraw
                // anything here.
                update combiner = Combiner::Collecting{
                    elems: self.combiner.get_Collecting_elems().push(Option::None),
                };
            }
        }

        #[inductive(combiner_skip)]
        fn combiner_skip_inductive(self: FlatCombiner, post: FlatCombiner) {
            let j = self.combiner.get_Collecting_elems().len();
            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(post.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) && i != j >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) >>= self.response_stored(i)));

            assert(!post.combiner_has(j));
        }

        transition!{
            combiner_go_to_responding() {
                require(self.combiner.is_Collecting());
                require(self.combiner.get_Collecting_elems().len() == self.num_clients);
                update combiner = Combiner::Responding{
                    elems: self.combiner.get_Collecting_elems(),
                    idx: 0,
                };
            }
        }

        transition!{
            combiner_send(response: Response, cur_slot: bool) {
                require(self.combiner.is_Responding());
                let j = self.combiner.get_Responding_idx();
                require(0 <= j && j < self.num_clients);
                let response_opt = self.combiner.get_Responding_elems().index(j);

                // The response we return has to have the right request ID
                require(equal(response_opt, Option::Some(response.rid)));

                // Set the slot back to false
                remove slots -= [j => cur_slot];
                add    slots += [j => false];

                // Update the combiner's local state
                update combiner = Combiner::Responding{
                    elems: self.combiner.get_Responding_elems(),
                    idx: j + 1,
                };

                deposit responses += [j => response] by {
                    assert(self.valid_idx(j));
                    assert(self.combiner_has(j));
                    assert(!self.response_stored(j));
                };
            }
        }

        #[inductive(combiner_send)]
        fn combiner_send_inductive(self: FlatCombiner, post: FlatCombiner, response: Response, cur_slot: bool) {
            let j = self.combiner.get_Responding_idx();

            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(post.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) && i != j >>= self.response_stored(i)));

            assert(!post.combiner_has(j));
        }

        transition!{
            combiner_send_skip() {
                require(self.combiner.is_Responding());
                let j = self.combiner.get_Responding_idx();
                require(0 <= j && j < self.num_clients);
                let response_opt = self.combiner.get_Responding_elems().index(j);

                // The response we return has to have the right request ID
                require(equal(response_opt, Option::None));

                // Update the combiner's local state
                update combiner = Combiner::Responding{
                    elems: self.combiner.get_Responding_elems(),
                    idx: j + 1,
                };
            }
        }

        #[inductive(combiner_send_skip)]
        fn combiner_send_skip_inductive(self: FlatCombiner, post: FlatCombiner) {
            let j = self.combiner.get_Responding_idx();

            assert(forall(|i| post.valid_idx(i) >>= self.valid_idx(i)));
            assert(post.valid_idx(j));
            assert(forall(|i| post.client_waiting(i) >>= self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) >>= self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) >>= self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) >>= self.response_stored(i)));

            assert(!post.combiner_has(j));
        }

        #[inductive(combiner_go_to_responding)]
        fn combiner_go_to_responding_inductive(self: FlatCombiner, post: FlatCombiner) {
            assert(forall(|i| post.valid_idx(i) == self.valid_idx(i)));
            assert(forall(|i| post.client_waiting(i) == self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) == self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) == self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) == self.response_stored(i)));
        }

        transition!{
            combiner_go_to_collecting() {
                require(self.combiner.is_Responding());
                require(self.combiner.get_Responding_idx() == self.num_clients);
                update combiner = Combiner::Collecting{ elems: Seq::empty() };
            }
        }

        #[inductive(combiner_go_to_collecting)]
        fn combiner_go_to_collecting_inductive(self: FlatCombiner, post: FlatCombiner) {
            assert(forall(|i| post.valid_idx(i) == self.valid_idx(i)));
            assert(forall(|i| post.client_waiting(i) == self.client_waiting(i)));
            assert(forall(|i| post.combiner_has(i) == self.combiner_has(i)));
            assert(forall(|i| post.request_stored(i) == self.request_stored(i)));
            assert(forall(|i| post.response_stored(i) == self.response_stored(i)));
        }

    }
}

fn main() { }
