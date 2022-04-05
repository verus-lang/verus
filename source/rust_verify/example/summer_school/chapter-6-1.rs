// rust_verify/tests/example.rs ignore
// TODO this is a work-in-progress

#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::seq::*;
use pervasive::map::*;
use pervasive::set::*;

use state_machines_macros::state_machine;
use state_machines_macros::case_on_next;
use state_machines_macros::case_on_init;

#[verifier(external_body)]
struct Key { }

#[verifier(external_body)]
struct Value { }

#[verifier(external_body)]
#[spec]
pub fn default() -> Value { unimplemented!() }

state_machine!{
    MapSpec {
        fields {
            pub map: Map<Key, Value>,
        }

        init!{
            empty() {
                init map = Map::total(|k| default());
            }
        }

        transition!{
            insert_op(key: Key, value: Value) {
                update map = pre.map.insert(key, value);
            }
        }

        transition!{
            query_op(key: Key, value: Value) {
                require(pre.map.contains_pair(key, value));
            }
        }

        transition!{
            noop() {
            }
        }
    }
}

state_machine!{
    ShardedKVProtocol {
        fields {
            // TODO have a way to annotate this as a constant outside of tokenized mode
            pub map_count: nat,

            pub maps: Seq<Map<Key, Value>>,
        }

        init!{
            initialize(map_count: nat) {
                require(0 < map_count);
                init map_count = map_count;
                init maps = Seq::new(map_count, |i| {
                    if i == 0 {
                        Map::total(|k| default())
                    } else {
                        Map::empty()
                    }
                });
            }
        }

        #[spec]
        pub fn valid_host(&self, i: nat) -> bool {
            i < self.map_count
        }

        transition!{
            insert(idx: nat, key: Key, value: Value) {
                require(pre.valid_host(idx));
                require(pre.maps.index(idx).dom().contains(key));
                update maps[idx][key] = value;
            }
        }

        transition!{
            query(idx: nat, key: Key, value: Value) {
                require(pre.valid_host(idx));
                require(pre.maps.index(idx).contains_pair(key, value));
            }
        }

        transition!{
            transfer(send_idx: nat, recv_idx: nat, key: Key, value: Value) {
                require(pre.valid_host(send_idx));
                require(pre.valid_host(recv_idx));
                require(pre.maps.index(send_idx).contains_pair(key, value));
                require(send_idx != recv_idx);
                update maps[send_idx] = pre.maps.index(send_idx).remove(key);
                update maps[recv_idx][key] = value;
            }
        }

        #[spec]
        pub fn host_has_key(&self, hostidx: nat, key: Key) -> bool {
            self.valid_host(hostidx)
            && self.maps.index(hostidx).dom().contains(key)
        }

        #[spec]
        pub fn key_holder(&self, key: Key) -> nat {
            choose(|idx| self.host_has_key(idx, key))
        }

        #[spec]
        pub fn abstraction_one_key(&self, key: Key) -> Value {
            if exists(|idx| self.host_has_key(idx, key)) {
                self.maps.index(self.key_holder(key)).index(key)
            } else {
                default()
            }
        }

        #[spec]
        pub fn interp_map(&self) -> Map<Key, Value> {
            Map::total(|key| self.abstraction_one_key(key))
        }

        #[invariant]
        pub fn num_hosts(&self) -> bool {
            self.maps.len() == self.map_count
        }

        #[invariant]
        pub fn inv_no_dupes(&self) -> bool {
            forall(|i: nat, j: nat, key: Key|
                self.host_has_key(i, key) && self.host_has_key(j, key) >>= i == j)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, map_count: nat) {
        }
       
        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, idx: nat, key: Key, value: Value) {
            //assert(forall(|k: Key| pre.host_has_key(idx, k) >>= post.host_has_key(idx, k)));
            //assert(forall(|k: Key| post.host_has_key(idx, k) >>= pre.host_has_key(idx, k)));
            //assert(forall(|k: Key| pre.host_has_key(idx, k) == post.host_has_key(idx, k)));
            assert(forall(|i: nat, k: Key| pre.host_has_key(i, k) == post.host_has_key(i, k)));
        }
       
        #[inductive(query)]
        fn query_inductive(pre: Self, post: Self, idx: nat, key: Key, value: Value) { }
       
        #[inductive(transfer)]
        fn transfer_inductive(pre: Self, post: Self, send_idx: nat, recv_idx: nat, key: Key, value: Value) {
            assert(forall(|i: nat, k: Key| !equal(k, key) >>= pre.host_has_key(i, k) == post.host_has_key(i, k)));
            assert(forall(|i: nat| i != send_idx && i != recv_idx >>= pre.host_has_key(i, key) == post.host_has_key(i, key)));

            assert(equal(post.maps.index(send_idx),
                pre.maps.index(send_idx).remove(key)));

            assert(!post.host_has_key(send_idx, key));
            assert(pre.host_has_key(send_idx, key));

            /*assert_forall_by(|i: nat, j: nat, k: Key| {
                requires(post.host_has_key(i, k) && post.host_has_key(j, k));
                ensures(i == j);
                if equal(k, key) {
                    assert(i != send_idx);
                    assert(j != send_idx);
                    if i != recv_idx {
                        assert(pre.host_has_key(i, key));
                    }
                    if i != recv_idx && j != recv_idx {
                        assert(pre.host_has_key(i, key));
                        assert(pre.host_has_key(j, key));
                        assert(pre.inv_no_dupes());
                        assert(i == j);
                    }
                    assert(i == j);
                } else {
                    assert(i == j);
                }
            });*/
        }
    }
}




#[spec]
fn interp(a: ShardedKVProtocol::State) -> MapSpec::State {
    MapSpec::State {
        map: a.interp_map()
    }
}


#[proof]
fn next_refines_next_with_macro(pre: ShardedKVProtocol::State, post: ShardedKVProtocol::State) {
    requires(pre.invariant()
        && post.invariant()
        && interp(pre).invariant()
        && ShardedKVProtocol::State::next(pre, post)
    );

    ensures(MapSpec::State::next(interp(pre), interp(post)));

    case_on_next!{pre, post, ShardedKVProtocol => {
        insert(idx, key, value) => {
            MapSpec::show::insert_op(interp(pre), interp(post), key, value);
        }
        query(idx, key, value) => {
            assert(interp(pre).map.ext_equal(interp(post).map));
            assert(equal(interp(pre).map, interp(post).map));

            assert(equal(Map::total(|key| pre.abstraction_one_key(key)).dom(),
                Set::empty().complement()));
            assert(equal(pre.interp_map(),
                Map::total(|key| pre.abstraction_one_key(key))));
            assert(equal(pre.interp_map().dom(), Set::empty().complement()));

            assert(equal(interp(pre).map.dom(), Set::empty().complement()));
            assert(interp(pre).map.dom().contains(key));
            assert(equal(interp(pre).map.index(key), value));
            MapSpec::show::query_op(interp(pre), interp(post), key, value);
        }
        transfer(send_idx, recv_idx, key, value) => {
            MapSpec::show::noop(interp(pre), interp(post));
        }
    }}
}

#[proof]
fn init_refines_init_with_macro(post: ShardedKVProtocol::State) {
    requires(post.invariant() && ShardedKVProtocol::State::init(post));

    ensures(MapSpec::State::init(interp(post)));

    case_on_init!{post, ShardedKVProtocol => {
        initialize(n) => {
            assert_forall_by(|k: Key| {
                ensures(
                    interp(post).map.dom().contains(k) &&
                    equal(interp(post).map.index(k), default())
                );
                assert(interp(post).map.dom().contains(k));
                assert(equal(interp(post).map.index(k), default()));
            });
            assert(interp(post).map.ext_equal(
                Map::total(|k| default())));
            MapSpec::show::empty(interp(post));
        }
    }}
}

fn main() {
}
