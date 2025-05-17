#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::map::*;
use vstd::seq::*;
use vstd::set::*;
use vstd::{pervasive::*, *};

use state_machines_macros::case_on_init;
use state_machines_macros::case_on_next;
use state_machines_macros::state_machine;

verus! {

#[verifier::external_body]  /* vattr */
pub struct Key {}

#[verifier::external_body]  /* vattr */
pub struct Value {}

#[verifier::external_body]  /* vattr */
#[verifier::spec]
pub fn default() -> Value {
    unimplemented!()
}

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
            pub map_count: int,

            pub maps: Seq<Map<Key, Value>>,
        }

        init!{
            initialize(map_count: int) {
                require(0 < map_count);
                init map_count = map_count;
                init maps = Seq::new(map_count as nat, |i| {
                    if i == 0 {
                        Map::total(|k| default())
                    } else {
                        Map::empty()
                    }
                });
            }
        }

        pub open spec fn valid_host(&self, i: int) -> bool {
            0 <= i < self.map_count
        }

        transition!{
            insert(idx: int, key: Key, value: Value) {
                require(pre.valid_host(idx));
                require(pre.maps.index(idx).dom().contains(key));
                update maps[idx][key] = value;
            }
        }

        transition!{
            query(idx: int, key: Key, value: Value) {
                require(pre.valid_host(idx));
                require(pre.maps.index(idx).contains_pair(key, value));
            }
        }

        transition!{
            transfer(send_idx: int, recv_idx: int, key: Key, value: Value) {
                require(pre.valid_host(send_idx));
                require(pre.valid_host(recv_idx));
                require(pre.maps.index(send_idx).contains_pair(key, value));
                require(send_idx != recv_idx);
                update maps[send_idx] = pre.maps.index(send_idx).remove(key);
                update maps[recv_idx][key] = value;
            }
        }

        pub open spec fn host_has_key(&self, hostidx: int, key: Key) -> bool {
            self.valid_host(hostidx)
            && self.maps.index(hostidx).dom().contains(key)
        }

        pub open spec fn key_holder(&self, key: Key) -> int {
            choose|idx| self.host_has_key(idx, key)
        }

        pub open spec fn abstraction_one_key(&self, key: Key) -> Value {
            if exists |idx| self.host_has_key(idx, key) {
                self.maps.index(self.key_holder(key)).index(key)
            } else {
                default()
            }
        }

        pub open spec fn interp_map(&self) -> Map<Key, Value> {
            Map::total(|key| self.abstraction_one_key(key))
        }

        #[invariant]
        pub open fn num_hosts(&self) -> bool {
            self.maps.len() == self.map_count
        }

        #[invariant]
        pub open fn inv_no_dupes(&self) -> bool {
            forall |i: int, j: int, key: Key|
                self.host_has_key(i, key) && self.host_has_key(j, key) ==> i == j
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, map_count: int) {
        }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, idx: int, key: Key, value: Value) {
            //assert(forall(|k: Key| pre.host_has_key(idx, k) ==> post.host_has_key(idx, k)));
            //assert(forall(|k: Key| post.host_has_key(idx, k) ==> pre.host_has_key(idx, k)));
            //assert(forall(|k: Key| pre.host_has_key(idx, k) == post.host_has_key(idx, k)));
            assert(forall |i: int, k: Key| pre.host_has_key(i, k) == post.host_has_key(i, k));
        }

        #[inductive(query)]
        fn query_inductive(pre: Self, post: Self, idx: int, key: Key, value: Value) { }

        #[inductive(transfer)]
        fn transfer_inductive(pre: Self, post: Self, send_idx: int, recv_idx: int, key: Key, value: Value) {
            assert(forall |i: int, k: Key| !equal(k, key) ==> pre.host_has_key(i, k) == post.host_has_key(i, k));
            assert(forall |i: int| i != send_idx && i != recv_idx ==> pre.host_has_key(i, key) == post.host_has_key(i, key));

            assert(equal(post.maps.index(send_idx),
                pre.maps.index(send_idx).remove(key)));

            assert(!post.host_has_key(send_idx, key));
            assert(pre.host_has_key(send_idx, key));

            /*assert_forall_by(|i: int, j: int, k: Key| {
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

spec fn interp(a: ShardedKVProtocol::State) -> MapSpec::State {
    MapSpec::State { map: a.interp_map() }
}

proof fn next_refines_next_with_macro(pre: ShardedKVProtocol::State, post: ShardedKVProtocol::State)
    requires
        pre.invariant(),
        post.invariant(),
        interp(pre).invariant(),
        ShardedKVProtocol::State::next(pre, post),
    ensures
        MapSpec::State::next(interp(pre), interp(post)),
{
    case_on_next!{pre, post, ShardedKVProtocol => {
        insert(idx, key, value) => {
            assert_maps_equal!(pre.interp_map().insert(key, value), post.interp_map(), k => {
                if equal(k, key) {
                    assert(pre.host_has_key(idx, key));
                    assert(post.host_has_key(idx, key));
                } else {
                    assert(pre.interp_map().dom().contains(k));
                    assert(post.interp_map().dom().contains(k));

                    if exists |idx| pre.host_has_key(idx, k) {
                        let i = pre.key_holder(k);
                        assert(pre.host_has_key(i, k));
                        assert(post.host_has_key(i, k));
                        assert(equal(pre.interp_map().index(k), post.interp_map().index(k)));
                    } else {
                        assert(forall |idx| post.host_has_key(idx, k) ==> pre.host_has_key(idx, k));
                        /*assert(forall |idx| !post.host_has_key(idx, k));
                        assert(!exists(|idx| post.host_has_key(idx, k)));
                        assert(equal(pre.abstraction_one_key(k), default()));
                        assert(equal(post.abstraction_one_key(k), default()));
                        assert(equal(pre.interp_map().index(k), post.interp_map().index(k)));*/
                    }

                    /*assert(pre.interp_map().dom().contains(k) ==>
                        post.interp_map().dom().contains(k)
                        && equal(pre.interp_map().index(k), post.interp_map().index(k))
                    );
                    assert(post.interp_map().dom().contains(k) ==>
                        pre.interp_map().dom().contains(k));*/
                }
            });
            MapSpec::show::insert_op(interp(pre), interp(post), key, value);
        }
        query(idx, key, value) => {
            //assert(interp(pre).map =~= interp(post).map);
            //assert(equal(interp(pre).map, interp(post).map));

            //assert(equal(Map::total(|key| pre.abstraction_one_key(key)).dom(),
            //    Set::empty().complement()));
            //assert(equal(pre.interp_map(),
            //    Map::total(|key| pre.abstraction_one_key(key))));
            //assert(equal(pre.interp_map().dom(), Set::empty().complement()));

            //assert(equal(interp(pre).map.dom(), Set::empty().complement()));
            //assert(interp(pre).map.dom().contains(key));
            //assert(equal(interp(pre).map.index(key),
            //    pre.abstraction_one_key(key)));

            assert(pre.host_has_key(idx, key));
            //assert(pre.host_has_key(pre.key_holder(key), key));
            //assert(equal(pre.key_holder(key), idx));

            //assert(equal(pre.abstraction_one_key(key), value));
            //assert(equal(interp(pre).map.index(key), value));
            MapSpec::show::query_op(interp(pre), interp(post), key, value);
        }
        transfer(send_idx, recv_idx, key, value) => {
            assert_maps_equal!(pre.interp_map(), post.interp_map(), k: Key => {
                if equal(k, key) {
                    assert(pre.host_has_key(send_idx, key));
                    assert(post.host_has_key(recv_idx, key));
                } else {
                    assert(pre.interp_map().dom().contains(k));
                    assert(post.interp_map().dom().contains(k));

                    if exists |idx| pre.host_has_key(idx, k) {
                        let i = pre.key_holder(k);
                        assert(pre.host_has_key(i, k));
                        assert(post.host_has_key(i, k));
                        assert(equal(pre.interp_map().index(k), post.interp_map().index(k)));
                    } else {
                        assert(forall |idx| post.host_has_key(idx, k) ==> pre.host_has_key(idx, k));
                    }
                }
            });
            MapSpec::show::noop(interp(pre), interp(post));
        }
    }}
}

proof fn init_refines_init_with_macro(post: ShardedKVProtocol::State)
    requires
        post.invariant() && ShardedKVProtocol::State::init(post),
    ensures
        MapSpec::State::init(interp(post)),
{
    case_on_init!{post, ShardedKVProtocol => {
        initialize(n) => {
            assert_maps_equal!(interp(post).map, Map::total(|k| default()), k: Key => {
                assert(interp(post).map.dom().contains(k));
                assert(equal(interp(post).map.index(k), default()));
            });

            MapSpec::show::empty(interp(post));
        }
    }}
}

fn main() {
}

} // verus!
