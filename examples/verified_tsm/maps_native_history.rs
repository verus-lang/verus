//! Entire original maps.rs model plus all previous checked client histories.
//! X's second history allocates an invariant State; it is not initializer-reachable.
#[path = "maps.rs"]
mod original;
use original::{Fancy, X};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

fn main() {
    proof {
        {
            let tracked (Tracked(instance), Tracked(mut bool_map)) = X::Instance::initialize(false);
            let tracked token = bool_map.remove(5);
            let tracked token = instance.add(5, token);
            assert(token.key() == 5 && token.value());
            bool_map.insert(token);
            assert(bool_map.map() == IMap::<int, bool>::empty().insert(5, true));
        }
        {
            let state = X::State {
                bool_map: IMap::empty().insert(5int, false).insert(19int, false),
            };
            let tracked token = X::Token::alloc_state(state);
            let owner = X::Fragment { bool_map: map_frag(IMap::empty().insert(5int, false)) };
            let observer = X::Fragment { bool_map: map_frag(IMap::empty().insert(19int, false)) };
            map_join(IMap::empty().insert(5int, false), IMap::empty().insert(19int, false));
            assert(IMap::empty().insert(5int, false).union_prefer_right(
                IMap::empty().insert(19int, false),
            ) =~= state.bool_map);
            let tracked (owner, observer) = token.split(owner, observer);
            let old = owner.fragment();
            let shared = observer.fragment();
            assert(X::Protocol::add_have_requires(old, shared, 5int)) by {
                let combined = X::Fragment::op(old, shared);
                assert forall|frame: X::Fragment, pre: X::State|
                    pre.invariant() && X::Fragment::op(combined, frame) == X::Protocol::embed(
                        pre,
                    ) implies X::State::add_have_enabled(pre, 5int)
                    && X::State::add_have_owners_enabled(pre, old, shared, 5int) by {
                    map_owned_frame(combined.bool_map, frame.bool_map, pre.bool_map, 5int, false);
                    map_owned_frame(combined.bool_map, frame.bool_map, pre.bool_map, 19int, false);
                }
            };
            let tracked owner = X::Protocol::add_have_with_shared(owner, &observer, 5int);
            let (frame, pre, post) = choose|frame: X::Fragment, pre: X::State, post: X::State|
                pre.invariant() && X::Fragment::op(X::Fragment::op(old, shared), frame)
                    == X::Protocol::embed(pre) && X::State::add_have_strong(pre, post, 5int)
                    && post.invariant() && owner.fragment() == X::Protocol::add_have_owned_post(
                    old,
                    pre,
                    post,
                    5int,
                ) && X::Fragment::op(X::Fragment::op(owner.fragment(), shared), frame)
                    == X::Protocol::embed(post);
            Pointwise::extensionality(
                owner.fragment().bool_map,
                map_frag(IMap::empty().insert(5int, true)),
            );
            assert(owner.fragment().bool_map == map_frag(IMap::empty().insert(5int, true)));
            assert(observer.fragment().bool_map == map_frag(IMap::empty().insert(19int, false)));
            let tracked token = owner.join(observer);
            token.validate();
        }
        {
            let tracked (Tracked(instance), Tracked(mut m), Tracked(mut map)) =
                Fancy::Instance::initialize(false);
            let tracked token = instance.do_deposit(true, &mut m, true);
            let tracked guard = instance.do_guard(0, true, &token);
            let tracked token1 = instance.do_deposit(false, &mut m, false);
            assert(*guard);
            let tracked guard1 = instance.do_guard(1, false, &token1);
            assert(!*guard1);
            assert(m.value() == 2);
            assert(token.key() == 0 && token.value());
            assert(token1.key() == 1 && !token1.value());
            map.insert(token);
            map.insert(token1);
            assert(map.map().contains_key(0) && map.map()[0] == true);
            assert(map.map().contains_key(1) && map.map()[1] == false);
            let state = instance.observe(&m, &map);
            assert(state.invariant());
            assert(state.m == 2);
            assert(state.map == IMap::<int, bool>::empty().insert(0, true).insert(1, false)) by {
                assert forall|i: int| state.map.contains_key(i) implies i == 0 || i == 1 by {};
                assert(state.map =~= IMap::<int, bool>::empty().insert(0, true).insert(1, false));
            }
            assert(state.storage_map == state.map);
            let tracked token = map.remove(0);
            let tracked guard = instance.do_guard(0, true, &token);
            assert(*guard);
            map.insert(token);
        }
        assert forall|pre: Fancy::State, value: bool|
            pre.invariant() implies !Fancy::State::do_withdraw_enabled(pre, value) by {
            assert(!pre.storage_map.contains_key(pre.m));
            assert(!pre.map.contains_key(pre.m));
        };
    }
}

} // verus!
