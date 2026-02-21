//! This code adds specifications for the standard-library types
//! `std::collections::BTreeMap` and `std::collections::BTreeSet`.
//!
//! The specification is only meaningful when the `Key` obeys our [`Ord`] model,
//! as specified by [`super::super::laws_cmp::obeys_cmp_spec`].
//!
//! By default, the Verus standard library brings useful axioms
//! about the behavior of `BTreeMap` and `BTreeSet` into the ambient
//! reasoning context by broadcasting the group
//! `vstd::std_specs::btree::group_btree_axioms`.
use super::super::laws_cmp::obeys_cmp_spec;
use super::super::prelude::*;
use super::cmp::OrdSpec;

use alloc::alloc::Allocator;
use core::borrow::Borrow;
use core::marker::PhantomData;
use core::option::Option;
use std::collections::btree_map;
use std::collections::btree_map::{Keys, Values};
use std::collections::btree_set;
use std::collections::{BTreeMap, BTreeSet};

verus! {

/// Whether the `Key` type obeys the cmp spec, required for [`BTreeMap`]
///
/// This is a workaround to the fact that [`BTreeMap`] "late binds" the trait bounds when needed.
/// For instance, [`BTreeMap::iter`] does not require `Key: Ord`, even though it yields ordered
/// items. Rather, it relies on the fact that [`BTreeMap::insert`] does require `Key: Ord`, meaning
/// no instance of a [`BTreeMap`] will ever have keys that cannot be comparable.
///
/// See also [`axiom_key_obeys_cmp_spec_meaning`].
pub uninterp spec fn key_obeys_cmp_spec<Key: ?Sized>() -> bool;

/// For types that are ordered, [`key_obeys_cmp_spec`] is equivalent to [`obeys_cmp_spec`].
pub broadcast axiom fn axiom_key_obeys_cmp_spec_meaning<K: Ord>()
    ensures
        #[trigger] key_obeys_cmp_spec::<K>() <==> obeys_cmp_spec::<K>(),
;

/// Whether a sequence is ordered in increasing order.
/// This only has meaning if `K: Ord` and [`obeys_cmp_spec::<K>`].
///
/// See [`axiom_increasing_seq_meaning`] for an interpretation of this predicate.
pub uninterp spec fn increasing_seq<K>(s: Seq<K>) -> bool;

/// An interpretation for the [`increasing_seq`] predicate.
pub broadcast axiom fn axiom_increasing_seq_meaning<K: Ord>(s: Seq<K>)
    requires
        obeys_cmp_spec::<K>(),
    ensures
        #[trigger] increasing_seq(s) <==> forall|i, j|
            0 <= i < j < s.len() ==> s[i].cmp_spec(&s[j]) is Less,
;

/// Specifications for the behavior of
/// [`std::collections::btree_map::Keys`](https://doc.rust-lang.org/std/collections/btree_map/struct.Keys.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExKeys<'a, Key, Value>(Keys<'a, Key, Value>);

pub trait KeysAdditionalSpecFns<'a, Key, Value> {
    spec fn view(self: &Self) -> (int, Seq<Key>);
}

impl<'a, Key, Value> KeysAdditionalSpecFns<'a, Key, Value> for Keys<'a, Key, Value> {
    uninterp spec fn view(self: &Keys<'a, Key, Value>) -> (int, Seq<Key>);
}

pub assume_specification<'a, Key, Value>[ Keys::<'a, Key, Value>::next ](
    keys: &mut Keys<'a, Key, Value>,
) -> (r: Option<&'a Key>)
    ensures
        ({
            let (old_index, old_seq) = old(keys)@;
            match r {
                None => {
                    &&& keys@ == old(keys)@
                    &&& old_index >= old_seq.len()
                },
                Some(k) => {
                    let (new_index, new_seq) = keys@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& k == old_seq[old_index]
                },
            }
        }),
;

pub struct KeysGhostIterator<'a, Key, Value> {
    pub pos: int,
    pub keys: Seq<Key>,
    pub phantom: Option<&'a Value>,
}

impl<'a, Key, Value> super::super::pervasive::ForLoopGhostIteratorNew for Keys<'a, Key, Value> {
    type GhostIter = KeysGhostIterator<'a, Key, Value>;

    open spec fn ghost_iter(&self) -> KeysGhostIterator<'a, Key, Value> {
        KeysGhostIterator { pos: self@.0, keys: self@.1, phantom: None }
    }
}

impl<'a, Key: 'a, Value: 'a> super::super::pervasive::ForLoopGhostIterator for KeysGhostIterator<
    'a,
    Key,
    Value,
> {
    type ExecIter = Keys<'a, Key, Value>;

    type Item = Key;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Keys<'a, Key, Value>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.keys == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.keys == self.keys
            &&& 0 <= self.pos <= self.keys.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.keys.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.keys.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<Key> {
        if 0 <= self.pos < self.keys.len() {
            Some(self.keys[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Keys<'a, Key, Value>) -> KeysGhostIterator<
        'a,
        Key,
        Value,
    > {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, Key, Value> View for KeysGhostIterator<'a, Key, Value> {
    type V = Seq<Key>;

    open spec fn view(&self) -> Seq<Key> {
        self.keys.take(self.pos)
    }
}

/// Specifications for the behavior of
/// [`std::collections::btree_map::Values`](https://doc.rust-lang.org/std/collections/btree_map/struct.Values.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExValues<'a, Key, Value>(Values<'a, Key, Value>);

pub trait ValuesAdditionalSpecFns<'a, Key, Value> {
    spec fn view(self: &Self) -> (int, Seq<Value>);
}

impl<'a, Key, Value> ValuesAdditionalSpecFns<'a, Key, Value> for Values<'a, Key, Value> {
    uninterp spec fn view(self: &Values<'a, Key, Value>) -> (int, Seq<Value>);
}

pub assume_specification<'a, Key, Value>[ Values::<'a, Key, Value>::next ](
    values: &mut Values<'a, Key, Value>,
) -> (r: Option<&'a Value>)
    ensures
        ({
            let (old_index, old_seq) = old(values)@;
            match r {
                None => {
                    &&& values@ == old(values)@
                    &&& old_index >= old_seq.len()
                },
                Some(v) => {
                    let (new_index, new_seq) = values@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& v == old_seq[old_index]
                },
            }
        }),
;

pub struct ValuesGhostIterator<'a, Key, Value> {
    pub pos: int,
    pub values: Seq<Value>,
    pub phantom: Option<&'a Key>,
}

impl<'a, Key, Value> super::super::pervasive::ForLoopGhostIteratorNew for Values<'a, Key, Value> {
    type GhostIter = ValuesGhostIterator<'a, Key, Value>;

    open spec fn ghost_iter(&self) -> ValuesGhostIterator<'a, Key, Value> {
        ValuesGhostIterator { pos: self@.0, values: self@.1, phantom: None }
    }
}

impl<'a, Key: 'a, Value: 'a> super::super::pervasive::ForLoopGhostIterator for ValuesGhostIterator<
    'a,
    Key,
    Value,
> {
    type ExecIter = Values<'a, Key, Value>;

    type Item = Value;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Values<'a, Key, Value>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.values == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.values == self.values
            &&& 0 <= self.pos <= self.values.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.values.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.values.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<Value> {
        if 0 <= self.pos < self.values.len() {
            Some(self.values[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Values<'a, Key, Value>) -> ValuesGhostIterator<
        'a,
        Key,
        Value,
    > {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, Key, Value> View for ValuesGhostIterator<'a, Key, Value> {
    type V = Seq<Value>;

    open spec fn view(&self) -> Seq<Value> {
        self.values.take(self.pos)
    }
}

// The `iter` method of a `BTreeMap` returns an iterator of type `btree_map::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExMapIter<'a, K, V>(btree_map::Iter<'a, K, V>);

pub trait MapIterAdditionalSpecFns<'a, Key, Value> {
    spec fn view(self: &Self) -> (int, Seq<(Key, Value)>);
}

impl<'a, K: 'a, V: 'a> MapIterAdditionalSpecFns<'a, K, V> for btree_map::Iter<'a, K, V> {
    uninterp spec fn view(self: &btree_map::Iter<'a, K, V>) -> (int, Seq<(K, V)>);
}

pub assume_specification<'a, K: 'a, V: 'a>[ btree_map::Iter::<'a, K, V>::next ](
    iter: &mut btree_map::Iter<'a, K, V>,
) -> (r: Option<(&'a K, &'a V)>)
    ensures
        ({
            let (old_index, old_seq) = old(iter)@;
            match r {
                None => {
                    &&& iter@ == old(iter)@
                    &&& old_index >= old_seq.len()
                },
                Some((k, v)) => {
                    let (new_index, new_seq) = iter@;
                    let (old_k, old_v) = old_seq[old_index];
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& k == old_k
                    &&& v == old_v
                    &&& old_seq.to_set().contains((*k, *v))
                },
            }
        }),
;

pub struct MapIterGhostIterator<'a, Key: 'a, Value: 'a> {
    pub pos: int,
    pub kv_pairs: Seq<(Key, Value)>,
    pub _marker: PhantomData<&'a Key>,
}

impl<'a, Key: 'a, Value: 'a> super::super::pervasive::ForLoopGhostIteratorNew for btree_map::Iter<
    'a,
    Key,
    Value,
> {
    type GhostIter = MapIterGhostIterator<'a, Key, Value>;

    open spec fn ghost_iter(&self) -> MapIterGhostIterator<'a, Key, Value> {
        MapIterGhostIterator { pos: self@.0, kv_pairs: self@.1, _marker: PhantomData }
    }
}

impl<'a, Key: 'a, Value: 'a> super::super::pervasive::ForLoopGhostIterator for MapIterGhostIterator<
    'a,
    Key,
    Value,
> {
    type ExecIter = btree_map::Iter<'a, Key, Value>;

    type Item = (Key, Value);

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &btree_map::Iter<'a, Key, Value>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.kv_pairs == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.kv_pairs == self.kv_pairs
            &&& 0 <= self.pos <= self.kv_pairs.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.kv_pairs.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.kv_pairs.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<(Key, Value)> {
        if 0 <= self.pos < self.kv_pairs.len() {
            Some(self.kv_pairs[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(
        &self,
        _exec_iter: &btree_map::Iter<'a, Key, Value>,
    ) -> MapIterGhostIterator<'a, Key, Value> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, Key, Value> View for MapIterGhostIterator<'a, Key, Value> {
    type V = Seq<(Key, Value)>;

    open spec fn view(&self) -> Seq<(Key, Value)> {
        self.kv_pairs.take(self.pos)
    }
}

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)]` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_btree_map_iter<'a, Key, Value, A: Allocator + Clone>(
    m: &'a BTreeMap<Key, Value, A>,
) -> (r: btree_map::Iter<'a, Key, Value>);

pub broadcast axiom fn axiom_spec_btree_map_iter<'a, Key, Value, A: Allocator + Clone>(
    m: &'a BTreeMap<Key, Value, A>,
)
    ensures
        ({
            let (pos, v) = #[trigger] spec_btree_map_iter(m)@;
            &&& pos == 0int
            &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] m@[v[i].0] == v[i].1
            &&& increasing_seq(v.map(|idx: int, kv: (Key, Value)| kv.0))
        }),
;

#[verifier::when_used_as_spec(spec_btree_map_iter)]
pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::iter ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (iter: btree_map::Iter<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            let (index, s) = iter@;
            &&& index == 0
            &&& s.to_set() == m@.kv_pairs()
            &&& s.no_duplicates()
            &&& increasing_seq(s.map(|idx: int, kv: (Key, Value)| kv.0))
        },
;

/// Specifications for the behavior of [`std::collections::BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html).
///
/// We model a `BTreeMap` as having a view of type `Map<Key, Value>`, which reflects the current state of the map.
///
/// These specifications are only meaningful if `key_obeys_cmp_spec::<Key>()` holds.
/// See [`key_obeys_cmp_spec`] for information on use with primitive types and other types.
///
/// Axioms about the behavior of BTreeMap are present in the broadcast group `vstd::std_specs::btree::group_btree_axioms`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeMap<Key, Value, A: Allocator + Clone>(BTreeMap<Key, Value, A>);

pub trait BTreeMapAdditionalSpecFns<Key, Value>: View<V = Map<Key, Value>> {
    spec fn spec_index(&self, k: Key) -> Value
        recommends
            self@.contains_key(k),
    ;
}

impl<Key, Value, A: Allocator + Clone> BTreeMapAdditionalSpecFns<Key, Value> for BTreeMap<
    Key,
    Value,
    A,
> {
    #[verifier::inline]
    open spec fn spec_index(&self, k: Key) -> Value {
        self@.index(k)
    }
}

impl<Key, Value, A: Allocator + Clone> View for BTreeMap<Key, Value, A> {
    type V = Map<Key, Value>;

    uninterp spec fn view(&self) -> Map<Key, Value>;
}

impl<Key: DeepView, Value: DeepView, A: Allocator + Clone> DeepView for BTreeMap<Key, Value, A> {
    type V = Map<Key::V, Value::V>;

    open spec fn deep_view(&self) -> Map<Key::V, Value::V> {
        btree_map_deep_view_impl(*self)
    }
}

/// The actual definition of `BTreeMap::deep_view`.
///
/// This is a separate function since it introduces a lot of quantifiers and revealing an opaque trait
/// method is not supported. In most cases, it's easier to use one of the lemmas below instead
/// of revealing this function directly.
#[verifier::opaque]
pub open spec fn btree_map_deep_view_impl<Key: DeepView, Value: DeepView, A: Allocator + Clone>(
    m: BTreeMap<Key, Value, A>,
) -> Map<Key::V, Value::V> {
    Map::new(
        |k: Key::V|
            exists|orig_k: Key| #[trigger] m@.contains_key(orig_k) && k == orig_k.deep_view(),
        |dk: Key::V|
            {
                let k = choose|k: Key| m@.contains_key(k) && #[trigger] k.deep_view() == dk;
                m@[k].deep_view()
            },
    )
}

pub broadcast proof fn lemma_btree_map_deepview_dom<K: DeepView, V: DeepView>(m: BTreeMap<K, V>)
    ensures
        #[trigger] m.deep_view().dom() == m@.dom().map(|k: K| k.deep_view()),
{
    reveal(btree_map_deep_view_impl);
    broadcast use group_btree_axioms;
    broadcast use crate::vstd::group_vstd_default;

    assert(m.deep_view().dom() =~= m@.dom().map(|k: K| k.deep_view()));
}

pub broadcast proof fn lemma_btree_map_deepview_properties<K: DeepView, V: DeepView>(
    m: BTreeMap<K, V>,
)
    requires
        crate::relations::injective(|k: K| k.deep_view()),
    ensures
        #![trigger m.deep_view()]
        // all elements in m.view() are present in m.deep_view()
        forall|k: K| #[trigger]
            m@.contains_key(k) ==> m.deep_view().contains_key(k.deep_view())
                && m.deep_view()[k.deep_view()] == m@[k].deep_view(),
        // all elements in m.deep_view() are present in m.view()
        forall|dk: <K as DeepView>::V| #[trigger]
            m.deep_view().contains_key(dk) ==> exists|k: K|
                k.deep_view() == dk && #[trigger] m@.contains_key(k),
{
    reveal(btree_map_deep_view_impl);
    broadcast use group_btree_axioms;
    broadcast use crate::vstd::group_vstd_default;

    assert(m.deep_view().dom() == m@.dom().map(|k: K| k.deep_view()));
    assert forall|k: K| #[trigger] m@.contains_key(k) implies m.deep_view().contains_key(
        k.deep_view(),
    ) && m.deep_view()[k.deep_view()] == m@[k].deep_view() by {
        assert forall|k1: K, k2: K| #[trigger]
            k1.deep_view() == #[trigger] k2.deep_view() implies k1 == k2 by {
            let ghost k_deepview = |k: K| k.deep_view();
            assert(crate::relations::injective(k_deepview));
            assert(k_deepview(k1) == k_deepview(k2));
        }
    }
}

pub broadcast proof fn lemma_btree_map_deepview_values<K: DeepView, V: DeepView>(m: BTreeMap<K, V>)
    requires
        crate::relations::injective(|k: K| k.deep_view()),
    ensures
        #[trigger] m.deep_view().values() =~= m@.values().map(|v: V| v.deep_view()),
{
    reveal(btree_map_deep_view_impl);
    broadcast use group_btree_axioms;
    broadcast use lemma_btree_map_deepview_properties;
    broadcast use crate::vstd::group_vstd_default;

    let lhs = m.deep_view().values();
    let rhs = m@.values().map(|v: V| v.deep_view());
    assert forall|v: V::V| #[trigger] lhs.contains(v) implies rhs.contains(v) by {
        let dk = choose|dk: K::V| #[trigger]
            m.deep_view().contains_key(dk) && m.deep_view()[dk] == v;
        let k = choose|k: K| #[trigger] m@.contains_key(k) && k.deep_view() == dk;
        let ov = choose|ov: V| #[trigger] m@.contains_key(k) && m@[k] == ov && ov.deep_view() == v;
        assert(v == ov.deep_view());
        assert(m@.values().contains(ov));
    }
}

/// Borrowing a key works the same way on deep_view as on view,
/// if deep_view is injective; see `axiom_contains_deref_key`.
pub broadcast axiom fn axiom_btree_map_deepview_borrow<
    K: DeepView + Borrow<Q>,
    V: DeepView,
    Q: View<V = <K as DeepView>::V> + Eq + ?Sized,
>(m: BTreeMap<K, V>, k: &Q)
    requires
        key_obeys_cmp_spec::<K>(),
        crate::relations::injective(|k: K| k.deep_view()),
    ensures
        #[trigger] contains_borrowed_key(m@, k) <==> m.deep_view().contains_key(k@),
;

/// A `Map` constructed from a `BTreeMap` is always finite.
pub broadcast axiom fn axiom_btree_map_view_finite_dom<K, V>(m: BTreeMap<K, V>)
    ensures
        #[trigger] m@.dom().finite(),
;

pub uninterp spec fn spec_btree_map_len<Key, Value, A: Allocator + Clone>(
    m: &BTreeMap<Key, Value, A>,
) -> usize;

pub broadcast axiom fn axiom_spec_btree_map_len<Key, Value, A: Allocator + Clone>(
    m: &BTreeMap<Key, Value, A>,
)
    ensures
        key_obeys_cmp_spec::<Key>() ==> #[trigger] spec_btree_map_len(m) == m@.len(),
;

#[verifier::when_used_as_spec(spec_btree_map_len)]
pub assume_specification<Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::len ](
    m: &BTreeMap<Key, Value, A>,
) -> (len: usize)
    ensures
        len == spec_btree_map_len(m),
;

pub assume_specification<Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::is_empty ](
    m: &BTreeMap<Key, Value, A>,
) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<K: Clone, V: Clone, A: Allocator + Clone>[ <BTreeMap::<
    K,
    V,
    A,
> as Clone>::clone ](this: &BTreeMap<K, V, A>) -> (other: BTreeMap<K, V, A>)
    ensures
        other@ == this@,
;

pub assume_specification<Key, Value>[ BTreeMap::<Key, Value>::new ]() -> (m: BTreeMap<Key, Value>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<K, V>[ <BTreeMap<K, V> as core::default::Default>::default ]() -> (m:
    BTreeMap<K, V>)
    ensures
        m@ == Map::<K, V>::empty(),
;

pub assume_specification<Key: Ord, Value, A: Allocator + Clone>[ BTreeMap::<
    Key,
    Value,
    A,
>::insert ](m: &mut BTreeMap<Key, Value, A>, k: Key, v: Value) -> (result: Option<Value>)
    ensures
        obeys_cmp_spec::<Key>() ==> {
            &&& m@ == old(m)@.insert(k, v)
            &&& match result {
                Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
                None => !old(m)@.contains_key(k),
            }
        },
;

// The specification for `contains_key` has a parameter `key: &Q`
// where you'd expect to find `key: &Key`. This allows for the case
// that `Key` can be borrowed as something other than `&Key`. For
// instance, `Box<u32>` can be borrowed as `&u32` and `String` can be
// borrowed as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively.
// To deal with this, we have a specification function that opaquely
// specifies what it means for a map to contain a borrowed key of type
// `&Q`. And the postcondition of `contains_key` just says that its
// result matches the output of that specification function. But this
// isn't very helpful by itself, since there's no body to that
// specification function. So we have special-case axioms that say
// what this means in two important circumstances: (1) `Key = Q` and
// (2) `Key = Box<Q>`.
pub uninterp spec fn contains_borrowed_key<Key, Value, Q: ?Sized>(
    m: Map<Key, Value>,
    k: &Q,
) -> bool;

pub broadcast axiom fn axiom_contains_deref_key<Q, Value>(m: Map<Q, Value>, k: &Q)
    ensures
        #[trigger] contains_borrowed_key::<Q, Value, Q>(m, k) <==> m.contains_key(*k),
;

pub broadcast axiom fn axiom_contains_box<Q, Value>(m: Map<Box<Q>, Value>, k: &Q)
    ensures
        #[trigger] contains_borrowed_key::<Box<Q>, Value, Q>(m, k) <==> m.contains_key(
            Box::new(*k),
        ),
;

pub assume_specification<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::contains_key::<Q> ](m: &BTreeMap<Key, Value, A>, k: &Q) -> (result:
    bool)
    ensures
        obeys_cmp_spec::<Key>() ==> result == contains_borrowed_key(m@, k),
;

// The specification for `get` has a parameter `key: &Q` where you'd
// expect to find `key: &Key`. This allows for the case that `Key` can
// be borrowed as something other than `&Key`. For instance,
// `Box<u32>` can be borrowed as `&u32` and `String` can be borrowed
// as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively.
// To deal with this, we have a specification function that opaquely
// specifies what it means for a map to map a borrowed key of type
// `&Q` to a certain value. And the postcondition of `get` says that
// its result matches the output of that specification function. (It
// also says that its result corresponds to the output of
// `contains_borrowed_key`, discussed above.) But this isn't very
// helpful by itself, since there's no body to that specification
// function. So we have special-case axioms that say what this means
// in two important circumstances: (1) `Key = Q` and (2) `Key =
// Box<Q>`.
pub uninterp spec fn maps_borrowed_key_to_value<Key, Value, Q: ?Sized>(
    m: Map<Key, Value>,
    k: &Q,
    v: Value,
) -> bool;

pub broadcast axiom fn axiom_maps_deref_key_to_value<Q, Value>(m: Map<Q, Value>, k: &Q, v: Value)
    ensures
        #[trigger] maps_borrowed_key_to_value::<Q, Value, Q>(m, k, v) <==> m.contains_key(*k)
            && m[*k] == v,
;

pub broadcast axiom fn axiom_maps_box_key_to_value<Q, Value>(m: Map<Box<Q>, Value>, q: &Q, v: Value)
    ensures
        #[trigger] maps_borrowed_key_to_value::<Box<Q>, Value, Q>(m, q, v) <==> {
            let k = Box::new(*q);
            &&& m.contains_key(k)
            &&& m[k] == v
        },
;

pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::get::<Q> ](m: &'a BTreeMap<Key, Value, A>, k: &Q) -> (result: Option<
    &'a Value,
>)
    ensures
        obeys_cmp_spec::<Key>() ==> match result {
            Some(v) => maps_borrowed_key_to_value(m@, k, *v),
            None => !contains_borrowed_key(m@, k),
        },
;

// The specification for `remove` has a parameter `key: &Q` where
// you'd expect to find `key: &Key`. This allows for the case that
// `Key` can be borrowed as something other than `&Key`. For instance,
// `Box<u32>` can be borrowed as `&u32` and `String` can be borrowed
// as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively. To deal with this, we have a specification function
// that opaquely specifies what it means for two maps to be related by
// a remove of a certain `&Q`. And the postcondition of `remove` says
// that `old(self)@` and `self@` satisfy that relationship. (It also
// says that its result corresponds to the output of
// `contains_borrowed_key` and `maps_borrowed_key_to_value`, discussed
// above.) But this isn't very helpful by itself, since there's no
// body to that specification function. So we have special-case axioms
// that say what this means in two important circumstances: (1) `Key =
// Q` and (2) `Key = Box<Q>`.
pub uninterp spec fn borrowed_key_removed<Key, Value, Q: ?Sized>(
    old_m: Map<Key, Value>,
    new_m: Map<Key, Value>,
    k: &Q,
) -> bool;

pub broadcast axiom fn axiom_deref_key_removed<Q, Value>(
    old_m: Map<Q, Value>,
    new_m: Map<Q, Value>,
    k: &Q,
)
    ensures
        #[trigger] borrowed_key_removed::<Q, Value, Q>(old_m, new_m, k) <==> new_m == old_m.remove(
            *k,
        ),
;

pub broadcast axiom fn axiom_box_key_removed<Q, Value>(
    old_m: Map<Box<Q>, Value>,
    new_m: Map<Box<Q>, Value>,
    q: &Q,
)
    ensures
        #[trigger] borrowed_key_removed::<Box<Q>, Value, Q>(old_m, new_m, q) <==> new_m
            == old_m.remove(Box::new(*q)),
;

pub assume_specification<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::remove::<Q> ](m: &mut BTreeMap<Key, Value, A>, k: &Q) -> (result:
    Option<Value>)
    ensures
        obeys_cmp_spec::<Key>() ==> {
            &&& borrowed_key_removed(old(m)@, m@, k)
            &&& match result {
                Some(v) => maps_borrowed_key_to_value(old(m)@, k, v),
                None => !contains_borrowed_key(old(m)@, k),
            }
        },
;

pub assume_specification<Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::clear ](
    m: &mut BTreeMap<Key, Value, A>,
)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::keys ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (keys: Keys<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            let (index, s) = keys@;
            &&& index == 0
            &&& s.to_set() == m@.dom()
            &&& s.no_duplicates()
            &&& increasing_seq(s)
        },
;

pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::values ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (values: Values<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            let (index, s) = values@;
            &&& index == 0
            &&& s.to_set() == m@.values()
            &&& exists|key_seq: Seq<Key>|
                {
                    &&& increasing_seq(key_seq)
                    &&& key_seq.to_set() == m@.dom()
                    &&& key_seq.no_duplicates()
                    &&& s == key_seq.map(|i: int, k| m@[k])
                }
        },
;

pub broadcast axiom fn axiom_btree_map_decreases<Key, Value, A: Allocator + Clone>(
    m: BTreeMap<Key, Value, A>,
)
    ensures
        #[trigger] (decreases_to!(m => m@)),
;

// The `iter` method of a `BTreeSet` returns an iterator of type `btree_set::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub struct ExSetIter<'a, K: 'a>(btree_set::Iter<'a, K>);

pub trait SetIterAdditionalSpecFns<'a, Key> {
    spec fn view(self: &Self) -> (int, Seq<Key>);
}

impl<'a, Key> SetIterAdditionalSpecFns<'a, Key> for btree_set::Iter<'a, Key> {
    uninterp spec fn view(self: &btree_set::Iter<'a, Key>) -> (int, Seq<Key>);
}

pub assume_specification<'a, Key>[ btree_set::Iter::<'a, Key>::next ](
    elements: &mut btree_set::Iter<'a, Key>,
) -> (r: Option<&'a Key>)
    ensures
        ({
            let (old_index, old_seq) = old(elements)@;
            match r {
                None => {
                    &&& elements@ == old(elements)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = elements@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& element == old_seq[old_index]
                },
            }
        }),
;

pub struct SetIterGhostIterator<'a, Key> {
    pub pos: int,
    pub elements: Seq<Key>,
    pub phantom: Option<&'a Key>,
}

impl<'a, Key> super::super::pervasive::ForLoopGhostIteratorNew for btree_set::Iter<'a, Key> {
    type GhostIter = SetIterGhostIterator<'a, Key>;

    open spec fn ghost_iter(&self) -> SetIterGhostIterator<'a, Key> {
        SetIterGhostIterator { pos: self@.0, elements: self@.1, phantom: None }
    }
}

impl<'a, Key> super::super::pervasive::ForLoopGhostIterator for SetIterGhostIterator<'a, Key> {
    type ExecIter = btree_set::Iter<'a, Key>;

    type Item = Key;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &btree_set::Iter<'a, Key>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.elements == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.elements == self.elements
            &&& 0 <= self.pos <= self.elements.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.elements.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.elements.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<Key> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(
        &self,
        _exec_iter: &btree_set::Iter<'a, Key>,
    ) -> SetIterGhostIterator<'a, Key> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, Key> View for SetIterGhostIterator<'a, Key> {
    type V = Seq<Key>;

    open spec fn view(&self) -> Seq<Key> {
        self.elements.take(self.pos)
    }
}

/// Specifications for the behavior of [`std::collections::BTreeSet`](https://doc.rust-lang.org/std/collections/struct.BTreeSet.html).
///
/// We model a `BTreeSet` as having a view of type `Set<Key>`, which reflects the current state of the set.
///
/// These specifications are only meaningful if `obeys_cmp_spec::<Key>()` hold.
/// See [`obeys_cmp_spec`] for information on use with primitive types and custom types.
///
/// Axioms about the behavior of BTreeSet are present in the broadcast group `vstd::std_specs::btree::group_btree_axioms`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeSet<Key, A: Allocator + Clone>(BTreeSet<Key, A>);

impl<Key, A: Allocator + Clone> View for BTreeSet<Key, A> {
    type V = Set<Key>;

    uninterp spec fn view(&self) -> Set<Key>;
}

impl<Key: DeepView, A: Allocator + Clone> DeepView for BTreeSet<Key, A> {
    type V = Set<Key::V>;

    open spec fn deep_view(&self) -> Set<Key::V> {
        self@.map(|x: Key| x.deep_view())
    }
}

pub uninterp spec fn spec_btree_set_len<Key, A: Allocator + Clone>(m: &BTreeSet<Key, A>) -> usize;

pub broadcast axiom fn axiom_spec_btree_set_len<Key, A: Allocator + Clone>(m: &BTreeSet<Key, A>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> #[trigger] spec_btree_set_len(m) == m@.len(),
;

#[verifier::when_used_as_spec(spec_btree_set_len)]
pub assume_specification<Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::len ](
    m: &BTreeSet<Key, A>,
) -> (len: usize)
    ensures
        len == spec_btree_set_len(m),
;

pub assume_specification<Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::is_empty ](
    m: &BTreeSet<Key, A>,
) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<K: Clone, A: Allocator + Clone>[ <BTreeSet::<K, A> as Clone>::clone ](
    this: &BTreeSet<K, A>,
) -> (other: BTreeSet<K, A>)
    ensures
        other@ == this@,
;

pub assume_specification<Key>[ BTreeSet::<Key>::new ]() -> (m: BTreeSet<Key>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<T>[ <BTreeSet<T> as core::default::Default>::default ]() -> (m: BTreeSet<
    T,
>)
    ensures
        m@ == Set::<T>::empty(),
;

pub assume_specification<Key: Ord, A: Allocator + Clone>[ BTreeSet::<Key, A>::insert ](
    m: &mut BTreeSet<Key, A>,
    k: Key,
) -> (result: bool)
    ensures
        obeys_cmp_spec::<Key>() ==> {
            &&& m@ == old(m)@.insert(k)
            &&& result == !old(m)@.contains(k)
        },
;

// The specification for `contains` has a parameter `key: &Q`
// where you'd expect to find `key: &Key`. This allows for the case
// that `Key` can be borrowed as something other than `&Key`. For
// instance, `Box<u32>` can be borrowed as `&u32` and `String` can be
// borrowed as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively.
// To deal with this, we have a specification function that opaquely
// specifies what it means for a set to contain a borrowed key of type
// `&Q`. And the postcondition of `contains` just says that its
// result matches the output of that specification function. But this
// isn't very helpful by itself, since there's no body to that
// specification function. So we have special-case axioms that say
// what this means in two important circumstances: (1) `Key = Q` and
// (2) `Key = Box<Q>`.
pub uninterp spec fn set_contains_borrowed_key<Key, Q: ?Sized>(m: Set<Key>, k: &Q) -> bool;

pub broadcast axiom fn axiom_set_contains_deref_key<Q>(m: Set<Q>, k: &Q)
    ensures
        #[trigger] set_contains_borrowed_key::<Q, Q>(m, k) <==> m.contains(*k),
;

pub broadcast axiom fn axiom_set_contains_box<Q>(m: Set<Box<Q>>, k: &Q)
    ensures
        #[trigger] set_contains_borrowed_key::<Box<Q>, Q>(m, k) <==> m.contains(Box::new(*k)),
;

pub assume_specification<Key: Borrow<Q> + Ord, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<
    Key,
    A,
>::contains ](m: &BTreeSet<Key, A>, k: &Q) -> (result: bool)
    ensures
        obeys_cmp_spec::<Key>() ==> result == set_contains_borrowed_key(m@, k),
;

// The specification for `get` has a parameter `key: &Q` where you'd
// expect to find `key: &Key`. This allows for the case that `Key` can
// be borrowed as something other than `&Key`. For instance,
// `Box<u32>` can be borrowed as `&u32` and `String` can be borrowed
// as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively.
// To deal with this, we have a specification function that opaquely
// specifies what it means for a returned reference to point to an
// element of a BTreeSet. And the postcondition of `get` says that
// its result matches the output of that specification function. (It
// also says that its result corresponds to the output of
// `contains_borrowed_key`, discussed above.) But this isn't very
// helpful by itself, since there's no body to that specification
// function. So we have special-case axioms that say what this means
// in two important circumstances: (1) `Key = Q` and (2) `Key =
// Box<Q>`.
pub uninterp spec fn sets_borrowed_key_to_key<Key, Q: ?Sized>(m: Set<Key>, k: &Q, v: &Key) -> bool;

pub broadcast axiom fn axiom_set_deref_key_to_value<Q>(m: Set<Q>, k: &Q, v: &Q)
    ensures
        #[trigger] sets_borrowed_key_to_key::<Q, Q>(m, k, v) <==> m.contains(*k) && k == v,
;

pub broadcast axiom fn axiom_set_box_key_to_value<Q>(m: Set<Box<Q>>, q: &Q, v: &Box<Q>)
    ensures
        #[trigger] sets_borrowed_key_to_key::<Box<Q>, Q>(m, q, v) <==> (m.contains(*v) && Box::new(
            *q,
        ) == v),
;

pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeSet::<Key, A>::get::<Q> ](m: &'a BTreeSet<Key, A>, k: &Q) -> (result: Option<&'a Key>)
    ensures
        obeys_cmp_spec::<Key>() ==> match result {
            Some(v) => sets_borrowed_key_to_key(m@, k, v),
            None => !set_contains_borrowed_key(m@, k),
        },
;

// The specification for `remove` has a parameter `key: &Q` where
// you'd expect to find `key: &Key`. This allows for the case that
// `Key` can be borrowed as something other than `&Key`. For instance,
// `Box<u32>` can be borrowed as `&u32` and `String` can be borrowed
// as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively. To deal with this, we have a specification function
// that opaquely specifies what it means for two sets to be related by
// a remove of a certain `&Q`. And the postcondition of `remove` says
// that `old(self)@` and `self@` satisfy that relationship. (It also
// says that its result corresponds to the output of
// `set_contains_borrowed_key`, discussed above.) But this isn't very
// helpful by itself, since there's no body to that specification
// function. So we have special-case axioms that say what this means
// in two important circumstances: (1) `Key = Q` and (2) `Key = Box<Q>`.
pub uninterp spec fn sets_differ_by_borrowed_key<Key, Q: ?Sized>(
    old_m: Set<Key>,
    new_m: Set<Key>,
    k: &Q,
) -> bool;

pub broadcast axiom fn axiom_set_deref_key_removed<Q>(old_m: Set<Q>, new_m: Set<Q>, k: &Q)
    ensures
        #[trigger] sets_differ_by_borrowed_key::<Q, Q>(old_m, new_m, k) <==> new_m == old_m.remove(
            *k,
        ),
;

pub broadcast axiom fn axiom_set_box_key_removed<Q>(old_m: Set<Box<Q>>, new_m: Set<Box<Q>>, q: &Q)
    ensures
        #[trigger] sets_differ_by_borrowed_key::<Box<Q>, Q>(old_m, new_m, q) <==> new_m
            == old_m.remove(Box::new(*q)),
;

pub assume_specification<Key: Borrow<Q> + Ord, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<
    Key,
    A,
>::remove::<Q> ](m: &mut BTreeSet<Key, A>, k: &Q) -> (result: bool)
    ensures
        obeys_cmp_spec::<Key>() ==> {
            &&& sets_differ_by_borrowed_key(old(m)@, m@, k)
            &&& result == set_contains_borrowed_key(old(m)@, k)
        },
;

pub assume_specification<Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::clear ](
    m: &mut BTreeSet<Key, A>,
) where A: Clone
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<'a, Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::iter ](
    m: &'a BTreeSet<Key, A>,
) -> (r: btree_set::Iter<'a, Key>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            let (index, s) = r@;
            &&& index == 0
            &&& s.to_set() == m@
            &&& s.no_duplicates()
            &&& increasing_seq(s)
        },
;

pub broadcast axiom fn axiom_btree_set_decreases<Key, A: Allocator + Clone>(m: BTreeSet<Key, A>)
    ensures
        #[trigger] (decreases_to!(m => m@)),
;

pub broadcast group group_btree_axioms {
    axiom_key_obeys_cmp_spec_meaning,
    axiom_increasing_seq_meaning,
    axiom_box_key_removed,
    axiom_contains_deref_key,
    axiom_contains_box,
    axiom_deref_key_removed,
    axiom_maps_deref_key_to_value,
    axiom_maps_box_key_to_value,
    axiom_btree_map_deepview_borrow,
    axiom_btree_map_view_finite_dom,
    axiom_spec_btree_map_len,
    axiom_set_box_key_removed,
    axiom_set_contains_deref_key,
    axiom_set_contains_box,
    axiom_set_deref_key_removed,
    axiom_set_deref_key_to_value,
    axiom_set_box_key_to_value,
    axiom_spec_btree_set_len,
    axiom_spec_btree_map_iter,
    axiom_btree_map_decreases,
    axiom_btree_set_decreases,
}

} // verus!
