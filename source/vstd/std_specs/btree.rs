//! This code adds specifications for the standard-library types
//! `alloc::collections::BTreeMap` and `alloc::collections::BTreeSet`.
//!
//! The specification is only meaningful when the `Key` obeys our [`Ord`] model,
//! as specified by [`super::super::laws_cmp::obeys_cmp_spec`].
//! Borrowed-query comparison guarantees additionally require
//! `<Q as OrdSpec>::obeys_cmp_spec()` and
//! `<Key as BorrowSpec<Q>>::obeys_borrow_spec()`.
//!
//! By default, the Verus standard library brings useful axioms
//! about the behavior of `BTreeMap` and `BTreeSet` into the ambient
//! reasoning context by broadcasting the group
//! `vstd::std_specs::btree::group_btree_axioms`.
use super::super::laws_cmp::obeys_cmp;
use super::super::map::{assert_maps_equal, assert_maps_equal_internal};
use super::super::prelude::*;
use super::borrow::BorrowSpec;
use super::cmp::{OrdSpec, cmp_matches_deep_equality, cmp_matches_equality};
use super::iter::IteratorSpec;

use alloc::alloc::Allocator;
use alloc::boxed::Box;
use alloc::collections::btree_map;
use alloc::collections::btree_map::{CursorMut, Keys, UnorderedKeyError, Values};
use alloc::collections::btree_set;
use alloc::collections::{BTreeMap, BTreeSet};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::Bound;
use core::option::Option;

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

/// For types that are ordered, [`key_obeys_cmp_spec`] is equivalent to [`obeys_cmp`].
pub broadcast axiom fn axiom_key_obeys_cmp_spec_meaning<K: Ord>()
    ensures
        #[trigger] key_obeys_cmp_spec::<K>() <==> obeys_cmp::<K>(),
;

/// Whether a sequence is ordered in increasing order.
/// This only has meaning if `K: Ord` and [`obeys_cmp::<K>`].
///
/// See [`axiom_increasing_seq_meaning`] for an interpretation of this predicate.
pub uninterp spec fn increasing_seq<K>(s: Seq<K>) -> bool;

/// An interpretation for the [`increasing_seq`] predicate.
pub broadcast axiom fn axiom_increasing_seq_meaning<K: Ord>(s: Seq<K>)
    requires
        obeys_cmp::<K>(),
    ensures
        #[trigger] increasing_seq(s) <==> forall|i, j|
            0 <= i < j < s.len() ==> s[i].cmp_spec(&s[j]) is Less,
;

/// Specifications for the behavior of
/// [`alloc::collections::btree_map::Keys`](https://doc.rust-lang.org/alloc/collections/btree_map/struct.Keys.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExKeys<'a, Key, Value>(Keys<'a, Key, Value>);

// To allow reasoning about the "contents" of the Keys iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original keys.
pub uninterp spec fn into_iter_keys<'a, Key, Value>(i: Keys<'a, Key, Value>) -> Seq<Key>;

impl<'a, K, V> super::iter::IteratorSpecImpl for Keys<'a, K, V> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_keys(*self).len() {
            Some(&into_iter_keys(*self)[index])
        } else {
            None
        }
    }
}

/// Specifications for the behavior of
/// [`alloc::collections::btree_map::Values`](https://doc.rust-lang.org/alloc/collections/btree_map/struct.Values.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExValues<'a, Key, Value>(Values<'a, Key, Value>);

// To allow reasoning about the "contents" of the Values iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original values.
pub uninterp spec fn into_iter_values<'a, Key, Value>(i: Values<'a, Key, Value>) -> Seq<Value>;

impl<'a, K, V> super::iter::IteratorSpecImpl for Values<'a, K, V> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_values(*self).len() {
            Some(&into_iter_values(*self)[index])
        } else {
            None
        }
    }
}

// The `iter` method of a `BTreeMap` returns an iterator of type `btree_map::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExMapIter<'a, K, V>(btree_map::Iter<'a, K, V>);

// To allow reasoning about the "contents" of the Iter iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original map.
pub uninterp spec fn into_iter<'a, Key, Value>(i: btree_map::Iter<'a, Key, Value>) -> Seq<
    (Key, Value),
>;

impl<'a, K, V> super::iter::IteratorSpecImpl for btree_map::Iter<'a, K, V> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter(*self).len() {
            let (k, v) = into_iter(*self)[index];
            Some((&k, &v))
        } else {
            None
        }
    }
}

pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::iter ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (iter: btree_map::Iter<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            &&& IteratorSpec::remaining(&iter).len() == m@.dom().len()
            &&& forall|i: int|
                #![trigger m@.contains_key(*IteratorSpec::remaining(&iter)[i].0)]
                #![trigger m@[*IteratorSpec::remaining(&iter)[i].0]]
                0 <= i < IteratorSpec::remaining(&iter).len() ==> m@.contains_key(
                    *IteratorSpec::remaining(&iter)[i].0,
                ) && m@[*IteratorSpec::remaining(&iter)[i].0] == *IteratorSpec::remaining(
                    &iter,
                )[i].1
            &&& forall|k: Key| #[trigger]
                m@.contains_key(k) ==> IteratorSpec::remaining(&iter).contains((&k, &m@[k]))
            &&& IteratorSpec::remaining(&iter).unref().to_set() == m@.kv_pairs()
            &&& iter.remaining().no_duplicates()
            &&& into_iter(iter) == IteratorSpec::remaining(&iter).unref()
            &&& IteratorSpec::decrease(&iter) is Some
            &&& increasing_seq(iter.remaining().map_values(|kv: (&Key, &Value)| *kv.0))
        },
;

/// Specifications for the behavior of [`alloc::collections::BTreeMap`](https://doc.rust-lang.org/alloc/collections/struct.BTreeMap.html).
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

/// Verus declaration for Rust's mutable B-tree cursor type.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
#[verifier::reject_recursive_types(A)]
pub struct ExCursorMut<'a, Key: 'a, Value: 'a, A>(CursorMut<'a, Key, Value, A>);

/// Verus declaration for the error returned when a cursor insertion would break key ordering.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUnorderedKeyError(UnorderedKeyError);

/// The abstract state of a mutable B-tree cursor.
///
/// A cursor points at the gap immediately before `keys[position]`. Therefore, `peek_next`
/// accesses `keys[position]`, while `peek_prev` accesses `keys[position - 1]`.
pub ghost struct CursorMutModel<Key, Value> {
    /// All keys in the underlying map, in strictly increasing order.
    pub keys: Seq<Key>,
    /// The index of the element immediately after the cursor.
    pub position: int,
    /// The current contents of the complete map borrowed by the cursor.
    pub map: Map<Key, Value>,
}

impl<Key, Value> CursorMutModel<Key, Value> {
    /// Whether this model consistently represents an ordered map and a gap in that map.
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.position <= self.keys.len()
        &&& self.keys.no_duplicates()
        &&& self.keys.to_set() == self.map.dom()
        &&& increasing_seq(self.keys)
    }
}

/// Abstract and prophetic state for mutable B-tree cursors.
pub trait CursorMutSpecFns<Key, Value>: View<V = CursorMutModel<Key, Value>> + Sized {
    /// The contents of the borrowed map when this cursor's borrow is resolved.
    #[verifier::prophetic]
    spec fn final_map(self) -> Map<Key, Value>;
}

impl<'a, Key, Value, A> View for CursorMut<'a, Key, Value, A> {
    type V = CursorMutModel<Key, Value>;

    uninterp spec fn view(&self) -> CursorMutModel<Key, Value>;
}

impl<'a, Key, Value, A> CursorMutSpecFns<Key, Value> for CursorMut<'a, Key, Value, A> {
    #[verifier::prophetic]
    uninterp spec fn final_map(self) -> Map<Key, Value>;
}

/// Whether a borrowed key type's ordering agrees with the ordering of stored keys.
///
/// This is the semantic requirement imposed on `Key: Borrow<Q>` by the standard library's
/// borrowed-key `BTreeMap` operations.
pub open spec fn borrowed_key_ordering_matches<Key: Borrow<Q> + Ord, Q: Ord + ?Sized>() -> bool {
    forall|k1: Key, k2: Key| #[trigger]
        k1.cmp_spec(&k2) == <Key as BorrowSpec<Q>>::spec_borrow(&k1).cmp_spec(
            <Key as BorrowSpec<Q>>::spec_borrow(&k2),
        )
}

/// Whether a key occurs before the gap returned by [`BTreeMap::lower_bound_mut`].
pub open spec fn before_lower_bound<Key: Borrow<Q>, Q: Ord + ?Sized>(
    key: Key,
    bound: Bound<&Q>,
) -> bool {
    let borrowed_key = <Key as BorrowSpec<Q>>::spec_borrow(&key);
    match bound {
        Bound::Included(bound_key) => borrowed_key.cmp_spec(bound_key) is Less,
        Bound::Excluded(bound_key) => !(borrowed_key.cmp_spec(bound_key) is Greater),
        Bound::Unbounded => false,
    }
}

/// Whether a key occurs before the gap returned by [`BTreeMap::upper_bound_mut`].
pub open spec fn before_upper_bound<Key: Borrow<Q>, Q: Ord + ?Sized>(
    key: Key,
    bound: Bound<&Q>,
) -> bool {
    let borrowed_key = <Key as BorrowSpec<Q>>::spec_borrow(&key);
    match bound {
        Bound::Included(bound_key) => !(borrowed_key.cmp_spec(bound_key) is Greater),
        Bound::Excluded(bound_key) => borrowed_key.cmp_spec(bound_key) is Less,
        Bound::Unbounded => true,
    }
}

/// Whether a cursor is at the gap selected by [`BTreeMap::lower_bound_mut`].
pub open spec fn positioned_at_lower_bound<Key: Borrow<Q>, Value, Q: Ord + ?Sized>(
    model: CursorMutModel<Key, Value>,
    bound: Bound<&Q>,
) -> bool {
    &&& forall|i: int|
        #![trigger before_lower_bound(model.keys[i], bound)]
        0 <= i < model.position ==> before_lower_bound(model.keys[i], bound)
    &&& forall|i: int|
        #![trigger before_lower_bound(model.keys[i], bound)]
        model.position <= i < model.keys.len() ==> !before_lower_bound(model.keys[i], bound)
}

/// Whether a cursor is at the gap selected by [`BTreeMap::upper_bound_mut`].
pub open spec fn positioned_at_upper_bound<Key: Borrow<Q>, Value, Q: Ord + ?Sized>(
    model: CursorMutModel<Key, Value>,
    bound: Bound<&Q>,
) -> bool {
    &&& forall|i: int|
        #![trigger before_upper_bound(model.keys[i], bound)]
        0 <= i < model.position ==> before_upper_bound(model.keys[i], bound)
    &&& forall|i: int|
        #![trigger before_upper_bound(model.keys[i], bound)]
        model.position <= i < model.keys.len() ==> !before_upper_bound(model.keys[i], bound)
}

/// Whether a key can be inserted at the cursor's current gap without breaking key order.
pub open spec fn key_fits_at_position<Key: Ord, Value>(
    model: CursorMutModel<Key, Value>,
    key: Key,
) -> bool {
    &&& (model.position == 0 || model.keys[model.position - 1].cmp_spec(&key) is Less)
    &&& (model.position == model.keys.len() || key.cmp_spec(&model.keys[model.position]) is Less)
}

/// Once the cursor has been dropped, its prophesied map is its current map.
pub broadcast axiom fn axiom_has_resolved_cursor<Key, Value, A>(cursor: CursorMut<Key, Value, A>)
    ensures
        #[trigger] has_resolved(cursor) ==> cursor.final_map() == cursor@.map,
;

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
        m@.dom().map(|k: Key| k.deep_view()),
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

pub open spec fn btree_map_keys_differ<Key: Ord, Value, A: Allocator + Clone>(
    m: &BTreeMap<Key, Value, A>,
) -> bool {
    forall|k1: Key, k2: Key|
        {
            &&& #[trigger] m@.contains_key(k1)
            &&& #[trigger] m@.contains_key(k2)
            &&& k1 != k2
        } ==> !(k1.cmp_spec(&k2) is Equal)
}

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

pub open spec fn btree_map_insert_ensures<Key: Ord, Value, A: Allocator + Clone>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
) -> bool {
    obeys_cmp::<Key>() ==> {
        &&& btree_map_keys_differ(old_m)
        &&& btree_map_keys_differ(final_m)
        &&& match result {
            Some(old_value) => exists|stored_key: Key|
                {
                    &&& #[trigger] old_m@.contains_key(stored_key)
                    &&& k.cmp_spec(&stored_key) is Equal
                    &&& old_value == old_m@[stored_key]
                    &&& final_m@ == old_m@.insert(stored_key, v)
                },
            None => {
                &&& forall|stored_key: Key| #[trigger]
                    old_m@.contains_key(stored_key) ==> !(k.cmp_spec(&stored_key) is Equal)
                &&& final_m@ == old_m@.insert(k, v)
            },
        }
    }
}

pub assume_specification<Key: Ord, Value, A: Allocator + Clone>[ BTreeMap::<
    Key,
    Value,
    A,
>::insert ](m: &mut BTreeMap<Key, Value, A>, k: Key, v: Value) -> (result: Option<Value>)
    ensures
        btree_map_insert_ensures(old(m), final(m), k, v, result),
;

pub broadcast proof fn lemma_btree_map_insert_ensures_if_cmp_matches_equality<
    Key: Ord,
    Value,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_map_insert_ensures::<Key, Value, A>(old_m, final_m, k, v, result),
    ensures
        final_m@ == old_m@.insert(k, v),
        match result {
            Some(old_value) => old_m@.contains_key(k) && old_value == old_m[k],
            None => !old_m@.contains_key(k),
        },
{
}

pub broadcast proof fn lemma_btree_map_insert_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    Value: DeepView,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_map_insert_ensures::<Key, Value, A>(old_m, final_m, k, v, result),
    ensures
        final_m.deep_view() == old_m.deep_view().insert(k.deep_view(), v.deep_view()),
        match result {
            Some(old_value) => {
                &&& old_m.deep_view().contains_key(k.deep_view())
                &&& old_value.deep_view() == old_m.deep_view()[k.deep_view()]
            },
            None => !old_m.deep_view().contains_key(k.deep_view()),
        },
{
    broadcast use {
        crate::map::group_map_lemmas,
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
    };

    reveal(btree_map_deep_view_impl);

    let stored_key = match result {
        Some(old_value) => choose|stored_key: Key|
            {
                &&& #[trigger] old_m@.contains_key(stored_key)
                &&& k.cmp_spec(&stored_key) is Equal
                &&& old_value == old_m@[stored_key]
                &&& final_m@ == old_m@.insert(stored_key, v)
            },
        None => k,
    };

    assert(final_m@.contains_key(stored_key));
    assert_maps_equal!(
        final_m.deep_view(),
        old_m.deep_view().insert(k.deep_view(), v.deep_view()),
        kd => {
            if final_m.deep_view().contains_key(kd) && kd != k.deep_view() {
                let key = choose|key: Key|
                    final_m@.contains_key(key) && #[trigger] key.deep_view() == kd;
                assert(old_m@.contains_key(key));
            }
            if old_m.deep_view().contains_key(kd) {
                let key = choose|key: Key|
                    old_m@.contains_key(key) && #[trigger] key.deep_view() == kd;
                assert(final_m@.contains_key(key));
            }
        }
    );
}

pub open spec fn btree_map_contains_key_ensures<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(m: &BTreeMap<Key, Value, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_map_keys_differ(m)
        &&& result == exists|key: Key|
            {
                &&& #[trigger] m@.contains_key(key)
                &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)) is Equal
            }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::contains_key::<Q> ](m: &BTreeMap<Key, Value, A>, k: &Q) -> (result:
    bool)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_map_contains_key_ensures(m, k, result),
;

pub broadcast proof fn lemma_btree_map_contains_key_ensures_if_cmp_matches_equality<
    Key: Ord,
    Value,
    A: Allocator + Clone,
>(m: &BTreeMap<Key, Value, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_map_contains_key_ensures(m, k, result),
    ensures
        result == m@.contains_key(*k),
{
    reveal(crate::laws_cmp::obeys_cmp_ord);
}

pub broadcast proof fn lemma_btree_map_contains_key_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    Value: DeepView,
    A: Allocator + Clone,
>(m: &BTreeMap<Key, Value, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_map_contains_key_ensures(m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        result == m.deep_view().contains_key(k.deep_view()),
{
    broadcast use {
        crate::map::group_map_lemmas,
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
    };

    reveal(crate::laws_cmp::obeys_cmp_ord);
    reveal(btree_map_deep_view_impl);

    if result {
        let key = choose|key: Key|
            {
                &&& #[trigger] m@.contains_key(key)
                &&& k.cmp_spec(&key) is Equal
            };
        assert(m.deep_view().contains_key(key.deep_view()));
    }
    if m.deep_view().contains_key(k.deep_view()) {
        let key = choose|key: Key|
            m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
        assert(k.cmp_spec(&key) is Equal);
    }
}

pub open spec fn btree_map_get_ensures<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(m: &BTreeMap<Key, Value, A>, k: &Q, result: Option<&Value>) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_map_keys_differ(m)
        &&& match result {
            Some(v) => exists|key: Key|
                {
                    &&& #[trigger] m@.contains_key(key)
                    &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)) is Equal
                    &&& m@[key] == *v
                },
            None => forall|key: Key| #[trigger]
                m@.contains_key(key) ==> !(k.cmp_spec(
                    <Key as BorrowSpec<Q>>::spec_borrow(&key),
                ) is Equal),
        }
    }
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::get::<Q> ](m: &'a BTreeMap<Key, Value, A>, k: &Q) -> (result: Option<
    &'a Value,
>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_map_get_ensures(m, k, result),
;

pub broadcast proof fn lemma_btree_map_get_ensures_if_cmp_matches_equality<
    Key: Ord,
    Value,
    A: Allocator + Clone,
>(m: &BTreeMap<Key, Value, A>, k: &Key, result: Option<&Value>)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_map_get_ensures(m, k, result),
    ensures
        match result {
            Some(v) => m@.contains_key(*k) && *v == m@[*k],
            None => !m@.contains_key(*k),
        },
{
    reveal(crate::laws_cmp::obeys_cmp_ord);
}

pub broadcast proof fn lemma_btree_map_get_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    Value: DeepView,
    A: Allocator + Clone,
>(m: &BTreeMap<Key, Value, A>, k: &Key, result: Option<&Value>)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_map_get_ensures(m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        match result {
            Some(v) => {
                &&& m.deep_view().contains_key(k.deep_view())
                &&& v.deep_view() == m.deep_view()[k.deep_view()]
            },
            None => !m.deep_view().contains_key(k.deep_view()),
        },
{
    broadcast use {
        crate::map::group_map_lemmas,
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
    };

    reveal(crate::laws_cmp::obeys_cmp_ord);
    reveal(btree_map_deep_view_impl);

    match result {
        Some(v) => {
            let stored_key = choose|key: Key|
                {
                    &&& #[trigger] m@.contains_key(key)
                    &&& k.cmp_spec(&key) is Equal
                    &&& m@[key] == *v
                };
            assert(m.deep_view().contains_key(k.deep_view()));
            let key = choose|key: Key|
                m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
            assert(key == stored_key);
        },
        None => {
            if m.deep_view().contains_key(k.deep_view()) {
                let key = choose|key: Key|
                    m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
                assert(k.cmp_spec(&key) is Equal);
            }
        },
    }
}

pub open spec fn btree_map_remove_ensures<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Q,
    result: Option<Value>,
) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_map_keys_differ(old_m)
        &&& btree_map_keys_differ(final_m)
        &&& match result {
            Some(v) => exists|key: Key|
                {
                    &&& #[trigger] old_m@.contains_key(key)
                    &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)) is Equal
                    &&& old_m@[key] == v
                    &&& final_m@ == old_m@.remove(key)
                },
            None => {
                &&& forall|key: Key| #[trigger]
                    old_m@.contains_key(key) ==> !(k.cmp_spec(
                        <Key as BorrowSpec<Q>>::spec_borrow(&key),
                    ) is Equal)
                &&& final_m@ == old_m@
            },
        }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::remove::<Q> ](m: &mut BTreeMap<Key, Value, A>, k: &Q) -> (result:
    Option<Value>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_map_remove_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_btree_map_remove_ensures_if_cmp_matches_equality<
    Key: Ord,
    Value,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Key,
    result: Option<Value>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_map_remove_ensures(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.remove(*k),
        match result {
            Some(v) => old_m@.contains_key(*k) && v == old_m@[*k],
            None => !old_m@.contains_key(*k),
        },
{
    broadcast use {crate::map::group_map_lemmas, crate::set::group_set_lemmas};

    reveal(crate::laws_cmp::obeys_cmp_ord);

    if result is None {
        assert(!old_m@.contains_key(*k));
        assert(old_m@.remove(*k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_btree_map_remove_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    Value: DeepView,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Key,
    result: Option<Value>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_map_remove_ensures(old_m, final_m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        final_m.deep_view() == old_m.deep_view().remove(k.deep_view()),
        match result {
            Some(v) => {
                &&& old_m.deep_view().contains_key(k.deep_view())
                &&& v.deep_view() == old_m.deep_view()[k.deep_view()]
            },
            None => !old_m.deep_view().contains_key(k.deep_view()),
        },
{
    broadcast use {
        crate::map::group_map_lemmas,
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
    };

    reveal(crate::laws_cmp::obeys_cmp_ord);
    reveal(btree_map_deep_view_impl);

    let stored_key = match result {
        Some(v) => choose|key: Key|
            {
                &&& #[trigger] old_m@.contains_key(key)
                &&& k.cmp_spec(&key) is Equal
                &&& old_m@[key] == v
                &&& final_m@ == old_m@.remove(key)
            },
        None => *k,
    };

    match result {
        Some(v) => {
            assert(old_m.deep_view().contains_key(k.deep_view()));
            let key = choose|key: Key|
                old_m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
            assert(key == stored_key);
        },
        None => {
            if old_m.deep_view().contains_key(k.deep_view()) {
                let key = choose|key: Key|
                    old_m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
                assert(k.cmp_spec(&key) is Equal);
            }
        },
    }

    assert_maps_equal!(
        final_m.deep_view(),
        old_m.deep_view().remove(k.deep_view()),
        kd => {
            if final_m.deep_view().contains_key(kd) {
                let key = choose|key: Key|
                    final_m@.contains_key(key) && #[trigger] key.deep_view() == kd;
                assert(old_m@.contains_key(key));
                assert(key.deep_view() != k.deep_view());
            }
            if old_m.deep_view().contains_key(kd) && kd != k.deep_view() {
                let key = choose|key: Key|
                    old_m@.contains_key(key) && #[trigger] key.deep_view() == kd;
                assert(final_m@.contains_key(key));
            }
        }
    );
}

pub open spec fn btree_map_get_mut_ensures<
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Q,
    result: Option<(Value, Value)>,
) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_map_keys_differ(old_m)
        &&& btree_map_keys_differ(final_m)
        &&& match result {
            Some((current_value, final_value)) => exists|stored_key: Key|
                {
                    &&& #[trigger] old_m@.contains_key(stored_key)
                    &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&stored_key)) is Equal
                    &&& old_m@[stored_key] == current_value
                    &&& final_m@ == old_m@.insert(stored_key, final_value)
                },
            None => {
                &&& forall|stored_key: Key| #[trigger]
                    old_m@.contains_key(stored_key) ==> !(k.cmp_spec(
                        <Key as BorrowSpec<Q>>::spec_borrow(&stored_key),
                    ) is Equal)
                &&& final_m@ == old_m@
            },
        }
    }
}

/// Specification for [`BTreeMap::get_mut`].
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::get_mut::<Q> ](
    m: &'a mut BTreeMap<Key, Value, A>,
    key: &Q,
) -> (result: Option<&'a mut Value>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        match result {
            Some(value) => btree_map_get_mut_ensures(
                old(m),
                final(m),
                key,
                Some((*value, *final(value))),
            ),
            None => btree_map_get_mut_ensures(old(m), final(m), key, None),
        },
;

pub broadcast proof fn lemma_btree_map_get_mut_ensures_if_cmp_matches_equality<
    Key: Ord,
    Value,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Key,
    result: Option<(Value, Value)>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_map_get_mut_ensures(old_m, final_m, k, result),
    ensures
        match result {
            Some((current_value, final_value)) => {
                &&& old_m@.contains_key(*k)
                &&& current_value == old_m@[*k]
                &&& final_m@ == old_m@.insert(*k, final_value)
            },
            None => {
                &&& !old_m@.contains_key(*k)
                &&& final_m@ == old_m@
            },
        },
{
    reveal(crate::laws_cmp::obeys_cmp_ord);
}

pub broadcast proof fn lemma_btree_map_get_mut_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    Value: DeepView,
    A: Allocator + Clone,
>(
    old_m: &BTreeMap<Key, Value, A>,
    final_m: &BTreeMap<Key, Value, A>,
    k: &Key,
    result: Option<(Value, Value)>,
)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_map_get_mut_ensures(old_m, final_m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        match result {
            Some((current_value, final_value)) => {
                &&& old_m.deep_view().contains_key(k.deep_view())
                &&& current_value.deep_view() == old_m.deep_view()[k.deep_view()]
                &&& final_m.deep_view() == old_m.deep_view().insert(
                    k.deep_view(),
                    final_value.deep_view(),
                )
            },
            None => {
                &&& !old_m.deep_view().contains_key(k.deep_view())
                &&& final_m.deep_view() == old_m.deep_view()
            },
        },
{
    reveal(crate::laws_cmp::obeys_cmp_ord);

    match result {
        Some((current_value, final_value)) => {
            lemma_btree_map_insert_ensures_if_cmp_matches_deep_equality(
                old_m,
                final_m,
                *k,
                final_value,
                Some(current_value),
            );
        },
        None => {
            broadcast use {
                crate::map::group_map_lemmas,
                crate::set::group_set_lemmas,
                Set::lemma_map_contains,
            };

            reveal(btree_map_deep_view_impl);

            if old_m.deep_view().contains_key(k.deep_view()) {
                let key = choose|key: Key|
                    old_m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
                assert(k.cmp_spec(&key) is Equal);
            }
        },
    }
}

pub assume_specification<Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::clear ](
    m: &mut BTreeMap<Key, Value, A>,
)
    ensures
        final(m)@ == Map::<Key, Value>::empty(),
;

/// Specification for [`BTreeMap::lower_bound_mut`].
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::lower_bound_mut::<Q> ](
    map: &'a mut BTreeMap<Key, Value, A>,
    bound: Bound<&Q>,
) -> (cursor: CursorMut<'a, Key, Value, A>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        ({
            &&& obeys_cmp::<Key>()
            &&& <Q as OrdSpec>::obeys_cmp_spec()
            &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
        }) ==> {
            &&& cursor@.wf()
            &&& cursor@.map == old(map)@
            &&& final(map)@ == cursor.final_map()
            &&& positioned_at_lower_bound(cursor@, bound)
        },
;

/// Specification for [`BTreeMap::upper_bound_mut`].
pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    Value,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeMap::<Key, Value, A>::upper_bound_mut::<Q> ](
    map: &'a mut BTreeMap<Key, Value, A>,
    bound: Bound<&Q>,
) -> (cursor: CursorMut<'a, Key, Value, A>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        ({
            &&& obeys_cmp::<Key>()
            &&& <Q as OrdSpec>::obeys_cmp_spec()
            &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
        }) ==> {
            &&& cursor@.wf()
            &&& cursor@.map == old(map)@
            &&& final(map)@ == cursor.final_map()
            &&& positioned_at_upper_bound(cursor@, bound)
        },
;

/// Specification for [`CursorMut::next`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::next ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position < old_model.keys.len()
                &&& *key == old_model.keys[old_model.position]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position + 1
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == old(cursor)@.keys.len()
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

/// Specification for [`CursorMut::prev`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::prev ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position > 0
                &&& *key == old_model.keys[old_model.position - 1]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position - 1
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == 0
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

/// Specification for [`CursorMut::peek_prev`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_prev ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position > 0
                &&& *key == old_model.keys[old_model.position - 1]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == 0
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

/// Specification for [`CursorMut::peek_next`].
pub assume_specification<'a, 'b, Key, Value, A>[ CursorMut::<'a, Key, Value, A>::peek_next ](
    cursor: &'b mut CursorMut<'a, Key, Value, A>,
) -> (result: Option<(&'b Key, &'b mut Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position < old_model.keys.len()
                &&& *key == old_model.keys[old_model.position]
                &&& *value == old_model.map[*key]
                &&& new_model.keys == old_model.keys
                &&& new_model.position == old_model.position
                &&& new_model.map == old_model.map.insert(*key, *final(value))
            },
            None => {
                &&& old(cursor)@.position == old(cursor)@.keys.len()
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

/// Specification for [`CursorMut::insert_after`].
pub assume_specification<'a, Key: Ord, Value, A: Allocator + Clone>[ CursorMut::<
    'a,
    Key,
    Value,
    A,
>::insert_after ](cursor: &mut CursorMut<'a, Key, Value, A>, key: Key, value: Value) -> (result:
    Result<(), UnorderedKeyError>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        obeys_cmp::<Key>() ==> {
            &&& final(cursor)@.wf()
            &&& match result {
                Ok(()) => {
                    let old_model = old(cursor)@;
                    let new_model = final(cursor)@;
                    &&& key_fits_at_position(old_model, key)
                    &&& new_model.keys == old_model.keys.insert(old_model.position, key)
                    &&& new_model.position == old_model.position
                    &&& new_model.map == old_model.map.insert(key, value)
                },
                Err(_) => {
                    &&& !key_fits_at_position(old(cursor)@, key)
                    &&& final(cursor)@ == old(cursor)@
                },
            }
        },
;

/// Specification for [`CursorMut::remove_next`].
pub assume_specification<'a, Key: Ord, Value, A: Allocator + Clone>[ CursorMut::<
    'a,
    Key,
    Value,
    A,
>::remove_next ](cursor: &mut CursorMut<'a, Key, Value, A>) -> (result: Option<(Key, Value)>)
    requires
        old(cursor)@.wf(),
    ensures
        final(cursor).final_map() == old(cursor).final_map(),
        final(cursor)@.wf(),
        match result {
            Some((key, value)) => {
                let old_model = old(cursor)@;
                let new_model = final(cursor)@;
                &&& old_model.position < old_model.keys.len()
                &&& key == old_model.keys[old_model.position]
                &&& value == old_model.map[key]
                &&& new_model.keys == old_model.keys.remove(old_model.position)
                &&& new_model.position == old_model.position
                &&& new_model.map == old_model.map.remove(key)
            },
            None => {
                &&& old(cursor)@.position == old(cursor)@.keys.len()
                &&& final(cursor)@ == old(cursor)@
            },
        },
;

pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::keys ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (keys: Keys<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            &&& IteratorSpec::remaining(&keys).unref().to_set() == m@.dom()
            &&& IteratorSpec::remaining(&keys).no_duplicates()
            &&& IteratorSpec::remaining(&keys).len() == m@.dom().len()
            &&& increasing_seq(IteratorSpec::remaining(&keys))
            &&& into_iter_keys(keys) == IteratorSpec::remaining(&keys).unref()
            &&& IteratorSpec::decrease(&keys) is Some
        },
;

pub assume_specification<'a, Key, Value, A: Allocator + Clone>[ BTreeMap::<Key, Value, A>::values ](
    m: &'a BTreeMap<Key, Value, A>,
) -> (values: Values<'a, Key, Value>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            &&& IteratorSpec::remaining(&values).unref().to_set() == m@.values()
            &&& IteratorSpec::remaining(&values).len() == m@.dom().len()
            &&& into_iter_values(values) == IteratorSpec::remaining(&values).unref()
            &&& IteratorSpec::decrease(&values) is Some
            &&& exists|key_seq: Seq<Key>|
                {
                    &&& increasing_seq(key_seq)
                    &&& key_seq.to_set() == m@.dom()
                    &&& key_seq.no_duplicates()
                    &&& IteratorSpec::remaining(&values) == key_seq.map(|i: int, k| &m@[k])
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

// To allow reasoning about the "contents" of the BtreeSet iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original keys.
pub uninterp spec fn into_iter_btree_keys<'a, Key>(i: btree_set::Iter::<'a, Key>) -> Seq<Key>;

impl<'a, T> super::iter::IteratorSpecImpl for btree_set::Iter::<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_btree_keys(*self).len() {
            Some(&into_iter_btree_keys(*self)[index])
        } else {
            None
        }
    }
}

/// Specifications for the behavior of [`alloc::collections::BTreeSet`](https://doc.rust-lang.org/alloc/collections/struct.BTreeSet.html).
///
/// We model a `BTreeSet` as having a view of type `Set<Key>`, which reflects the current state of the set.
///
/// These specifications are only meaningful if `obeys_cmp::<Key>()` hold.
/// See [`obeys_cmp`] for information on use with primitive types and custom types.
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

pub open spec fn btree_set_elements_differ<Key: Ord, A: Allocator + Clone>(
    m: &BTreeSet<Key, A>,
) -> bool {
    forall|k1: Key, k2: Key|
        {
            &&& #[trigger] m@.contains(k1)
            &&& #[trigger] m@.contains(k2)
            &&& k1 != k2
        } ==> !(k1.cmp_spec(&k2) is Equal)
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

pub open spec fn btree_set_insert_ensures<Key: Ord, A: Allocator + Clone>(
    old_m: &BTreeSet<Key, A>,
    final_m: &BTreeSet<Key, A>,
    k: Key,
    result: bool,
) -> bool {
    obeys_cmp::<Key>() ==> {
        &&& btree_set_elements_differ(old_m)
        &&& btree_set_elements_differ(final_m)
        &&& if result {
            &&& forall|stored_key: Key| #[trigger]
                old_m@.contains(stored_key) ==> !(k.cmp_spec(&stored_key) is Equal)
            &&& final_m@ == old_m@.insert(k)
        } else {
            &&& exists|stored_key: Key| #[trigger]
                old_m@.contains(stored_key) && k.cmp_spec(&stored_key) is Equal
            &&& final_m@ == old_m@
        }
    }
}

pub assume_specification<Key: Ord, A: Allocator + Clone>[ BTreeSet::<Key, A>::insert ](
    m: &mut BTreeSet<Key, A>,
    k: Key,
) -> (result: bool)
    ensures
        btree_set_insert_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_btree_set_insert_ensures_if_cmp_matches_equality<
    Key: Ord,
    A: Allocator + Clone,
>(old_m: &BTreeSet<Key, A>, final_m: &BTreeSet<Key, A>, k: Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_set_insert_ensures::<Key, A>(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.insert(k),
        result == !old_m@.contains(k),
{
    broadcast use crate::set::group_set_lemmas;

    assert(k.cmp_spec(&k) is Equal);
    if !result {
        assert(old_m@.contains(k));
        assert(old_m@.insert(k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_btree_set_insert_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    A: Allocator + Clone,
>(old_m: &BTreeSet<Key, A>, final_m: &BTreeSet<Key, A>, k: Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_set_insert_ensures::<Key, A>(old_m, final_m, k, result),
    ensures
        final_m.deep_view() == old_m.deep_view().insert(k.deep_view()),
        result == !old_m.deep_view().contains(k.deep_view()),
{
    broadcast use {
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
        Set::lemma_set_map_insert_commute,
    };

    if result {
        assert(!old_m.deep_view().contains(k.deep_view())) by {
            if old_m.deep_view().contains(k.deep_view()) {
                let stored_key = choose|stored_key: Key|
                    old_m@.contains(stored_key) && #[trigger] stored_key.deep_view()
                        == k.deep_view();
                assert(k.cmp_spec(&stored_key) is Equal);
            }
        }
    } else {
        let stored_key = choose|stored_key: Key| #[trigger]
            old_m@.contains(stored_key) && k.cmp_spec(&stored_key) is Equal;
        assert(stored_key.deep_view() == k.deep_view());
        assert(old_m.deep_view().contains(k.deep_view()));
    }
    assert(final_m.deep_view() =~= old_m.deep_view().insert(k.deep_view()));
}

pub open spec fn btree_set_contains_ensures<
    Key: Borrow<Q> + Ord,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(m: &BTreeSet<Key, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_set_elements_differ(m)
        &&& result == exists|key: Key|
            {
                &&& #[trigger] m@.contains(key)
                &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)) is Equal
            }
    }
}

pub assume_specification<Key: Borrow<Q> + Ord, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<
    Key,
    A,
>::contains ](m: &BTreeSet<Key, A>, k: &Q) -> (result: bool)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_set_contains_ensures(m, k, result),
;

pub broadcast proof fn lemma_btree_set_contains_ensures_if_cmp_matches_equality<
    Key: Ord,
    A: Allocator + Clone,
>(m: &BTreeSet<Key, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_set_contains_ensures(m, k, result),
    ensures
        result == m@.contains(*k),
{
    reveal(crate::laws_cmp::obeys_cmp_ord);
}

pub broadcast proof fn lemma_btree_set_contains_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    A: Allocator + Clone,
>(m: &BTreeSet<Key, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_set_contains_ensures(m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        result == m.deep_view().contains(k.deep_view()),
{
    broadcast use {crate::set::group_set_lemmas, Set::lemma_map_contains};

    reveal(crate::laws_cmp::obeys_cmp_ord);

    if result {
        let key = choose|key: Key|
            {
                &&& #[trigger] m@.contains(key)
                &&& k.cmp_spec(&key) is Equal
            };
        assert(m.deep_view().contains(key.deep_view()));
    }
    if m.deep_view().contains(k.deep_view()) {
        let key = choose|key: Key| m@.contains(key) && #[trigger] key.deep_view() == k.deep_view();
        assert(k.cmp_spec(&key) is Equal);
    }
}

pub open spec fn btree_set_get_ensures<Key: Borrow<Q> + Ord, A: Allocator + Clone, Q: Ord + ?Sized>(
    m: &BTreeSet<Key, A>,
    k: &Q,
    result: Option<&Key>,
) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_set_elements_differ(m)
        &&& match result {
            Some(key) => {
                &&& m@.contains(*key)
                &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(key)) is Equal
            },
            None => forall|key: Key| #[trigger]
                m@.contains(key) ==> !(k.cmp_spec(
                    <Key as BorrowSpec<Q>>::spec_borrow(&key),
                ) is Equal),
        }
    }
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Ord,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>[ BTreeSet::<Key, A>::get::<Q> ](m: &'a BTreeSet<Key, A>, k: &Q) -> (result: Option<&'a Key>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_set_get_ensures(m, k, result),
;

pub broadcast proof fn lemma_btree_set_get_ensures_if_cmp_matches_equality<
    Key: Ord,
    A: Allocator + Clone,
>(m: &BTreeSet<Key, A>, k: &Key, result: Option<&Key>)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_set_get_ensures(m, k, result),
    ensures
        match result {
            Some(key) => m@.contains(*key) && *key == *k,
            None => !m@.contains(*k),
        },
{
    reveal(crate::laws_cmp::obeys_cmp_ord);
}

pub broadcast proof fn lemma_btree_set_get_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    A: Allocator + Clone,
>(m: &BTreeSet<Key, A>, k: &Key, result: Option<&Key>)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_set_get_ensures(m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        match result {
            Some(key) => {
                &&& m@.contains(*key)
                &&& m.deep_view().contains(k.deep_view())
                &&& key.deep_view() == k.deep_view()
            },
            None => !m.deep_view().contains(k.deep_view()),
        },
{
    broadcast use {crate::set::group_set_lemmas, Set::lemma_map_contains};

    reveal(crate::laws_cmp::obeys_cmp_ord);

    match result {
        Some(key) => {
            assert(m.deep_view().contains(key.deep_view()));
        },
        None => {
            if m.deep_view().contains(k.deep_view()) {
                let key = choose|key: Key|
                    m@.contains(key) && #[trigger] key.deep_view() == k.deep_view();
                assert(k.cmp_spec(&key) is Equal);
            }
        },
    }
}

pub open spec fn btree_set_remove_ensures<
    Key: Borrow<Q> + Ord,
    A: Allocator + Clone,
    Q: Ord + ?Sized,
>(old_m: &BTreeSet<Key, A>, final_m: &BTreeSet<Key, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_cmp::<Key>()
        &&& <Q as OrdSpec>::obeys_cmp_spec()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& btree_set_elements_differ(old_m)
        &&& btree_set_elements_differ(final_m)
        &&& if result {
            exists|key: Key|
                {
                    &&& #[trigger] old_m@.contains(key)
                    &&& k.cmp_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)) is Equal
                    &&& final_m@ == old_m@.remove(key)
                }
        } else {
            &&& forall|key: Key| #[trigger]
                old_m@.contains(key) ==> !(k.cmp_spec(
                    <Key as BorrowSpec<Q>>::spec_borrow(&key),
                ) is Equal)
            &&& final_m@ == old_m@
        }
    }
}

pub assume_specification<Key: Borrow<Q> + Ord, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<
    Key,
    A,
>::remove::<Q> ](m: &mut BTreeSet<Key, A>, k: &Q) -> (result: bool)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        btree_set_remove_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_btree_set_remove_ensures_if_cmp_matches_equality<
    Key: Ord,
    A: Allocator + Clone,
>(old_m: &BTreeSet<Key, A>, final_m: &BTreeSet<Key, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_equality::<Key>(),
        #[trigger] btree_set_remove_ensures(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.remove(*k),
        result == old_m@.contains(*k),
{
    broadcast use crate::set::group_set_lemmas;

    reveal(crate::laws_cmp::obeys_cmp_ord);

    if !result {
        assert(!old_m@.contains(*k));
        assert(old_m@.remove(*k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_btree_set_remove_ensures_if_cmp_matches_deep_equality<
    Key: Ord + DeepView,
    A: Allocator + Clone,
>(old_m: &BTreeSet<Key, A>, final_m: &BTreeSet<Key, A>, k: &Key, result: bool)
    requires
        obeys_cmp::<Key>(),
        cmp_matches_deep_equality::<Key>(),
        #[trigger] btree_set_remove_ensures(old_m, final_m, k, result),
    ensures
        Key::obeys_cmp_spec(),
        final_m.deep_view() == old_m.deep_view().remove(k.deep_view()),
        result == old_m.deep_view().contains(k.deep_view()),
{
    broadcast use {crate::set::group_set_lemmas, Set::lemma_map_contains};

    reveal(crate::laws_cmp::obeys_cmp_ord);

    let stored_key = if result {
        choose|key: Key|
            {
                &&& #[trigger] old_m@.contains(key)
                &&& k.cmp_spec(&key) is Equal
                &&& final_m@ == old_m@.remove(key)
            }
    } else {
        *k
    };
    assert(stored_key.deep_view() == k.deep_view());

    if result {
        assert(old_m.deep_view().contains(k.deep_view()));
    } else if old_m.deep_view().contains(k.deep_view()) {
        let key = choose|key: Key|
            old_m@.contains(key) && #[trigger] key.deep_view() == k.deep_view();
        assert(k.cmp_spec(&key) is Equal);
    }
    assert forall|kd: Key::V| #[trigger]
        final_m.deep_view().contains(kd) <==> old_m.deep_view().remove(k.deep_view()).contains(
            kd,
        ) by {
        if final_m.deep_view().contains(kd) {
            let key = choose|key: Key| final_m@.contains(key) && #[trigger] key.deep_view() == kd;
            assert(old_m@.contains(key));
            assert(key.deep_view() != k.deep_view());
        }
        if old_m.deep_view().contains(kd) && kd != k.deep_view() {
            let key = choose|key: Key| old_m@.contains(key) && #[trigger] key.deep_view() == kd;
            assert(final_m@.contains(key));
        }
    }
    assert(final_m.deep_view() =~= old_m.deep_view().remove(k.deep_view()));
}

pub assume_specification<Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::clear ](
    m: &mut BTreeSet<Key, A>,
) where A: Clone
    ensures
        final(m)@ == Set::<Key>::empty(),
;

pub assume_specification<'a, Key, A: Allocator + Clone>[ BTreeSet::<Key, A>::iter ](
    m: &'a BTreeSet<Key, A>,
) -> (r: btree_set::Iter<'a, Key>)
    ensures
        key_obeys_cmp_spec::<Key>() ==> {
            &&& IteratorSpec::remaining(&r).unref().to_set() == m@
            &&& IteratorSpec::remaining(&r).no_duplicates()
            &&& IteratorSpec::remaining(&r).len() == m@.len()
            &&& increasing_seq(IteratorSpec::remaining(&r))
            &&& into_iter_btree_keys(r) == IteratorSpec::remaining(&r).unref()
            &&& IteratorSpec::decrease(&r) is Some
        },
;

pub broadcast axiom fn axiom_btree_set_decreases<Key, A: Allocator + Clone>(m: BTreeSet<Key, A>)
    ensures
        #[trigger] (decreases_to!(m => m@)),
;

pub broadcast group group_btree_axioms {
    axiom_key_obeys_cmp_spec_meaning,
    axiom_increasing_seq_meaning,
    axiom_spec_btree_map_len,
    lemma_btree_map_insert_ensures_if_cmp_matches_equality,
    lemma_btree_map_insert_ensures_if_cmp_matches_deep_equality,
    lemma_btree_map_contains_key_ensures_if_cmp_matches_equality,
    lemma_btree_map_contains_key_ensures_if_cmp_matches_deep_equality,
    lemma_btree_map_get_ensures_if_cmp_matches_equality,
    lemma_btree_map_get_ensures_if_cmp_matches_deep_equality,
    lemma_btree_map_remove_ensures_if_cmp_matches_equality,
    lemma_btree_map_remove_ensures_if_cmp_matches_deep_equality,
    lemma_btree_map_get_mut_ensures_if_cmp_matches_equality,
    lemma_btree_map_get_mut_ensures_if_cmp_matches_deep_equality,
    axiom_spec_btree_set_len,
    lemma_btree_set_insert_ensures_if_cmp_matches_equality,
    lemma_btree_set_insert_ensures_if_cmp_matches_deep_equality,
    lemma_btree_set_contains_ensures_if_cmp_matches_equality,
    lemma_btree_set_contains_ensures_if_cmp_matches_deep_equality,
    lemma_btree_set_get_ensures_if_cmp_matches_equality,
    lemma_btree_set_get_ensures_if_cmp_matches_deep_equality,
    lemma_btree_set_remove_ensures_if_cmp_matches_equality,
    lemma_btree_set_remove_ensures_if_cmp_matches_deep_equality,
    axiom_btree_map_decreases,
    axiom_btree_set_decreases,
    axiom_has_resolved_cursor,
}

} // verus!
