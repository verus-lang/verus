//! This code adds specifications for the standard-library types
//! `alloc::collections::BTreeMap` and `alloc::collections::BTreeSet`.
//!
//! The specification is only meaningful when the `Key` obeys our [`Ord`] model,
//! as specified by [`super::super::laws_cmp::obeys_cmp_spec`].
//!
//! By default, the Verus standard library brings useful axioms
//! about the behavior of `BTreeMap` and `BTreeSet` into the ambient
//! reasoning context by broadcasting the group
//! `vstd::std_specs::btree::group_btree_axioms`.
use super::super::laws_cmp::obeys_cmp;
use super::super::prelude::*;
use super::cmp::OrdSpec;
use super::iter::IteratorSpec;

#[cfg(verus_keep_ghost)]
use super::super::map::assert_maps_equal;

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

    uninterp spec fn will_return_none(&self) -> bool;

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

    uninterp spec fn will_return_none(&self) -> bool;

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

    uninterp spec fn will_return_none(&self) -> bool;

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
pub uninterp spec fn borrowed_key_ordering_matches<Key: Borrow<Q> + Ord, Q: Ord + ?Sized>() -> bool;

/// A key type has the same ordering as itself.
pub broadcast axiom fn axiom_deref_key_ordering_matches<Key: Ord>()
    ensures
        #[trigger] borrowed_key_ordering_matches::<Key, Key>(),
;

/// The ordering of a stored key relative to a borrowed lookup key.
pub uninterp spec fn borrowed_key_cmp<Key, Q: ?Sized>(stored_key: Key, key: &Q) -> Ordering;

/// Comparing a stored key against a borrowed key of the same type agrees with [`OrdSpec`].
pub broadcast axiom fn axiom_deref_key_cmp<Key: Ord>(stored_key: Key, key: &Key)
    ensures
        #[trigger] borrowed_key_cmp::<Key, Key>(stored_key, key) == stored_key.cmp_spec(key),
;

/// Whether a key occurs before the gap returned by [`BTreeMap::lower_bound_mut`].
pub open spec fn before_lower_bound<Key, Q: ?Sized>(key: Key, bound: Bound<&Q>) -> bool {
    match bound {
        Bound::Included(bound_key) => borrowed_key_cmp(key, bound_key) is Less,
        Bound::Excluded(bound_key) => !(borrowed_key_cmp(key, bound_key) is Greater),
        Bound::Unbounded => false,
    }
}

/// Whether a key occurs before the gap returned by [`BTreeMap::upper_bound_mut`].
pub open spec fn before_upper_bound<Key, Q: ?Sized>(key: Key, bound: Bound<&Q>) -> bool {
    match bound {
        Bound::Included(bound_key) => !(borrowed_key_cmp(key, bound_key) is Greater),
        Bound::Excluded(bound_key) => borrowed_key_cmp(key, bound_key) is Less,
        Bound::Unbounded => true,
    }
}

/// Whether a cursor is at the gap selected by [`BTreeMap::lower_bound_mut`].
pub open spec fn positioned_at_lower_bound<Key, Value, Q: ?Sized>(
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
pub open spec fn positioned_at_upper_bound<Key, Value, Q: ?Sized>(
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
        obeys_cmp::<Key>() ==> {
            &&& final(m)@ == old(m)@.insert(k, v)
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
        obeys_cmp::<Key>() ==> result == contains_borrowed_key(m@, k),
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
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        obeys_cmp::<Key>() ==> match result {
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
        obeys_cmp::<Key>() ==> {
            &&& borrowed_key_removed(old(m)@, final(m)@, k)
            &&& match result {
                Some(v) => maps_borrowed_key_to_value(old(m)@, k, v),
                None => !contains_borrowed_key(old(m)@, k),
            }
        },
;

/// Relates a map before and after mutating the value selected by a borrowed key.
pub open spec fn borrowed_key_mutated<Key, Value, Q: ?Sized>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Q,
    old_value: Value,
    new_value: Value,
) -> bool {
    &&& maps_borrowed_key_to_value(old_map, key, old_value)
    &&& maps_borrowed_key_to_value(new_map, key, new_value)
    &&& exists|remainder: Map<Key, Value>|
        {
            &&& borrowed_key_removed(old_map, remainder, key)
            &&& borrowed_key_removed(new_map, remainder, key)
        }
}

/// Simplifies [`borrowed_key_mutated`] when the borrowed key has the map's key type.
pub broadcast proof fn lemma_borrowed_key_mutated_deref<Key, Value>(
    old_map: Map<Key, Value>,
    new_map: Map<Key, Value>,
    key: &Key,
    old_value: Value,
    new_value: Value,
)
    ensures
        #[trigger] borrowed_key_mutated(old_map, new_map, key, old_value, new_value) <==> {
            &&& old_map.contains_key(*key)
            &&& old_map[*key] == old_value
            &&& new_map == old_map.insert(*key, new_value)
        },
{
    broadcast use {
        axiom_deref_key_removed,
        axiom_maps_deref_key_to_value,
        super::super::map::group_map_lemmas,
        super::super::set::group_set_lemmas,
    };

    if borrowed_key_mutated(old_map, new_map, key, old_value, new_value) {
        let remainder = choose|remainder: Map<Key, Value>|
            {
                &&& borrowed_key_removed(old_map, remainder, key)
                &&& borrowed_key_removed(new_map, remainder, key)
            };
        assert(remainder == new_map.remove(*key));
        assert_maps_equal!(new_map, old_map.insert(*key, new_value), candidate => {
            if candidate != *key {
                assert(old_map.remove(*key)[candidate] == old_map[candidate]);
            }
        });
    } else if old_map.contains_key(*key) && old_map[*key] == old_value && new_map == old_map.insert(
        *key,
        new_value,
    ) {
        let remainder = old_map.remove(*key);
        assert_maps_equal!(new_map.remove(*key), remainder, candidate => {});
        assert(borrowed_key_removed(new_map, remainder, key));
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
    map: &'a mut BTreeMap<Key, Value, A>,
    key: &Q,
) -> (result: Option<&'a mut Value>)
    requires
        borrowed_key_ordering_matches::<Key, Q>(),
    ensures
        obeys_cmp::<Key>() ==> match result {
            Some(value) => borrowed_key_mutated(old(map)@, final(map)@, key, *value, *final(value)),
            None => !contains_borrowed_key(old(map)@, key) && final(map)@ == old(map)@,
        },
;

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
        obeys_cmp::<Key>() ==> {
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
        obeys_cmp::<Key>() ==> {
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

    uninterp spec fn will_return_none(&self) -> bool;

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
        obeys_cmp::<Key>() ==> {
            &&& final(m)@ == old(m)@.insert(k)
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
        obeys_cmp::<Key>() ==> result == set_contains_borrowed_key(m@, k),
    no_unwind
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
        obeys_cmp::<Key>() ==> match result {
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
        obeys_cmp::<Key>() ==> {
            &&& sets_differ_by_borrowed_key(old(m)@, final(m)@, k)
            &&& result == set_contains_borrowed_key(old(m)@, k)
        },
;

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
    axiom_box_key_removed,
    axiom_contains_deref_key,
    axiom_contains_box,
    axiom_deref_key_removed,
    axiom_maps_deref_key_to_value,
    axiom_maps_box_key_to_value,
    axiom_btree_map_deepview_borrow,
    axiom_spec_btree_map_len,
    axiom_set_box_key_removed,
    axiom_set_contains_deref_key,
    axiom_set_contains_box,
    axiom_set_deref_key_removed,
    axiom_set_deref_key_to_value,
    axiom_set_box_key_to_value,
    axiom_spec_btree_set_len,
    axiom_btree_map_decreases,
    axiom_btree_set_decreases,
    axiom_deref_key_ordering_matches,
    axiom_deref_key_cmp,
    axiom_has_resolved_cursor,
    lemma_borrowed_key_mutated_deref,
}

} // verus!
