//! Specifications for `std::collections::BTreeMap`
//!
//! BTreeMap is viewed as a `Map<K, V>` since it maintains key-value associations.
//! Unlike HashMap, BTreeMap requires Ord on keys and iteration is ordered.
use super::super::prelude::*;

use alloc::collections::btree_map::{IntoIter, Iter, Keys, Values};
use alloc::collections::BTreeMap;
use core::alloc::Allocator;
use core::clone::Clone;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeMap<K, V, A: Allocator + Clone>(BTreeMap<K, V, A>);

/// BTreeMap views as a `Map<K, V>`
impl<K, V, A: Allocator + Clone> View for BTreeMap<K, V, A> {
    type V = Map<K, V>;

    uninterp spec fn view(&self) -> Map<K, V>;
}

pub trait BTreeMapAdditionalSpecFns<K, V>: View<V = Map<K, V>> {
    spec fn spec_index(&self, k: K) -> V
        recommends
            self@.contains_key(k),
    ;
}

impl<K, V, A: Allocator + Clone> BTreeMapAdditionalSpecFns<K, V> for BTreeMap<K, V, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, k: K) -> V {
        self@.index(k)
    }
}

// Len (with autospec pattern)

pub uninterp spec fn spec_btree_map_len<K, V, A: Allocator + Clone>(m: &BTreeMap<K, V, A>) -> usize;

pub broadcast proof fn axiom_spec_len<K, V, A: Allocator + Clone>(m: &BTreeMap<K, V, A>)
    ensures
        #[trigger] spec_btree_map_len(m) == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_map_len)]
pub assume_specification<K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::len ](m: &BTreeMap<K, V, A>) -> (len: usize)
    ensures
        len == spec_btree_map_len(m),
    no_unwind
;

pub assume_specification<K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::is_empty ](m: &BTreeMap<K, V, A>) -> (res: bool)
    ensures
        res <==> m@.len() == 0,
;

pub assume_specification<K, V>[ BTreeMap::<K, V>::new ]() -> (m: BTreeMap<K, V>)
    ensures
        m@ == Map::<K, V>::empty(),
;

pub assume_specification<K: Ord, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::insert ](
    m: &mut BTreeMap<K, V, A>,
    key: K,
    value: V,
) -> (old_value: Option<V>)
    ensures
        m@ == old(m)@.insert(key, value),
        old(m)@.contains_key(key) ==> old_value.is_some() && old_value.unwrap() == old(m)@[key],
        !old(m)@.contains_key(key) ==> old_value.is_none(),
;

// For borrowed key operations, we use the same pattern as HashMap.
// These take &Q where K: Borrow<Q>, allowing e.g. &str lookups in BTreeMap<String, V>.

pub uninterp spec fn btree_contains_borrowed_key<K, V, Q: ?Sized>(m: Map<K, V>, k: &Q) -> bool;

pub broadcast proof fn axiom_btree_contains_deref_key<Q, V>(m: Map<Q, V>, k: &Q)
    ensures
        #[trigger] btree_contains_borrowed_key::<Q, V, Q>(m, k) <==> m.contains_key(*k),
{
    admit();
}

pub uninterp spec fn btree_maps_borrowed_key_to_value<K, V, Q: ?Sized>(m: Map<K, V>, k: &Q, v: V) -> bool;

pub broadcast proof fn axiom_btree_maps_deref_key_to_value<Q, V>(m: Map<Q, V>, k: &Q, v: V)
    ensures
        #[trigger] btree_maps_borrowed_key_to_value::<Q, V, Q>(m, k, v) <==> m.contains_key(*k) && m[*k] == v,
{
    admit();
}

pub uninterp spec fn btree_borrowed_key_removed<K, V, Q: ?Sized>(old_m: Map<K, V>, new_m: Map<K, V>, k: &Q) -> bool;

pub broadcast proof fn axiom_btree_deref_key_removed<Q, V>(old_m: Map<Q, V>, new_m: Map<Q, V>, k: &Q)
    ensures
        #[trigger] btree_borrowed_key_removed::<Q, V, Q>(old_m, new_m, k) <==> new_m == old_m.remove(*k),
{
    admit();
}

use core::borrow::Borrow;

pub assume_specification<'a, K: Ord + Borrow<Q>, V, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeMap::<K, V, A>::get::<Q> ](
    m: &'a BTreeMap<K, V, A>,
    key: &Q,
) -> (value: Option<&'a V>)
    ensures
        match value {
            Some(v) => btree_maps_borrowed_key_to_value(m@, key, *v),
            None => !btree_contains_borrowed_key(m@, key),
        },
    no_unwind
;

pub assume_specification<K: Ord + Borrow<Q>, V, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeMap::<K, V, A>::contains_key::<Q> ](
    m: &BTreeMap<K, V, A>,
    key: &Q,
) -> (result: bool)
    ensures
        result == btree_contains_borrowed_key(m@, key),
;

pub assume_specification<K: Ord + Borrow<Q>, V, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeMap::<K, V, A>::remove::<Q> ](
    m: &mut BTreeMap<K, V, A>,
    key: &Q,
) -> (old_value: Option<V>)
    ensures
        btree_borrowed_key_removed(old(m)@, m@, key),
        match old_value {
            Some(v) => btree_maps_borrowed_key_to_value(old(m)@, key, v),
            None => !btree_contains_borrowed_key(old(m)@, key),
        },
;

pub assume_specification<K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::clear ](m: &mut BTreeMap<K, V, A>)
    ensures
        m@ == Map::<K, V>::empty(),
;

// retain - NOT WRAPPABLE
//
// BTreeMap::retain takes FnMut(&K, &mut V) -> bool, allowing the predicate to
// mutate values while filtering. This breaks the traditional expectation that
// filter predicates are pure functions. Verus does not yet support &mut in
// closure arguments, so retain cannot be called in verified code.
//
// If Rust had used FnMut(&K, &V) -> bool (immutable reference), this would be
// straightforward to specify and verify. The &mut V is a pragmatic choice for
// efficiency (mutate + filter in one pass) at the cost of verification clarity.
//
// pub assume_specification<K: Ord, V, A: Allocator + Clone, F: FnMut(&K, &mut V) -> bool>[
//     BTreeMap::<K, V, A>::retain::<F>
// ](m: &mut BTreeMap<K, V, A>, f: F)
//     ensures
//         forall|k: K| m@.contains_key(k) ==> old(m)@.contains_key(k),
//         forall|k: K| m@.contains_key(k) ==> m@[k] == old(m)@[k],
// ;

pub assume_specification<K: Clone, V: Clone, A: Allocator + Clone>[ <BTreeMap<K, V, A> as Clone>::clone ](
    m: &BTreeMap<K, V, A>,
) -> (res: BTreeMap<K, V, A>)
    ensures
        res@ == m@,
;

/// A `Map` constructed from a `BTreeMap` is always finite.
pub broadcast proof fn axiom_btree_map_view_finite_dom<K, V, A: Allocator + Clone>(m: BTreeMap<K, V, A>)
    ensures
        #[trigger] m@.dom().finite(),
{
    admit();
}

// Keys iterator

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExBTreeMapKeys<'a, K, V>(Keys<'a, K, V>);

impl<'a, K, V> View for Keys<'a, K, V> {
    type V = (int, Seq<K>);

    uninterp spec fn view(&self) -> (int, Seq<K>);
}

pub assume_specification<'a, K, V>[ Keys::<'a, K, V>::next ](
    keys: &mut Keys<'a, K, V>,
) -> (r: Option<&'a K>)
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
                    &&& *k == old_seq[old_index]
                },
            }
        }),
;

pub struct BTreeMapKeysGhostIterator<'a, K, V> {
    pub pos: int,
    pub keys: Seq<K>,
    pub _marker: PhantomData<&'a V>,
}

impl<'a, K, V> super::super::pervasive::ForLoopGhostIteratorNew for Keys<'a, K, V> {
    type GhostIter = BTreeMapKeysGhostIterator<'a, K, V>;

    open spec fn ghost_iter(&self) -> BTreeMapKeysGhostIterator<'a, K, V> {
        BTreeMapKeysGhostIterator { pos: self@.0, keys: self@.1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> super::super::pervasive::ForLoopGhostIterator for BTreeMapKeysGhostIterator<'a, K, V> {
    type ExecIter = Keys<'a, K, V>;
    type Item = K;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Keys<'a, K, V>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<K> {
        if 0 <= self.pos < self.keys.len() {
            Some(self.keys[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Keys<'a, K, V>) -> BTreeMapKeysGhostIterator<'a, K, V> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, K, V> View for BTreeMapKeysGhostIterator<'a, K, V> {
    type V = Seq<K>;

    open spec fn view(&self) -> Seq<K> {
        self.keys.take(self.pos)
    }
}

pub assume_specification<'a, K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::keys ](m: &'a BTreeMap<K, V, A>) -> (keys: Keys<'a, K, V>)
    ensures
        ({
            let (index, s) = keys@;
            &&& index == 0
            &&& s.to_set() == m@.dom()
            &&& s.no_duplicates()
            &&& s.len() == m@.len()  // length preserved
        }),
    no_unwind
;

// Values iterator

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExBTreeMapValues<'a, K, V>(Values<'a, K, V>);

impl<'a, K, V> View for Values<'a, K, V> {
    type V = (int, Seq<V>);

    uninterp spec fn view(&self) -> (int, Seq<V>);
}

pub assume_specification<'a, K, V>[ Values::<'a, K, V>::next ](
    values: &mut Values<'a, K, V>,
) -> (r: Option<&'a V>)
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
                    &&& *v == old_seq[old_index]
                },
            }
        }),
;

pub struct BTreeMapValuesGhostIterator<'a, K, V> {
    pub pos: int,
    pub values: Seq<V>,
    pub _marker: PhantomData<&'a K>,
}

impl<'a, K, V> super::super::pervasive::ForLoopGhostIteratorNew for Values<'a, K, V> {
    type GhostIter = BTreeMapValuesGhostIterator<'a, K, V>;

    open spec fn ghost_iter(&self) -> BTreeMapValuesGhostIterator<'a, K, V> {
        BTreeMapValuesGhostIterator { pos: self@.0, values: self@.1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> super::super::pervasive::ForLoopGhostIterator for BTreeMapValuesGhostIterator<'a, K, V> {
    type ExecIter = Values<'a, K, V>;
    type Item = V;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Values<'a, K, V>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<V> {
        if 0 <= self.pos < self.values.len() {
            Some(self.values[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Values<'a, K, V>) -> BTreeMapValuesGhostIterator<'a, K, V> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, K, V> View for BTreeMapValuesGhostIterator<'a, K, V> {
    type V = Seq<V>;

    open spec fn view(&self) -> Seq<V> {
        self.values.take(self.pos)
    }
}

pub assume_specification<'a, K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::values ](m: &'a BTreeMap<K, V, A>) -> (values: Values<'a, K, V>)
    ensures
        ({
            let (index, s) = values@;
            &&& index == 0
            &&& forall|i: int| 0 <= i < s.len() ==> m@.values().contains(#[trigger] s[i])
            &&& s.len() == m@.len()  // length preserved
        }),
    no_unwind
;

// Iter (key-value pairs)

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub struct ExBTreeMapIter<'a, K, V>(Iter<'a, K, V>);

impl<'a, K, V> View for Iter<'a, K, V> {
    type V = (int, Seq<(K, V)>);

    uninterp spec fn view(&self) -> (int, Seq<(K, V)>);
}

pub assume_specification<'a, K: 'a, V: 'a>[ Iter::<'a, K, V>::next ](
    iter: &mut Iter<'a, K, V>,
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
                    &&& *k == old_k
                    &&& *v == old_v
                },
            }
        }),
;

pub struct BTreeMapIterGhostIterator<'a, K, V> {
    pub pos: int,
    pub kv_pairs: Seq<(K, V)>,
    pub _marker: PhantomData<&'a K>,
}

impl<'a, K, V> super::super::pervasive::ForLoopGhostIteratorNew for Iter<'a, K, V> {
    type GhostIter = BTreeMapIterGhostIterator<'a, K, V>;

    open spec fn ghost_iter(&self) -> BTreeMapIterGhostIterator<'a, K, V> {
        BTreeMapIterGhostIterator { pos: self@.0, kv_pairs: self@.1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> super::super::pervasive::ForLoopGhostIterator for BTreeMapIterGhostIterator<'a, K, V> {
    type ExecIter = Iter<'a, K, V>;
    type Item = (K, V);
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Iter<'a, K, V>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<(K, V)> {
        if 0 <= self.pos < self.kv_pairs.len() {
            Some(self.kv_pairs[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Iter<'a, K, V>) -> BTreeMapIterGhostIterator<'a, K, V> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, K, V> View for BTreeMapIterGhostIterator<'a, K, V> {
    type V = Seq<(K, V)>;

    open spec fn view(&self) -> Seq<(K, V)> {
        self.kv_pairs.take(self.pos)
    }
}

pub uninterp spec fn spec_btree_map_iter<'a, K, V, A: Allocator + Clone>(m: &'a BTreeMap<K, V, A>) -> Iter<'a, K, V>;

pub broadcast proof fn axiom_spec_iter<'a, K, V, A: Allocator + Clone>(m: &'a BTreeMap<K, V, A>)
    ensures
        ({
            let (pos, s) = #[trigger] spec_btree_map_iter(m)@;
            &&& pos == 0int
            &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] m@[s[i].0] == s[i].1
        }),
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_map_iter)]
pub assume_specification<'a, K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::iter ](m: &'a BTreeMap<K, V, A>) -> (iter: Iter<'a, K, V>)
    ensures
        ({
            let (index, s) = iter@;
            &&& index == 0
            &&& s.to_set() == m@.kv_pairs()
            &&& s.no_duplicates()
            &&& s.len() == m@.len()  // length preserved
        }),
    no_unwind
;

// IntoIter (consuming iterator)

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeMapIntoIter<K, V, A: Allocator + Clone>(IntoIter<K, V, A>);

impl<K, V, A: Allocator + Clone> View for IntoIter<K, V, A> {
    type V = (int, Seq<(K, V)>);

    uninterp spec fn view(&self) -> (int, Seq<(K, V)>);
}

pub assume_specification<K, V, A: Allocator + Clone>[ IntoIter::<K, V, A>::next ](
    iter: &mut IntoIter<K, V, A>,
) -> (r: Option<(K, V)>)
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
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& (k, v) == old_seq[old_index]
                },
            }
        }),
;

pub struct BTreeMapIntoIterGhostIterator<K, V, A: Allocator + Clone> {
    pub pos: int,
    pub kv_pairs: Seq<(K, V)>,
    pub _marker: PhantomData<A>,
}

impl<K, V, A: Allocator + Clone> super::super::pervasive::ForLoopGhostIteratorNew for IntoIter<K, V, A> {
    type GhostIter = BTreeMapIntoIterGhostIterator<K, V, A>;

    open spec fn ghost_iter(&self) -> BTreeMapIntoIterGhostIterator<K, V, A> {
        BTreeMapIntoIterGhostIterator { pos: self@.0, kv_pairs: self@.1, _marker: PhantomData }
    }
}

impl<K, V, A: Allocator + Clone> super::super::pervasive::ForLoopGhostIterator for BTreeMapIntoIterGhostIterator<K, V, A> {
    type ExecIter = IntoIter<K, V, A>;
    type Item = (K, V);
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &IntoIter<K, V, A>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<(K, V)> {
        if 0 <= self.pos < self.kv_pairs.len() {
            Some(self.kv_pairs[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &IntoIter<K, V, A>) -> BTreeMapIntoIterGhostIterator<K, V, A> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<K, V, A: Allocator + Clone> View for BTreeMapIntoIterGhostIterator<K, V, A> {
    type V = Seq<(K, V)>;

    open spec fn view(&self) -> Seq<(K, V)> {
        self.kv_pairs.take(self.pos)
    }
}

pub uninterp spec fn spec_btree_map_into_iter<K, V, A: Allocator + Clone>(m: BTreeMap<K, V, A>) -> IntoIter<K, V, A>;

pub broadcast proof fn axiom_spec_into_iter<K, V, A: Allocator + Clone>(m: BTreeMap<K, V, A>)
    ensures
        (#[trigger] spec_btree_map_into_iter(m))@.0 == 0,
        (#[trigger] spec_btree_map_into_iter(m))@.1.to_set() == m@.kv_pairs(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_map_into_iter)]
pub assume_specification<K, V, A: Allocator + Clone>[ BTreeMap::<K, V, A>::into_iter ](m: BTreeMap<K, V, A>) -> (iter: IntoIter<K, V, A>)
    ensures
        iter@.0 == 0,
        iter@.1.to_set() == m@.kv_pairs(),
        iter@.1.no_duplicates(),
        iter@.1.len() == m@.len(),  // length preserved
;

// DeepView implementation for BTreeMap

impl<K: DeepView, V: DeepView, A: Allocator + Clone> DeepView for BTreeMap<K, V, A> {
    type V = Map<K::V, V::V>;

    open spec fn deep_view(&self) -> Map<K::V, V::V> {
        btree_map_deep_view_impl(*self)
    }
}

/// The actual definition of `BTreeMap::deep_view`.
///
/// This is a separate function since it introduces a lot of quantifiers and revealing an opaque trait
/// method is not supported. In most cases, it's easier to use one of the lemmas below instead
/// of revealing this function directly.
#[verifier::opaque]
pub open spec fn btree_map_deep_view_impl<K: DeepView, V: DeepView, A: Allocator + Clone>(
    m: BTreeMap<K, V, A>,
) -> Map<K::V, V::V> {
    Map::new(
        |k: K::V|
            exists|orig_k: K| #[trigger] m@.contains_key(orig_k) && k == orig_k.deep_view(),
        |dk: K::V|
            {
                let k = choose|k: K| m@.contains_key(k) && #[trigger] k.deep_view() == dk;
                m@[k].deep_view()
            },
    )
}

pub broadcast proof fn lemma_btreemap_deepview_dom<K: DeepView, V: DeepView, A: Allocator + Clone>(m: BTreeMap<K, V, A>)
    ensures
        #[trigger] m.deep_view().dom() == m@.dom().map(|k: K| k.deep_view()),
{
    reveal(btree_map_deep_view_impl);
    broadcast use group_btree_map_axioms;
    broadcast use crate::vstd::group_vstd_default;

    assert(m.deep_view().dom() =~= m@.dom().map(|k: K| k.deep_view()));
}

pub broadcast proof fn lemma_btreemap_deepview_properties<K: DeepView, V: DeepView, A: Allocator + Clone>(m: BTreeMap<K, V, A>)
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
    broadcast use group_btree_map_axioms;
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

// Broadcast group

pub broadcast group group_btree_map_axioms {
    axiom_spec_len,
    axiom_btree_map_view_finite_dom,
    axiom_btree_contains_deref_key,
    axiom_btree_maps_deref_key_to_value,
    axiom_btree_deref_key_removed,
    axiom_spec_iter,
    axiom_spec_into_iter,
}

} // verus!
