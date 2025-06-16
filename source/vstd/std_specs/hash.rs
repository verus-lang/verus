/// This code adds specifications for the standard-library types
/// `std::collections::HashMap` and `std::collections::HashSet`.
///
/// Most of the specification only applies if you use `HashMap<Key,
/// Value>` or `HashSet<Key>`. If you use some custom build hasher,
/// e.g., with`HashMap<Key, Value, CustomBuildHasher>`, the
/// specification won't specify much.
///
/// Likewise, the specification is only meaningful when the `Key`
/// obeys our hash table model, i.e., (1) `Key::hash` is
/// deterministic and (2) any two `Key`s satisfying `==` are
/// identical. We have an axiom that all primitive types and `Box`es
/// thereof obey this model. But if you want to use some other key
/// type `MyKey`, you need to explicitly state your assumption that it
/// does so with
/// `assume(vstd::std_specs::hash::obeys_key_model::<MyKey>());`.
/// In the future, we plan to devise a way for you to prove that it
/// does so, so that you don't have to make such an assumption.
///
/// By default, the Verus standard library brings useful axioms
/// about the behavior of `HashMap` and `HashSet` into the ambient
/// reasoning context by broadcasting the group
/// `vstd::std_specs::hash::group_hash_axioms`.
use super::super::prelude::*;

use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;
use core::option::Option;
use core::option::Option::None;
use std::collections::hash_map;
use std::collections::hash_map::{DefaultHasher, Keys, RandomState, Values};
use std::collections::hash_set;
use std::collections::{HashMap, HashSet};

verus! {

// We model a `DefaultHasher` as having a view (i.e., an abstract
// state) of type `Seq<Seq<u8>>`. This reflects the sequence of write
// operations performed so far, where each write is modeled as having
// written a sequence of bytes. There's also a specification for
// how a view will be transformed by `finish` into a `u64`.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDefaultHasher(DefaultHasher);

impl View for DefaultHasher {
    type V = Seq<Seq<u8>>;

    #[verifier::external_body]
    uninterp spec fn view(&self) -> Seq<Seq<u8>>;
}

pub trait DefaultHasherAdditionalSpecFns {
    spec fn spec_finish(s: Seq<Seq<u8>>) -> u64;
}

impl DefaultHasherAdditionalSpecFns for DefaultHasher {
    #[verifier::external_body]
    uninterp spec fn spec_finish(s: Seq<Seq<u8>>) -> u64;
}

// This is the specification of behavior for `DefaultHasher::new()`.
pub assume_specification[ DefaultHasher::new ]() -> (result: DefaultHasher)
    ensures
        result@ == Seq::<Seq<u8>>::empty(),
;

// This is the specification of behavior for `DefaultHasher::write(&[u8])`.
pub assume_specification[ DefaultHasher::write ](state: &mut DefaultHasher, bytes: &[u8])
    ensures
        state@ == old(state)@.push(bytes@),
;

// This is the specification of behavior for `DefaultHasher::finish()`.
pub assume_specification[ DefaultHasher::finish ](state: &DefaultHasher) -> (result: u64)
    ensures
        result == DefaultHasher::spec_finish(state@),
;

// This function specifies whether a type obeys the requirements
// to be a key in a hash table and have that hash table conform to our
// hash-table model. The two requirements are (1) the hash function
// has to be deterministic and (2) any two elements considered equal
// by the executable `==` operator must be identical. Requirement (1)
// isn't satisfied by having `Key` implement `Hash`, since this trait
// doesn't mandate determinism.
#[verifier::external_body]
pub uninterp spec fn obeys_key_model<Key: ?Sized>() -> bool;

// These axioms state that any primitive type, or `Box` thereof,
// obeys the requirements to be a key in a hash table that
// conforms to our hash-table model.
// (Declare each separately to enable pruning of unused primitive types.)
pub broadcast proof fn axiom_bool_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<bool>(),
{
    admit();
}

pub broadcast proof fn axiom_u8_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<u8>(),
{
    admit();
}

pub broadcast proof fn axiom_u16_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<u16>(),
{
    admit();
}

pub broadcast proof fn axiom_u32_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<u32>(),
{
    admit();
}

pub broadcast proof fn axiom_u64_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<u64>(),
{
    admit();
}

pub broadcast proof fn axiom_u128_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<u128>(),
{
    admit();
}

pub broadcast proof fn axiom_usize_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<usize>(),
{
    admit();
}

pub broadcast proof fn axiom_i8_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<i8>(),
{
    admit();
}

pub broadcast proof fn axiom_i16_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<i16>(),
{
    admit();
}

pub broadcast proof fn axiom_i32_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<i32>(),
{
    admit();
}

pub broadcast proof fn axiom_i164_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<i64>(),
{
    admit();
}

pub broadcast proof fn axiom_i128_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<i128>(),
{
    admit();
}

pub broadcast proof fn axiom_isize_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<isize>(),
{
    admit();
}

pub broadcast proof fn axiom_box_bool_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<Box<bool>>(),
{
    admit();
}

pub broadcast proof fn axiom_box_integer_type_obeys_hash_table_key_model<Key: Integer + ?Sized>()
    requires
        obeys_key_model::<Key>(),
    ensures
        #[trigger] obeys_key_model::<Box<Key>>(),
{
    admit();
}

#[verifier::external_trait_specification]
pub trait ExHasher {
    type ExternalTraitSpecificationFor: Hasher;
}

// Our model for the external trait `BuildHasher` is that for any two
// `Hasher`s it builds, if they're both given the same write sequence
// then their states will match and they'll produce the same digest
// when invoked with `finish()`.
//
// We don't expect that all types implementing the `BuildHasher` trait
// will conform to our model, just the types T for which
// `builds_valid_hashers::<T>()` holds.
#[verifier::external_trait_specification]
pub trait ExBuildHasher {
    type ExternalTraitSpecificationFor: BuildHasher;

    type Hasher: Hasher;
}

#[verifier::external_body]
pub uninterp spec fn builds_valid_hashers<T: ?Sized>() -> bool;

// A commonly used type of trait `BuildHasher` is `RandomState`. We
// model that type here. In particular, we have an axiom that
// `RandomState` conforms to our model of how `BuildHasher` behaves.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRandomState(RandomState);

pub broadcast proof fn axiom_random_state_builds_valid_hashers()
    ensures
        #[trigger] builds_valid_hashers::<RandomState>(),
{
    admit();
}

// The `keys` method of a `HashMap` returns an iterator of type `Keys`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExKeys<'a, Key: 'a, Value: 'a>(Keys<'a, Key, Value>);

pub trait KeysAdditionalSpecFns<'a, Key: 'a, Value: 'a> {
    spec fn view(self: &Self) -> (int, Seq<Key>);
}

impl<'a, Key: 'a, Value: 'a> KeysAdditionalSpecFns<'a, Key, Value> for Keys<'a, Key, Value> {
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

// The `values` method of a `HashMap` returns an iterator of type `Values`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExValues<'a, Key: 'a, Value: 'a>(Values<'a, Key, Value>);

pub trait ValuesAdditionalSpecFns<'a, Key: 'a, Value: 'a> {
    spec fn view(self: &Self) -> (int, Seq<Value>);
}

impl<'a, Key: 'a, Value: 'a> ValuesAdditionalSpecFns<'a, Key, Value> for Values<'a, Key, Value> {
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

// The `iter` method of a `HashMap` returns an iterator of type `hash_map::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExMapIter<'a, Key: 'a, Value: 'a>(hash_map::Iter<'a, Key, Value>);

pub trait MapIterAdditionalSpecFns<'a, Key: 'a, Value: 'a> {
    spec fn view(self: &Self) -> (int, Seq<(Key, Value)>);
}

impl<'a, Key: 'a, Value: 'a> MapIterAdditionalSpecFns<'a, Key, Value> for hash_map::Iter<
    'a,
    Key,
    Value,
> {
    uninterp spec fn view(self: &hash_map::Iter<'a, Key, Value>) -> (int, Seq<(Key, Value)>);
}

pub assume_specification<'a, Key, Value>[ hash_map::Iter::<'a, Key, Value>::next ](
    iter: &mut hash_map::Iter<'a, Key, Value>,
) -> (r: Option<(&'a Key, &'a Value)>)
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

pub struct MapIterGhostIterator<'a, Key, Value> {
    pub pos: int,
    pub kv_pairs: Seq<(Key, Value)>,
    pub _marker: PhantomData<&'a Key>,
}

impl<'a, Key, Value> super::super::pervasive::ForLoopGhostIteratorNew for hash_map::Iter<
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
    type ExecIter = hash_map::Iter<'a, Key, Value>;

    type Item = (Key, Value);

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &hash_map::Iter<'a, Key, Value>) -> bool {
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
        _exec_iter: &hash_map::Iter<'a, Key, Value>,
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
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_hash_map_iter<'a, Key, Value, S>(m: &'a HashMap<Key, Value, S>) -> (r:
    hash_map::Iter<'a, Key, Value>);

pub broadcast proof fn axiom_spec_hash_map_iter<'a, Key, Value, S>(m: &'a HashMap<Key, Value, S>)
    ensures
        ({
            let (pos, v) = #[trigger] spec_hash_map_iter(m)@;
            &&& pos == 0int
            &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] m@[v[i].0] == v[i].1
        }),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_map_iter)]
pub assume_specification<'a, Key, Value, S>[ HashMap::<Key, Value, S>::iter ](
    m: &'a HashMap<Key, Value, S>,
) -> (iter: hash_map::Iter<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            let (index, s) = iter@;
            &&& index == 0
            &&& s.to_set() == m@.kv_pairs()
            &&& s.no_duplicates()
        },
;

// We now specify the behavior of `HashMap`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
#[verifier::reject_recursive_types(S)]
pub struct ExHashMap<Key, Value, S>(HashMap<Key, Value, S>);

pub trait HashMapAdditionalSpecFns<Key, Value>: View<V = Map<Key, Value>> {
    spec fn spec_index(&self, k: Key) -> Value
        recommends
            self@.contains_key(k),
    ;
}

impl<Key, Value, S> HashMapAdditionalSpecFns<Key, Value> for HashMap<Key, Value, S> {
    #[verifier::inline]
    open spec fn spec_index(&self, k: Key) -> Value {
        self@.index(k)
    }
}

impl<Key, Value, S> View for HashMap<Key, Value, S> {
    type V = Map<Key, Value>;

    uninterp spec fn view(&self) -> Map<Key, Value>;
}

impl<Key: DeepView, Value: DeepView, S> DeepView for HashMap<Key, Value, S> {
    type V = Map<Key::V, Value::V>;

    open spec fn deep_view(&self) -> Map<Key::V, Value::V> {
        hash_map_deep_view_impl(*self)
    }
}

/// The actual definition of `HashMap::deep_view`.
///
/// This is a separate function since it introduces a lot of quantifiers and revealing an opaque trait
/// method is not supported. In most cases, it's easier to use one of the lemmas below instead
/// of revealing this function directly.
#[verifier::opaque]
pub open spec fn hash_map_deep_view_impl<Key: DeepView, Value: DeepView, S>(
    m: HashMap<Key, Value, S>,
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

pub broadcast proof fn lemma_hashmap_deepview_dom<K: DeepView, V: DeepView>(m: HashMap<K, V>)
    ensures
        #[trigger] m.deep_view().dom() == m@.dom().map(|k: K| k.deep_view()),
{
    reveal(hash_map_deep_view_impl);
    broadcast use group_hash_axioms;
    broadcast use crate::vstd::group_vstd_default;

    assert(m.deep_view().dom() =~= m@.dom().map(|k: K| k.deep_view()));
}

pub broadcast proof fn lemma_hashmap_deepview_properties<K: DeepView, V: DeepView>(m: HashMap<K, V>)
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
    reveal(hash_map_deep_view_impl);
    broadcast use group_hash_axioms;
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

pub broadcast proof fn lemma_hashmap_deepview_values<K: DeepView, V: DeepView>(m: HashMap<K, V>)
    requires
        crate::relations::injective(|k: K| k.deep_view()),
    ensures
        #[trigger] m.deep_view().values() =~= m@.values().map(|v: V| v.deep_view()),
{
    reveal(hash_map_deep_view_impl);
    broadcast use group_hash_axioms;
    broadcast use lemma_hashmap_deepview_properties;
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
pub broadcast proof fn axiom_hashmap_deepview_borrow<
    K: DeepView + Borrow<Q>,
    V: DeepView,
    Q: View<V = <K as DeepView>::V> + Hash + Eq + ?Sized,
>(m: HashMap<K, V>, k: &Q)
    requires
        obeys_key_model::<K>(),
        crate::relations::injective(|k: K| k.deep_view()),
    ensures
        #[trigger] contains_borrowed_key(m@, k) <==> m.deep_view().contains_key(k@),
{
    admit();
}

/// A `Map` constructed from a `HashMap` is always finite.
pub broadcast proof fn axiom_hashmap_view_finite_dom<K, V>(m: HashMap<K, V>)
    ensures
        #[trigger] m@.dom().finite(),
{
    admit();
}

pub uninterp spec fn spec_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>) -> usize;

pub broadcast proof fn axiom_spec_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_map_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_map_len)]
pub assume_specification<Key, Value, S>[ HashMap::<Key, Value, S>::len ](
    m: &HashMap<Key, Value, S>,
) -> (len: usize)
    ensures
        len == spec_hash_map_len(m),
;

pub assume_specification<Key, Value, S>[ HashMap::<Key, Value, S>::is_empty ](
    m: &HashMap<Key, Value, S>,
) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<K: Clone, V: Clone, S: Clone>[ <HashMap::<K, V, S> as Clone>::clone ](
    this: &HashMap<K, V, S>,
) -> (other: HashMap<K, V, S>)
    ensures
        other@ == this@,
;

pub assume_specification<Key, Value>[ HashMap::<Key, Value>::new ]() -> (m: HashMap<
    Key,
    Value,
    RandomState,
>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<Key, Value>[ HashMap::<Key, Value>::with_capacity ](capacity: usize) -> (m:
    HashMap<Key, Value, RandomState>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher>[ HashMap::<
    Key,
    Value,
    S,
>::reserve ](m: &mut HashMap<Key, Value, S>, additional: usize)
    ensures
        m@ == old(m)@,
;

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher>[ HashMap::<Key, Value, S>::insert ](
    m: &mut HashMap<Key, Value, S>,
    k: Key,
    v: Value,
) -> (result: Option<Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
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

pub broadcast proof fn axiom_contains_deref_key<Q, Value>(m: Map<Q, Value>, k: &Q)
    ensures
        #[trigger] contains_borrowed_key::<Q, Value, Q>(m, k) <==> m.contains_key(*k),
{
    admit();
}

pub broadcast proof fn axiom_contains_box<Q, Value>(m: Map<Box<Q>, Value>, k: &Q)
    ensures
        #[trigger] contains_borrowed_key::<Box<Q>, Value, Q>(m, k) <==> m.contains_key(
            Box::new(*k),
        ),
{
    admit();
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S>::contains_key::<Q> ](m: &HashMap<Key, Value, S>, k: &Q) -> (result:
    bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> result == contains_borrowed_key(
            m@,
            k,
        ),
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

pub broadcast proof fn axiom_maps_deref_key_to_value<Q, Value>(m: Map<Q, Value>, k: &Q, v: Value)
    ensures
        #[trigger] maps_borrowed_key_to_value::<Q, Value, Q>(m, k, v) <==> m.contains_key(*k)
            && m[*k] == v,
{
    admit();
}

pub broadcast proof fn axiom_maps_box_key_to_value<Q, Value>(m: Map<Box<Q>, Value>, q: &Q, v: Value)
    ensures
        #[trigger] maps_borrowed_key_to_value::<Box<Q>, Value, Q>(m, q, v) <==> {
            let k = Box::new(*q);
            &&& m.contains_key(k)
            &&& m[k] == v
        },
{
    admit();
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S>::get::<Q> ](m: &'a HashMap<Key, Value, S>, k: &Q) -> (result: Option<
    &'a Value,
>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> match result {
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

pub broadcast proof fn axiom_deref_key_removed<Q, Value>(
    old_m: Map<Q, Value>,
    new_m: Map<Q, Value>,
    k: &Q,
)
    ensures
        #[trigger] borrowed_key_removed::<Q, Value, Q>(old_m, new_m, k) <==> new_m == old_m.remove(
            *k,
        ),
{
    admit();
}

pub broadcast proof fn axiom_box_key_removed<Q, Value>(
    old_m: Map<Box<Q>, Value>,
    new_m: Map<Box<Q>, Value>,
    q: &Q,
)
    ensures
        #[trigger] borrowed_key_removed::<Box<Q>, Value, Q>(old_m, new_m, q) <==> new_m
            == old_m.remove(Box::new(*q)),
{
    admit();
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S>::remove::<Q> ](m: &mut HashMap<Key, Value, S>, k: &Q) -> (result:
    Option<Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& borrowed_key_removed(old(m)@, m@, k)
            &&& match result {
                Some(v) => maps_borrowed_key_to_value(old(m)@, k, v),
                None => !contains_borrowed_key(old(m)@, k),
            }
        },
;

pub assume_specification<Key, Value, S>[ HashMap::<Key, Value, S>::clear ](
    m: &mut HashMap<Key, Value, S>,
)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<'a, Key, Value, S>[ HashMap::<Key, Value, S>::keys ](
    m: &'a HashMap<Key, Value, S>,
) -> (keys: Keys<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            let (index, s) = keys@;
            &&& index == 0
            &&& s.to_set() == m@.dom()
            &&& s.no_duplicates()
        },
;

pub assume_specification<'a, Key, Value, S>[ HashMap::<Key, Value, S>::values ](
    m: &'a HashMap<Key, Value, S>,
) -> (values: Values<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            let (index, s) = values@;
            &&& index == 0
            &&& s.to_set() == m@.values()
        },
;

// The `iter` method of a `HashSet` returns an iterator of type `hash_set::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
pub struct ExSetIter<'a, Key: 'a>(hash_set::Iter<'a, Key>);

pub trait SetIterAdditionalSpecFns<'a, Key: 'a> {
    spec fn view(self: &Self) -> (int, Seq<Key>);
}

impl<'a, Key: 'a> SetIterAdditionalSpecFns<'a, Key> for hash_set::Iter<'a, Key> {
    uninterp spec fn view(self: &hash_set::Iter<'a, Key>) -> (int, Seq<Key>);
}

pub assume_specification<'a, Key>[ hash_set::Iter::<'a, Key>::next ](
    elements: &mut hash_set::Iter<'a, Key>,
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

impl<'a, Key> super::super::pervasive::ForLoopGhostIteratorNew for hash_set::Iter<'a, Key> {
    type GhostIter = SetIterGhostIterator<'a, Key>;

    open spec fn ghost_iter(&self) -> SetIterGhostIterator<'a, Key> {
        SetIterGhostIterator { pos: self@.0, elements: self@.1, phantom: None }
    }
}

impl<'a, Key: 'a> super::super::pervasive::ForLoopGhostIterator for SetIterGhostIterator<'a, Key> {
    type ExecIter = hash_set::Iter<'a, Key>;

    type Item = Key;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &hash_set::Iter<'a, Key>) -> bool {
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

    open spec fn ghost_advance(&self, _exec_iter: &hash_set::Iter<'a, Key>) -> SetIterGhostIterator<
        'a,
        Key,
    > {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, Key> View for SetIterGhostIterator<'a, Key> {
    type V = Seq<Key>;

    open spec fn view(&self) -> Seq<Key> {
        self.elements.take(self.pos)
    }
}

// We now specify the behavior of `HashSet`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::reject_recursive_types(S)]
pub struct ExHashSet<Key, S>(HashSet<Key, S>);

impl<Key, S> View for HashSet<Key, S> {
    type V = Set<Key>;

    uninterp spec fn view(&self) -> Set<Key>;
}

pub uninterp spec fn spec_hash_set_len<Key, S>(m: &HashSet<Key, S>) -> usize;

pub broadcast proof fn axiom_spec_hash_set_len<Key, S>(m: &HashSet<Key, S>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_set_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_set_len)]
pub assume_specification<Key, S>[ HashSet::<Key, S>::len ](m: &HashSet<Key, S>) -> (len: usize)
    ensures
        len == spec_hash_set_len(m),
;

pub assume_specification<Key, S>[ HashSet::<Key, S>::is_empty ](m: &HashSet<Key, S>) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<Key>[ HashSet::<Key>::new ]() -> (m: HashSet<Key, RandomState>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<Key>[ HashSet::<Key>::with_capacity ](capacity: usize) -> (m: HashSet<
    Key,
    RandomState,
>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<Key: Eq + Hash, S: BuildHasher>[ HashSet::<Key, S>::reserve ](
    m: &mut HashSet<Key, S>,
    additional: usize,
)
    ensures
        m@ == old(m)@,
;

pub assume_specification<Key: Eq + Hash, S: BuildHasher>[ HashSet::<Key, S>::insert ](
    m: &mut HashSet<Key, S>,
    k: Key,
) -> (result: bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
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

pub broadcast proof fn axiom_set_contains_deref_key<Q>(m: Set<Q>, k: &Q)
    ensures
        #[trigger] set_contains_borrowed_key::<Q, Q>(m, k) <==> m.contains(*k),
{
    admit();
}

pub broadcast proof fn axiom_set_contains_box<Q>(m: Set<Box<Q>>, k: &Q)
    ensures
        #[trigger] set_contains_borrowed_key::<Box<Q>, Q>(m, k) <==> m.contains(Box::new(*k)),
{
    admit();
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S>::contains ](m: &HashSet<Key, S>, k: &Q) -> (result: bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> result
            == set_contains_borrowed_key(m@, k),
;

// The specification for `get` has a parameter `key: &Q` where you'd
// expect to find `key: &Key`. This allows for the case that `Key` can
// be borrowed as something other than `&Key`. For instance,
// `Box<u32>` can be borrowed as `&u32` and `String` can be borrowed
// as `&str`, so in those cases `Q` would be `u32` and `str`
// respectively.
// To deal with this, we have a specification function that opaquely
// specifies what it means for a returned reference to point to an
// element of a HashSet. And the postcondition of `get` says that
// its result matches the output of that specification function. (It
// also says that its result corresponds to the output of
// `contains_borrowed_key`, discussed above.) But this isn't very
// helpful by itself, since there's no body to that specification
// function. So we have special-case axioms that say what this means
// in two important circumstances: (1) `Key = Q` and (2) `Key =
// Box<Q>`.
pub uninterp spec fn sets_borrowed_key_to_key<Key, Q: ?Sized>(m: Set<Key>, k: &Q, v: &Key) -> bool;

pub broadcast proof fn axiom_set_deref_key_to_value<Q>(m: Set<Q>, k: &Q, v: &Q)
    ensures
        #[trigger] sets_borrowed_key_to_key::<Q, Q>(m, k, v) <==> m.contains(*k) && k == v,
{
    admit();
}

pub broadcast proof fn axiom_set_box_key_to_value<Q>(m: Set<Box<Q>>, q: &Q, v: &Box<Q>)
    ensures
        #[trigger] sets_borrowed_key_to_key::<Box<Q>, Q>(m, q, v) <==> (m.contains(*v) && Box::new(
            *q,
        ) == v),
{
    admit();
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S>::get::<Q> ](m: &'a HashSet<Key, S>, k: &Q) -> (result: Option<&'a Key>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> match result {
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

pub broadcast proof fn axiom_set_deref_key_removed<Q>(old_m: Set<Q>, new_m: Set<Q>, k: &Q)
    ensures
        #[trigger] sets_differ_by_borrowed_key::<Q, Q>(old_m, new_m, k) <==> new_m == old_m.remove(
            *k,
        ),
{
    admit();
}

pub broadcast proof fn axiom_set_box_key_removed<Q>(old_m: Set<Box<Q>>, new_m: Set<Box<Q>>, q: &Q)
    ensures
        #[trigger] sets_differ_by_borrowed_key::<Box<Q>, Q>(old_m, new_m, q) <==> new_m
            == old_m.remove(Box::new(*q)),
{
    admit();
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S>::remove::<Q> ](m: &mut HashSet<Key, S>, k: &Q) -> (result: bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& sets_differ_by_borrowed_key(old(m)@, m@, k)
            &&& result == set_contains_borrowed_key(old(m)@, k)
        },
;

pub assume_specification<Key, S>[ HashSet::<Key, S>::clear ](m: &mut HashSet<Key, S>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<'a, Key, S>[ HashSet::<Key, S>::iter ](m: &'a HashSet<Key, S>) -> (r:
    hash_set::Iter<'a, Key>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            let (index, s) = r@;
            &&& index == 0
            &&& s.to_set() == m@
            &&& s.no_duplicates()
        },
;

pub broadcast group group_hash_axioms {
    axiom_box_key_removed,
    axiom_contains_deref_key,
    axiom_contains_box,
    axiom_deref_key_removed,
    axiom_maps_deref_key_to_value,
    axiom_maps_box_key_to_value,
    axiom_hashmap_deepview_borrow,
    axiom_hashmap_view_finite_dom,
    axiom_bool_obeys_hash_table_key_model,
    axiom_u8_obeys_hash_table_key_model,
    axiom_u16_obeys_hash_table_key_model,
    axiom_u32_obeys_hash_table_key_model,
    axiom_u64_obeys_hash_table_key_model,
    axiom_u128_obeys_hash_table_key_model,
    axiom_usize_obeys_hash_table_key_model,
    axiom_i8_obeys_hash_table_key_model,
    axiom_i16_obeys_hash_table_key_model,
    axiom_i32_obeys_hash_table_key_model,
    axiom_i164_obeys_hash_table_key_model,
    axiom_i128_obeys_hash_table_key_model,
    axiom_isize_obeys_hash_table_key_model,
    axiom_box_bool_obeys_hash_table_key_model,
    axiom_box_integer_type_obeys_hash_table_key_model,
    axiom_random_state_builds_valid_hashers,
    axiom_spec_hash_map_len,
    axiom_set_box_key_removed,
    axiom_set_contains_deref_key,
    axiom_set_contains_box,
    axiom_set_deref_key_removed,
    axiom_set_deref_key_to_value,
    axiom_set_box_key_to_value,
    axiom_spec_hash_set_len,
    axiom_spec_hash_map_iter,
}

} // verus!
