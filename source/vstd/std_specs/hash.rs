//! This code adds specifications for the standard-library types
//! `std::collections::HashMap` and `std::collections::HashSet`.
//!
//! Most of the specification only applies if you use `HashMap<Key,
//! Value>` or `HashSet<Key>`. If you use some custom build hasher,
//! e.g., with`HashMap<Key, Value, CustomBuildHasher>`, the
//! specification won't specify much unless you assume
//! [`builds_valid_hashers<CustomBuildHasher>()`].
//!
//! Likewise, the specification is only meaningful when `eq_spec`
//! faithfully models executable equality, executable equality is
//! reflexive, symmetric, and transitive; hashing is
//! deterministic; executable-equal keys hash identically; and
//! cloning, when supported, preserves structural identity and
//! executable equality. We have an axiom that all primitive types and
//! `Box`es thereof obey this model. But if you want to use some other
//! key type `MyKey`, you need to explicitly state your assumption
//! that it does so with
//! `assume(vstd::std_specs::hash::obeys_key_model::<MyKey>());`. In
//! the future, we plan to devise a way for you to prove that it does
//! so, so that you don't have to make such an assumption.
//!
//! Insertion and borrowed-key operations' contracts use `eq_spec`,
//! without identifying equality with structural equality. Broadcast
//! lemmas provide structural- and deep-equality special cases.
//!
//! Borrowed-key lookups also require
//! `borrowed_key_hashing_matches::<Key, Q>()` and use the model in
//! `BorrowSpec`. Their postconditions additionally require `Q` to obey
//! the hashing and equality models. Compatibility is supplied for identity,
//! reference, `Box`, and `String` borrowing.
//!
//! By default, the Verus standard library brings useful axioms
//! about the behavior of `HashMap` and `HashSet` into the ambient
//! reasoning context by broadcasting the group
//! `vstd::std_specs::hash::group_hash_axioms`.
use super::super::map::{assert_maps_equal, assert_maps_equal_internal};
use super::super::prelude::*;
use super::borrow::BorrowSpec;
use super::cmp::{PartialEqSpec, eq_matches_deep_equality, eq_matches_equality};
use super::iter::IteratorSpec;

use core::alloc::Allocator;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;
use core::option::Option;
use core::option::Option::None;
use std::collections::hash_map;
use std::collections::hash_map::{
    DefaultHasher, Entry, Keys, OccupiedEntry, RandomState, VacantEntry, Values,
};
use std::collections::hash_set;
use std::collections::{HashMap, HashSet};

verus! {

/// Specifications for the behavior of
/// [`std::collections::hash_map::DefaultHasher`](https://doc.rust-lang.org/std/collections/hash_map/struct.DefaultHasher.html).
///
/// We model a `DefaultHasher` as having a view (i.e., an abstract
/// state) of type `Seq<Seq<u8>>`. This reflects the sequence of write
/// operations performed so far, where each write is modeled as having
/// written a sequence of bytes. There's also a specification for
/// how a view will be transformed by `finish` into a `u64`.
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
        final(state)@ == old(state)@.push(bytes@),
;

// This is the specification of behavior for `DefaultHasher::finish()`.
pub assume_specification[ DefaultHasher::finish ](state: &DefaultHasher) -> (result: u64)
    ensures
        result == DefaultHasher::spec_finish(state@),
;

/// Specifies whether a type `Key` conforms to our requirements to be
/// a key in our hash table (and hash set) model.
///
/// These requirements are that (1)
/// `<Key as PartialEqSpec>::obeys_eq_spec()` is true and executable
/// equality is reflexive, symmetric, and transitive; (2) the hash
/// function is deterministic; (3) executable-equal keys have equal
/// hashes; and (4) if `Key` implements `Clone`, cloning produces a
/// result structurally identical and executable-equal to its input.
/// `Key` need not implement `Clone`. Requirement (2) isn't satisfied
/// by having `Key` implement `Hash`, since this trait doesn't mandate
/// determinism.
///
/// The standard library has axioms that all primitive types and `Box`es
/// thereof obey this model. If you want to use some other key
/// type `MyKey`, you need to explicitly state your assumption that it
/// does so with
/// `assume(vstd::std_specs::hash::obeys_key_model::<MyKey>())`.
/// In the future, we plan to devise a way for you to prove that it
/// does so, so that you don't have to make such an assumption.
#[verifier::external_body]
pub uninterp spec fn obeys_key_model<Key: ?Sized>() -> bool;

/// The key model supplies faithful equality and equivalence laws, including for unsized keys.
pub broadcast axiom fn axiom_key_model_implies_obeys_eq<Key: Hash + Eq + ?Sized>()
    requires
        #[trigger] obeys_key_model::<Key>(),
    ensures
        <Key as PartialEqSpec>::obeys_eq_spec(),
        forall|a: &Key| #[trigger] a.eq_spec(a),
        forall|a: &Key, b: &Key| #[trigger] a.eq_spec(b) <==> b.eq_spec(a),
        forall|a: &Key, b: &Key, c: &Key|
            a.eq_spec(b) && #[trigger] b.eq_spec(c) ==> #[trigger] a.eq_spec(c),
;

pub broadcast proof fn lemma_key_model_implies_obeys_eq<Key: Hash + Eq>()
    requires
        #[trigger] obeys_key_model::<Key>(),
    ensures
        crate::laws_eq::obeys_eq::<Key>(),
{
    broadcast use axiom_key_model_implies_obeys_eq;

    reveal(crate::laws_eq::obeys_eq_spec_properties);
}

/// Whether borrowing a key preserves its `Hash` and `Eq` behavior.
///
/// Owned keys and their borrowed forms must hash identically for any
/// hasher and compare equal in the same circumstances. This predicate
/// is opaque because `Hash` does not yet have a specification model.
pub uninterp spec fn borrowed_key_hashing_matches<
    Key: Borrow<Q> + Hash + Eq + ?Sized,
    Q: Hash + Eq + ?Sized,
>() -> bool;

pub broadcast axiom fn axiom_borrowed_key_hashing_matches_self<Q: Hash + Eq + ?Sized>()
    ensures
        #[trigger] borrowed_key_hashing_matches::<Q, Q>(),
;

pub broadcast axiom fn axiom_borrowed_key_hashing_matches_ref<Q: Hash + Eq + ?Sized>()
    ensures
        #[trigger] borrowed_key_hashing_matches::<&Q, Q>(),
;

pub broadcast axiom fn axiom_borrowed_key_hashing_matches_box<Q: Hash + Eq + ?Sized, A: Allocator>()
    ensures
        #[trigger] borrowed_key_hashing_matches::<Box<Q, A>, Q>(),
;

pub broadcast axiom fn axiom_borrowed_key_hashing_matches_string()
    ensures
        #[trigger] borrowed_key_hashing_matches::<String, str>(),
;

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

pub broadcast proof fn axiom_i64_obeys_hash_table_key_model()
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

/// Specifies whether a type conforms to our requirements to be a hash builder
/// in our hash table (and hash set) model.
///
/// Our model requires that for any two `Hasher`s that the `BuildHasher` builds,
/// if they're both given the same write sequence
/// then their states will match and they'll produce the same digest
/// when invoked with `finish()`.
///
/// The standard library has an axiom that `RandomState`, the default `BuildHasher`
/// used by `HashMap` and `HashSet`, implements this model.
/// If you want to use some other hash builder type `MyHashBuilder`,
/// you need to explicitly state your assumption that it does so with
/// `assume(vstd::std_specs::hash::builds_valid_hashers::<MyHashBuilder>())`.
#[verifier::external_body]
pub uninterp spec fn builds_valid_hashers<T: ?Sized>() -> bool;

/// Specifications for the behavior of
/// [`std::hash::RandomState`](https://doc.rust-lang.org/std/hash/struct.RandomState.html).
///
/// `RandomState` is the default `BuildHasher` used by Rust's `HashMap` and `HashSet` implementations.
/// We have an axiom that `RandomState` satisfies [`builds_valid_hashers()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.builds_valid_hashers.html)
/// and thereby conforms to our model of how `BuildHasher` behaves.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRandomState(RandomState);

pub broadcast proof fn axiom_random_state_builds_valid_hashers()
    ensures
        #[trigger] builds_valid_hashers::<RandomState>(),
{
    admit();
}

/// Specifications for the behavior of
/// [`std::collections::hash_map::Keys`](https://doc.rust-lang.org/std/collections/hash_map/struct.Keys.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExKeys<'a, Key: 'a, Value: 'a>(Keys<'a, Key, Value>);

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
/// [`std::collections::hash_map::Values`](https://doc.rust-lang.org/std/collections/hash_map/struct.Values.html).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExValues<'a, Key: 'a, Value: 'a>(Values<'a, Key, Value>);

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

// The `iter` method of a `HashMap` returns an iterator of type `hash_map::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
pub struct ExMapIter<'a, Key: 'a, Value: 'a>(hash_map::Iter<'a, Key, Value>);

// To allow reasoning about the "contents" of the Iter iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original map.
pub uninterp spec fn into_iter<'a, Key, Value>(i: hash_map::Iter<'a, Key, Value>) -> Seq<
    (Key, Value),
>;

impl<'a, K, V> super::iter::IteratorSpecImpl for hash_map::Iter<'a, K, V> {
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

pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::iter ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (iter: hash_map::Iter<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
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
        },
;

/// Specifications for the behavior of [`std::collections::HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html).
///
/// We model a `HashMap` as having a view of type `Map<Key, Value>`, which reflects the current state of the map.
///
/// These specifications are only meaningful if `obeys_key_model::<Key>()` and `builds_valid_hashers::<S>()` hold.
/// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
/// for information on use with primitive types and other types,
/// and see [`builds_valid_hashers()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.builds_valid_hashers.html)
/// for information on use with Rust's default implementation and custom implementations.
///
/// Axioms about the behavior of HashMap are present in the broadcast group `vstd::std_specs::hash::group_hash_axioms`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::accept_recursive_types(Value)]
#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(A)]
pub struct ExHashMap<Key, Value, S, A: Allocator>(HashMap<Key, Value, S, A>);

pub trait HashMapAdditionalSpecFns<Key, Value>: View<V = Map<Key, Value>> {
    spec fn spec_index(&self, k: Key) -> Value
        recommends
            self@.contains_key(k),
    ;
}

impl<Key, Value, S, A: Allocator> HashMapAdditionalSpecFns<Key, Value> for HashMap<
    Key,
    Value,
    S,
    A,
> {
    #[verifier::inline]
    open spec fn spec_index(&self, k: Key) -> Value {
        self@.index(k)
    }
}

/// The actual definition of `HashMap::deep_view`.
///
/// This is a separate function since it introduces a lot of quantifiers and revealing an opaque trait
/// method is not supported. In most cases, it's easier to use one of the lemmas below instead
/// of revealing this function directly.
#[verifier::opaque]
pub open spec fn hash_map_deep_view_impl<
    Key: DeepView,
    Value: DeepView,
    S,
    A: core::alloc::Allocator,
>(m: HashMap<Key, Value, S, A>) -> Map<Key::V, Value::V> {
    Map::new(
        m@.dom().map(|k: Key| k.deep_view()),
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

    lemma_hashmap_deepview_dom(m);
    assert(m.deep_view().dom() == m@.dom().map(|k: K| k.deep_view()));
    assert forall|k: K| #[trigger] m@.contains_key(k) implies m.deep_view().contains_key(
        k.deep_view(),
    ) && m.deep_view()[k.deep_view()] == m@[k].deep_view() by {
        assert(m@.dom().contains(k));
        assert(m@.dom().map(|k: K| k.deep_view()).contains(k.deep_view()));
        assert(m.deep_view().dom().contains(k.deep_view()));
        let k2 = choose|k2: K| m@.contains_key(k2) && #[trigger] k2.deep_view() == k.deep_view();
        assert forall|k1: K, k2: K| #[trigger]
            k1.deep_view() == #[trigger] k2.deep_view() implies k1 == k2 by {
            let ghost k_deepview = |k: K| k.deep_view();
            assert(crate::relations::injective(k_deepview));
            assert(k_deepview(k1) == k_deepview(k2));
        }
        assert(k2 == k);
    }
    assert forall|dk: K::V| #[trigger] m.deep_view().contains_key(dk) implies exists|k: K|
        k.deep_view() == dk && #[trigger] m@.contains_key(k) by {
        assert(m.deep_view().dom().contains(dk));
        assert(m@.dom().map(|k: K| k.deep_view()).contains(dk));
        let k = choose|k: K| #[trigger] m@.dom().contains(k) && k.deep_view() == dk;
        assert(m@.contains_key(k));
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

pub uninterp spec fn spec_hash_map_len<Key, Value, S, A: Allocator>(
    m: &HashMap<Key, Value, S, A>,
) -> usize;

pub broadcast proof fn axiom_spec_hash_map_len<Key, Value, S, A: Allocator>(
    m: &HashMap<Key, Value, S, A>,
)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_map_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_map_len)]
pub assume_specification<Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::len ](
    m: &HashMap<Key, Value, S, A>,
) -> (len: usize)
    ensures
        len == spec_hash_map_len(m),
;

pub assume_specification<Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::capacity ](
    m: &HashMap<Key, Value, S, A>,
) -> (cap: usize)
    ensures
        cap >= spec_hash_map_len(m),
;

pub assume_specification<Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::is_empty ](
    m: &HashMap<Key, Value, S, A>,
) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<K: Clone, V: Clone, S: Clone, A: Allocator + Clone>[ <HashMap::<
    K,
    V,
    S,
    A,
> as Clone>::clone ](this: &HashMap<K, V, S, A>) -> (other: HashMap<K, V, S, A>)
    ensures
        other@.dom() == this@.dom(),
        forall|key|
            #![trigger other@.dom().contains(key)]
            other@.dom().contains(key) ==> cloned(this@[key], #[trigger] other@[key]),
;

pub assume_specification<Key, Value>[ HashMap::<Key, Value>::new ]() -> (m: HashMap<
    Key,
    Value,
    RandomState,
>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<K, V, S: core::default::Default>[ <HashMap<
    K,
    V,
    S,
> as core::default::Default>::default ]() -> (m: HashMap<K, V, S>)
    ensures
        m@ == Map::<K, V>::empty(),
;

pub assume_specification<Key, Value>[ HashMap::<Key, Value>::with_capacity ](capacity: usize) -> (m:
    HashMap<Key, Value, RandomState>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<Key, Value, S>[ HashMap::<Key, Value, S>::with_hasher ](
    hash_builder: S,
) -> (m: HashMap<Key, Value, S>)
    ensures
        m@ == Map::<Key, Value>::empty(),
;

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher, A: Allocator>[ HashMap::<
    Key,
    Value,
    S,
    A,
>::reserve ](m: &mut HashMap<Key, Value, S, A>, additional: usize)
    ensures
        final(m)@ == old(m)@,
;

pub open spec fn hash_map_keys_differ<Key: Eq + Hash, Value, S, A: Allocator>(
    m: &HashMap<Key, Value, S, A>,
) -> bool {
    forall|k1: Key, k2: Key|
        {
            &&& #[trigger] m@.contains_key(k1)
            &&& #[trigger] m@.contains_key(k2)
            &&& k1 != k2
        } ==> !k1.eq_spec(&k2)
}

pub open spec fn hash_map_insert_ensures<Key: Eq + Hash, Value, S: BuildHasher, A: Allocator>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& builds_valid_hashers::<S>()
    }) ==> {
        &&& hash_map_keys_differ(old_m)
        &&& hash_map_keys_differ(final_m)
        &&& match result {
            Some(old_value) => exists|stored_key: Key|
                {
                    &&& #[trigger] old_m@.contains_key(stored_key)
                    &&& k.eq_spec(&stored_key)
                    &&& old_value == old_m@[stored_key]
                    &&& final_m@ == old_m@.insert(stored_key, v)
                },
            None => {
                &&& forall|stored_key: Key| #[trigger]
                    old_m@.contains_key(stored_key) ==> !k.eq_spec(&stored_key)
                &&& final_m@ == old_m@.insert(k, v)
            },
        }
    }
}

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher, A: Allocator>[ HashMap::<
    Key,
    Value,
    S,
    A,
>::insert ](m: &mut HashMap<Key, Value, S, A>, k: Key, v: Value) -> (result: Option<Value>)
    ensures
        hash_map_insert_ensures(old(m), final(m), k, v, result),
;

pub broadcast proof fn lemma_hash_map_insert_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    Value,
    S: BuildHasher,
    A: Allocator,
>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_map_insert_ensures(old_m, final_m, k, v, result),
    ensures
        final_m@ == old_m@.insert(k, v),
        match result {
            Some(old_value) => old_m@.contains_key(k) && old_value == old_m@[k],
            None => !old_m@.contains_key(k),
        },
{
}

pub broadcast proof fn lemma_hash_map_insert_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    Value: DeepView,
    S: BuildHasher,
    A: Allocator,
>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: Key,
    v: Value,
    result: Option<Value>,
)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_map_insert_ensures(old_m, final_m, k, v, result),
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

    reveal(hash_map_deep_view_impl);

    let stored_key = match result {
        Some(old_value) => choose|stored_key: Key|
            {
                &&& #[trigger] old_m@.contains_key(stored_key)
                &&& k.eq_spec(&stored_key)
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

pub open spec fn hash_map_contains_key_ensures<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(m: &HashMap<Key, Value, S, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_map_keys_differ(m)
        &&& result == exists|key: Key|
            {
                &&& #[trigger] m@.contains_key(key)
                &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
            }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::contains_key::<Q> ](
    m: &HashMap<Key, Value, S, A>,
    k: &Q,
) -> (result: bool)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_map_contains_key_ensures(m, k, result),
;

pub broadcast proof fn lemma_hash_map_contains_key_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    Value,
    S: BuildHasher,
    A: Allocator,
>(m: &HashMap<Key, Value, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_map_contains_key_ensures(m, k, result),
    ensures
        result == m@.contains_key(*k),
{
}

pub broadcast proof fn lemma_hash_map_contains_key_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    Value: DeepView,
    S: BuildHasher,
    A: Allocator,
>(m: &HashMap<Key, Value, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_map_contains_key_ensures(m, k, result),
    ensures
        result == m.deep_view().contains_key(k.deep_view()),
{
    broadcast use {
        crate::map::group_map_lemmas,
        crate::set::group_set_lemmas,
        Set::lemma_map_contains,
    };

    reveal(hash_map_deep_view_impl);

    if result {
        let key = choose|key: Key|
            {
                &&& #[trigger] m@.contains_key(key)
                &&& k.eq_spec(&key)
            };
        assert(m.deep_view().contains_key(key.deep_view()));
    }
    if m.deep_view().contains_key(k.deep_view()) {
        let key = choose|key: Key|
            m@.contains_key(key) && #[trigger] key.deep_view() == k.deep_view();
        assert(k.eq_spec(&key));
    }
}

pub open spec fn hash_map_get_ensures<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(m: &HashMap<Key, Value, S, A>, k: &Q, result: Option<&Value>) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_map_keys_differ(m)
        &&& match result {
            Some(v) => exists|key: Key|
                {
                    &&& #[trigger] m@.contains_key(key)
                    &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
                    &&& m@[key] == *v
                },
            None => forall|key: Key| #[trigger]
                m@.contains_key(key) ==> !k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)),
        }
    }
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::get::<Q> ](m: &'a HashMap<Key, Value, S, A>, k: &Q) -> (result:
    Option<&'a Value>)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_map_get_ensures(m, k, result),
;

pub broadcast proof fn lemma_hash_map_get_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    Value,
    S: BuildHasher,
    A: Allocator,
>(m: &HashMap<Key, Value, S, A>, k: &Key, result: Option<&Value>)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_map_get_ensures(m, k, result),
    ensures
        match result {
            Some(v) => m@.contains_key(*k) && *v == m@[*k],
            None => !m@.contains_key(*k),
        },
{
}

pub broadcast proof fn lemma_hash_map_get_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    Value: DeepView,
    S: BuildHasher,
    A: Allocator,
>(m: &HashMap<Key, Value, S, A>, k: &Key, result: Option<&Value>)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_map_get_ensures(m, k, result),
    ensures
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

    reveal(hash_map_deep_view_impl);

    match result {
        Some(v) => {
            let stored_key = choose|key: Key|
                {
                    &&& #[trigger] m@.contains_key(key)
                    &&& k.eq_spec(&key)
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
                assert(k.eq_spec(&key));
            }
        },
    }
}

pub open spec fn hash_map_remove_ensures<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: &Q,
    result: Option<Value>,
) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_map_keys_differ(old_m)
        &&& hash_map_keys_differ(final_m)
        &&& match result {
            Some(v) => exists|key: Key|
                {
                    &&& #[trigger] old_m@.contains_key(key)
                    &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
                    &&& old_m@[key] == v
                    &&& final_m@ == old_m@.remove(key)
                },
            None => {
                &&& forall|key: Key| #[trigger]
                    old_m@.contains_key(key) ==> !k.eq_spec(
                        <Key as BorrowSpec<Q>>::spec_borrow(&key),
                    )
                &&& final_m@ == old_m@
            },
        }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    Value,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::remove::<Q> ](m: &mut HashMap<Key, Value, S, A>, k: &Q) -> (result:
    Option<Value>)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_map_remove_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_hash_map_remove_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    Value,
    S: BuildHasher,
    A: Allocator,
>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: &Key,
    result: Option<Value>,
)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_map_remove_ensures(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.remove(*k),
        match result {
            Some(v) => old_m@.contains_key(*k) && v == old_m@[*k],
            None => !old_m@.contains_key(*k),
        },
{
    broadcast use {crate::map::group_map_lemmas, crate::set::group_set_lemmas};

    if result is None {
        assert(!old_m@.contains_key(*k));
        assert(old_m@.remove(*k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_hash_map_remove_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    Value: DeepView,
    S: BuildHasher,
    A: Allocator,
>(
    old_m: &HashMap<Key, Value, S, A>,
    final_m: &HashMap<Key, Value, S, A>,
    k: &Key,
    result: Option<Value>,
)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_map_remove_ensures(old_m, final_m, k, result),
    ensures
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

    reveal(hash_map_deep_view_impl);

    let stored_key = match result {
        Some(v) => choose|key: Key|
            {
                &&& #[trigger] old_m@.contains_key(key)
                &&& k.eq_spec(&key)
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
                assert(k.eq_spec(&key));
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

pub assume_specification<Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::clear ](
    m: &mut HashMap<Key, Value, S, A>,
)
    ensures
        final(m)@ == Map::<Key, Value>::empty(),
;

pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::keys ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (keys: Keys<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& IteratorSpec::remaining(&keys).unref().to_set() == m@.dom()
            &&& IteratorSpec::remaining(&keys).no_duplicates()
            &&& IteratorSpec::remaining(&keys).len() == m@.dom().len()
            &&& into_iter_keys(keys) == IteratorSpec::remaining(&keys).unref()
            &&& IteratorSpec::decrease(&keys) is Some
        },
;

pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::values ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (values: Values<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& IteratorSpec::remaining(&values).unref().to_set() == m@.values()
            &&& IteratorSpec::remaining(&values).len() == m@.dom().len()
            &&& into_iter_values(values) == IteratorSpec::remaining(&values).unref()
            &&& IteratorSpec::decrease(&values) is Some
        },
;

pub broadcast proof fn axiom_hashmap_decreases<Key, Value, S>(m: HashMap<Key, Value, S>)
    ensures
        #[trigger] (decreases_to!(m => m@)),
{
    admit();
}

// The `iter` method of a `HashSet` returns an iterator of type `hash_set::Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
pub struct ExSetIter<'a, Key: 'a>(hash_set::Iter<'a, Key>);

// To allow reasoning about the "contents" of the HashSet iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original keys.
pub uninterp spec fn into_iter_hash_keys<'a, Key>(i: hash_set::Iter::<'a, Key>) -> Seq<Key>;

impl<'a, K> super::iter::IteratorSpecImpl for hash_set::Iter::<'a, K> {
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
        if 0 <= index < into_iter_hash_keys(*self).len() {
            Some(&into_iter_hash_keys(*self)[index])
        } else {
            None
        }
    }
}

/// Specifications for the behavior of [`std::collections::HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html).
///
/// We model a `HashSet` as having a view of type `Set<Key>`, which reflects the current state of the set.
///
/// These specifications are only meaningful if `obeys_key_model::<Key>()` and `builds_valid_hashers::<S>()` hold.
/// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
/// for information on use with primitive types and custom types,
/// and see [`builds_valid_hashers()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.builds_valid_hashers.html)
/// for information on use with Rust's default implementation and custom implementations.
///
/// Axioms about the behavior of HashSet are present in the broadcast group `vstd::std_specs::hash::group_hash_axioms`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(Key)]
#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(A)]
pub struct ExHashSet<Key, S, A: Allocator>(HashSet<Key, S, A>);

pub uninterp spec fn spec_hash_set_len<Key, S, A: Allocator>(m: &HashSet<Key, S, A>) -> usize;

pub broadcast proof fn axiom_spec_hash_set_len<Key, S, A: Allocator>(m: &HashSet<Key, S, A>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_set_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_set_len)]
pub assume_specification<Key, S, A: Allocator>[ HashSet::<Key, S, A>::len ](
    m: &HashSet<Key, S, A>,
) -> (len: usize)
    ensures
        len == spec_hash_set_len(m),
;

pub assume_specification<Key, S, A: Allocator>[ HashSet::<Key, S, A>::is_empty ](
    m: &HashSet<Key, S, A>,
) -> (res: bool)
    ensures
        res == m@.is_empty(),
;

pub assume_specification<Key>[ HashSet::<Key>::new ]() -> (m: HashSet<Key, RandomState>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<T, S: core::default::Default>[ <HashSet<
    T,
    S,
> as core::default::Default>::default ]() -> (m: HashSet<T, S>)
    ensures
        m@ == Set::<T>::empty(),
;

pub assume_specification<Key>[ HashSet::<Key>::with_capacity ](capacity: usize) -> (m: HashSet<
    Key,
    RandomState,
>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<Key, S>[ HashSet::<Key, S>::with_hasher ](hash_builder: S) -> (m: HashSet<
    Key,
    S,
>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<Key, S>[ HashSet::<Key, S>::with_capacity_and_hasher ](
    capacity: usize,
    hash_builder: S,
) -> (m: HashSet<Key, S>)
    ensures
        m@ == Set::<Key>::empty(),
;

pub assume_specification<Key: Eq + Hash, S: BuildHasher, A: Allocator>[ HashSet::<
    Key,
    S,
    A,
>::reserve ](m: &mut HashSet<Key, S, A>, additional: usize)
    ensures
        final(m)@ == old(m)@,
;

pub open spec fn hash_set_elements_differ<Key: Eq + Hash, S, A: Allocator>(
    m: &HashSet<Key, S, A>,
) -> bool {
    forall|k1: Key, k2: Key|
        {
            &&& #[trigger] m@.contains(k1)
            &&& #[trigger] m@.contains(k2)
            &&& k1 != k2
        } ==> !k1.eq_spec(&k2)
}

pub open spec fn hash_set_insert_ensures<Key: Eq + Hash, S: BuildHasher, A: Allocator>(
    old_m: &HashSet<Key, S, A>,
    final_m: &HashSet<Key, S, A>,
    k: Key,
    result: bool,
) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& builds_valid_hashers::<S>()
    }) ==> {
        &&& hash_set_elements_differ(old_m)
        &&& hash_set_elements_differ(final_m)
        &&& if result {
            &&& forall|stored_key: Key| #[trigger]
                old_m@.contains(stored_key) ==> !k.eq_spec(&stored_key)
            &&& final_m@ == old_m@.insert(k)
        } else {
            &&& exists|stored_key: Key| #[trigger]
                old_m@.contains(stored_key) && k.eq_spec(&stored_key)
            &&& final_m@ == old_m@
        }
    }
}

pub assume_specification<Key: Eq + Hash, S: BuildHasher, A: Allocator>[ HashSet::<
    Key,
    S,
    A,
>::insert ](m: &mut HashSet<Key, S, A>, k: Key) -> (result: bool)
    ensures
        hash_set_insert_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_hash_set_insert_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
>(old_m: &HashSet<Key, S, A>, final_m: &HashSet<Key, S, A>, k: Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_set_insert_ensures(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.insert(k),
        result == !old_m@.contains(k),
{
    broadcast use crate::set::group_set_lemmas;

    assert(k.eq_spec(&k));
    if !result {
        assert(old_m@.contains(k));
        assert(old_m@.insert(k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_hash_set_insert_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    S: BuildHasher,
    A: Allocator,
>(old_m: &HashSet<Key, S, A>, final_m: &HashSet<Key, S, A>, k: Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_set_insert_ensures(old_m, final_m, k, result),
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
                assert(k.eq_spec(&stored_key));
            }
        }
    } else {
        let stored_key = choose|stored_key: Key| #[trigger]
            old_m@.contains(stored_key) && k.eq_spec(&stored_key);
        assert(stored_key.deep_view() == k.deep_view());
        assert(old_m.deep_view().contains(k.deep_view()));
    }
    assert(final_m.deep_view() =~= old_m.deep_view().insert(k.deep_view()));
}

pub open spec fn hash_set_contains_ensures<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(m: &HashSet<Key, S, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_set_elements_differ(m)
        &&& result == exists|key: Key|
            {
                &&& #[trigger] m@.contains(key)
                &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
            }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::contains ](m: &HashSet<Key, S, A>, k: &Q) -> (result: bool)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_set_contains_ensures(m, k, result),
;

pub broadcast proof fn lemma_hash_set_contains_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
>(m: &HashSet<Key, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_set_contains_ensures(m, k, result),
    ensures
        result == m@.contains(*k),
{
}

pub broadcast proof fn lemma_hash_set_contains_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    S: BuildHasher,
    A: Allocator,
>(m: &HashSet<Key, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_set_contains_ensures(m, k, result),
    ensures
        result == m.deep_view().contains(k.deep_view()),
{
    broadcast use {crate::set::group_set_lemmas, Set::lemma_map_contains};

    if result {
        let key = choose|key: Key| #[trigger] m@.contains(key) && k.eq_spec(&key);
        assert(m.deep_view().contains(key.deep_view()));
    }
    if m.deep_view().contains(k.deep_view()) {
        let key = choose|key: Key| m@.contains(key) && #[trigger] key.deep_view() == k.deep_view();
        assert(k.eq_spec(&key));
    }
}

pub open spec fn hash_set_get_ensures<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(m: &HashSet<Key, S, A>, k: &Q, result: Option<&Key>) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_set_elements_differ(m)
        &&& match result {
            Some(key) => {
                &&& m@.contains(*key)
                &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(key))
            },
            None => forall|key: Key| #[trigger]
                m@.contains(key) ==> !k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key)),
        }
    }
}

pub assume_specification<
    'a,
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::get::<Q> ](m: &'a HashSet<Key, S, A>, k: &Q) -> (result: Option<&'a Key>)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_set_get_ensures(m, k, result),
;

pub broadcast proof fn lemma_hash_set_get_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
>(m: &HashSet<Key, S, A>, k: &Key, result: Option<&Key>)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_set_get_ensures(m, k, result),
    ensures
        match result {
            Some(key) => m@.contains(*key) && *key == *k,
            None => !m@.contains(*k),
        },
{
}

pub broadcast proof fn lemma_hash_set_get_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    S: BuildHasher,
    A: Allocator,
>(m: &HashSet<Key, S, A>, k: &Key, result: Option<&Key>)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_set_get_ensures(m, k, result),
    ensures
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

    match result {
        Some(key) => {
            assert(m.deep_view().contains(key.deep_view()));
        },
        None => {
            if m.deep_view().contains(k.deep_view()) {
                let key = choose|key: Key|
                    m@.contains(key) && #[trigger] key.deep_view() == k.deep_view();
                assert(k.eq_spec(&key));
            }
        },
    }
}

pub open spec fn hash_set_remove_ensures<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>(old_m: &HashSet<Key, S, A>, final_m: &HashSet<Key, S, A>, k: &Q, result: bool) -> bool {
    ({
        &&& obeys_key_model::<Key>()
        &&& obeys_key_model::<Q>()
        &&& builds_valid_hashers::<S>()
        &&& <Key as BorrowSpec<Q>>::obeys_borrow_spec()
    }) ==> {
        &&& hash_set_elements_differ(old_m)
        &&& hash_set_elements_differ(final_m)
        &&& if result {
            exists|key: Key|
                {
                    &&& #[trigger] old_m@.contains(key)
                    &&& k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
                    &&& final_m@ == old_m@.remove(key)
                }
        } else {
            &&& forall|key: Key| #[trigger]
                old_m@.contains(key) ==> !k.eq_spec(<Key as BorrowSpec<Q>>::spec_borrow(&key))
            &&& final_m@ == old_m@
        }
    }
}

pub assume_specification<
    Key: Borrow<Q> + Hash + Eq,
    S: BuildHasher,
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::remove::<Q> ](m: &mut HashSet<Key, S, A>, k: &Q) -> (result: bool)
    requires
        borrowed_key_hashing_matches::<Key, Q>(),
    ensures
        hash_set_remove_ensures(old(m), final(m), k, result),
;

pub broadcast proof fn lemma_hash_set_remove_ensures_if_eq_matches_equality<
    Key: Eq + Hash,
    S: BuildHasher,
    A: Allocator,
>(old_m: &HashSet<Key, S, A>, final_m: &HashSet<Key, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_equality::<Key>(),
        #[trigger] hash_set_remove_ensures(old_m, final_m, k, result),
    ensures
        final_m@ == old_m@.remove(*k),
        result == old_m@.contains(*k),
{
    broadcast use crate::set::group_set_lemmas;

    if !result {
        assert(!old_m@.contains(*k));
        assert(old_m@.remove(*k) =~= old_m@);
    }
}

pub broadcast proof fn lemma_hash_set_remove_ensures_if_eq_matches_deep_equality<
    Key: Eq + Hash + DeepView,
    S: BuildHasher,
    A: Allocator,
>(old_m: &HashSet<Key, S, A>, final_m: &HashSet<Key, S, A>, k: &Key, result: bool)
    requires
        obeys_key_model::<Key>(),
        builds_valid_hashers::<S>(),
        eq_matches_deep_equality::<Key>(),
        #[trigger] hash_set_remove_ensures(old_m, final_m, k, result),
    ensures
        final_m.deep_view() == old_m.deep_view().remove(k.deep_view()),
        result == old_m.deep_view().contains(k.deep_view()),
{
    broadcast use {crate::set::group_set_lemmas, Set::lemma_map_contains};

    let stored_key = if result {
        choose|key: Key|
            {
                &&& #[trigger] old_m@.contains(key)
                &&& k.eq_spec(&key)
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
        assert(k.eq_spec(&key));
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

pub assume_specification<Key, S, A: Allocator>[ HashSet::<Key, S, A>::clear ](
    m: &mut HashSet<Key, S, A>,
)
    ensures
        final(m)@ == Set::<Key>::empty(),
;

pub assume_specification<'a, Key, S, A: Allocator>[ HashSet::<Key, S, A>::iter ](
    m: &'a HashSet<Key, S, A>,
) -> (hash_keys: hash_set::Iter<'a, Key>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& IteratorSpec::remaining(&hash_keys).unref().to_set() == m@
            &&& IteratorSpec::remaining(&hash_keys).no_duplicates()
            &&& IteratorSpec::remaining(&hash_keys).len() == m@.len()
            &&& into_iter_hash_keys(hash_keys) == IteratorSpec::remaining(&hash_keys).unref()
            &&& IteratorSpec::decrease(&hash_keys) is Some
        },
;

pub broadcast proof fn axiom_hashset_decreases<Key, S, A: Allocator>(m: HashSet<Key, S, A>)
    ensures
        #[trigger] (decreases_to!(m => m@)),
{
    admit();
}

//////// Entry API
// Specs for OccupiedEntry, VacantEntry, and the Entry enum
// OccupiedEntry and VacantEntry are both opaque;
// Entry is just an enum wrapper around the other 2, so we leave it transparent.
#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExOccupiedEntry<'a, K: 'a, V: 'a, A: Allocator>(OccupiedEntry<'a, K, V, A>);

#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExVacantEntry<'a, K: 'a, V: 'a, A: Allocator>(VacantEntry<'a, K, V, A>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
pub struct ExEntry<'a, K: 'a, V: 'a, A: Allocator>(Entry<'a, K, V, A>);

/// Specification for an [`OccupiedEntry`].
/// Contains the current key and value in the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
/// The final value is optional, since the user might choose to remove the entry.
pub trait OccupiedEntrySpecFns<K, V, A>: Sized {
    spec fn spec_key(self) -> K;

    spec fn value(self) -> V;

    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> OccupiedEntrySpecFns<K, V, A> for OccupiedEntry<'a, K, V, A> {
    uninterp spec fn spec_key(self) -> K;

    uninterp spec fn value(self) -> V;

    #[verifier::prophetic]
    uninterp spec fn final_value(self) -> Option<V>;
}

/// Specification for a [`VacantEntry`].
/// Contains the current key for the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
/// The final value is optional, since the user may or may not choose to insert a value.
pub trait VacantEntrySpecFns<K, V, A>: Sized {
    spec fn spec_key(self) -> K;

    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> VacantEntrySpecFns<K, V, A> for VacantEntry<'a, K, V, A> {
    uninterp spec fn spec_key(self) -> K;

    #[verifier::prophetic]
    uninterp spec fn final_value(self) -> Option<V>;
}

/// Specification for an [`Entry`].
/// Contains the current key for the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
pub trait EntrySpecFns<K, V, A>: Sized {
    spec fn spec_key(self) -> K;

    spec fn value(self) -> Option<V>;

    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> EntrySpecFns<K, V, A> for Entry<'a, K, V, A> {
    open spec fn spec_key(self) -> K {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.spec_key(),
            Entry::Vacant(vacant_entry) => vacant_entry.spec_key(),
        }
    }

    open spec fn value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => Some(occupied_entry.value()),
            Entry::Vacant(vacant_entry) => None,
        }
    }

    #[verifier::prophetic]
    open spec fn final_value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.final_value(),
            Entry::Vacant(vacant_entry) => vacant_entry.final_value(),
        }
    }
}

pub broadcast axiom fn axiom_has_resolved_occupied_entry<K, V, A: Allocator>(
    entry: OccupiedEntry<K, V, A>,
)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == Some(entry.value()),
;

pub broadcast axiom fn axiom_has_resolved_vacant_entry<K, V, A: Allocator>(
    entry: VacantEntry<K, V, A>,
)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == None::<V>,
;

pub broadcast proof fn axiom_has_resolved_entry<K, V, A: Allocator>(entry: Entry<K, V, A>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == entry.value(),
{
    broadcast use axiom_has_resolved_occupied_entry;
    broadcast use axiom_has_resolved_vacant_entry;

}

pub assume_specification<'a, Key: Hash + Eq, Value, S: BuildHasher, A: Allocator>[ HashMap::<
    Key,
    Value,
    S,
    A,
>::entry ](m: &'a mut HashMap<Key, Value, S, A>, key: Key) -> (entry: Entry<'a, Key, Value, A>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() && eq_matches_equality::<Key>()
            ==> (entry.key() == key && entry.value() == old(m)@.get(key) && final(m)@ == (
        match entry.final_value() {
            Some(value) => old(m)@.insert(key, value),
            None => old(m)@.remove(key),
        })),
;

//// Entry
#[verifier::allow_in_spec]
pub assume_specification<'a, 'b, K, V, A: Allocator>[ Entry::key ](
    entry: &'b Entry::<'a, K, V, A>,
) -> (key: &'b K)
    returns
        &entry.spec_key(),
;

pub assume_specification<'a, K, V, A: Allocator>[ Entry::or_insert ](
    entry: Entry::<'a, K, V, A>,
    default: V,
) -> (value: &'a mut V)
    ensures
        *value == (match entry.value() {
            Some(v) => v,
            None => default,
        }),
        entry.final_value() == Some(*final(value)),
;

pub assume_specification<'a, K, V, A: Allocator>[ Entry::insert_entry ](
    entry: Entry::<'a, K, V, A>,
    value: V,
) -> (occ_entry: OccupiedEntry<'a, K, V, A>)
    ensures
        occ_entry.key() == entry.key(),
        occ_entry.value() == value,
        entry.final_value() == occ_entry.final_value(),
;

//// OccupiedEntry
// This module works around a bug with `allow_in_spec` that creates duplicate spec fn names
mod m_occ {
    use super::*;

    #[verifier::allow_in_spec]
    pub assume_specification<'a, 'b, K, V, A: Allocator>[ OccupiedEntry::key ](
        entry: &'b OccupiedEntry::<'a, K, V, A>,
    ) -> (key: &'b K)
        returns
            &entry.spec_key(),
    ;

}

pub assume_specification<'a, K, V, A: Allocator>[ OccupiedEntry::remove_entry ](
    entry: OccupiedEntry::<'a, K, V, A>,
) -> (kv: (K, V))
    ensures
        entry.final_value() == None,
    returns
        (*entry.key(), entry.value()),
;

pub assume_specification<'a, 'b, K, V, A: Allocator>[ OccupiedEntry::get ](
    entry: &'b OccupiedEntry::<'a, K, V, A>,
) -> (value: &'b V)
    ensures
        *value == entry.value(),
;

pub assume_specification<'a, 'b, K, V, A: Allocator>[ OccupiedEntry::get_mut ](
    entry: &'b mut OccupiedEntry::<'a, K, V, A>,
) -> (value: &'b mut V)
    ensures
        *value == old(entry).value(),
        final(entry).key() == old(entry).key(),
        final(entry).value() == *final(value),
        final(entry).final_value() == old(entry).final_value(),
;

pub assume_specification<'a, K, V, A: Allocator>[ OccupiedEntry::into_mut ](
    entry: OccupiedEntry::<'a, K, V, A>,
) -> (value: &mut V)
    ensures
        *value == entry.value(),
        entry.final_value() == Some(*final(value)),
;

pub assume_specification<'a, K, V, A: Allocator>[ OccupiedEntry::insert ](
    entry: &mut OccupiedEntry::<'a, K, V, A>,
    value: V,
) -> (old_value: V)
    ensures
        old_value == old(entry).value(),
        final(entry).key() == old(entry).key(),
        final(entry).value() == value,
        final(entry).final_value() == old(entry).final_value(),
;

pub assume_specification<'a, K, V, A: Allocator>[ OccupiedEntry::remove ](
    entry: OccupiedEntry::<'a, K, V, A>,
) -> (value: V)
    ensures
        value == entry.value(),
        entry.final_value() == None,
;

//// VacantEntry
// This module works around a bug with `allow_in_spec` that creates duplicate spec fn names
mod m_vac {
    use super::*;

    #[verifier::allow_in_spec]
    pub assume_specification<'a, 'b, K: 'a, V: 'a, A: Allocator>[ VacantEntry::key ](
        entry: &'b VacantEntry::<'a, K, V, A>,
    ) -> (key: &'b K)
        returns
            &entry.spec_key(),
    ;

}

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator>[ VacantEntry::into_key ](
    entry: VacantEntry::<'a, K, V, A>,
) -> (key: K)
    ensures
        key == entry.key(),
        entry.final_value() == None,
;

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator>[ VacantEntry::insert ](
    entry: VacantEntry::<'a, K, V, A>,
    value: V,
) -> (value_ref: &mut V)
    ensures
        *value_ref == value,
        entry.final_value() == Some(*final(value_ref)),
;

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator>[ VacantEntry::insert_entry ](
    entry: VacantEntry::<'a, K, V, A>,
    value: V,
) -> (occ_entry: OccupiedEntry::<'a, K, V, A>)
    ensures
        occ_entry.key() == entry.key(),
        occ_entry.value() == value,
        entry.final_value() == occ_entry.final_value(),
;

pub broadcast group group_hash_axioms {
    lemma_hash_map_insert_ensures_if_eq_matches_equality,
    lemma_hash_map_insert_ensures_if_eq_matches_deep_equality,
    lemma_hash_map_contains_key_ensures_if_eq_matches_equality,
    lemma_hash_map_contains_key_ensures_if_eq_matches_deep_equality,
    lemma_hash_map_get_ensures_if_eq_matches_equality,
    lemma_hash_map_get_ensures_if_eq_matches_deep_equality,
    lemma_hash_map_remove_ensures_if_eq_matches_equality,
    lemma_hash_map_remove_ensures_if_eq_matches_deep_equality,
    lemma_hash_set_insert_ensures_if_eq_matches_equality,
    lemma_hash_set_insert_ensures_if_eq_matches_deep_equality,
    lemma_hash_set_contains_ensures_if_eq_matches_equality,
    lemma_hash_set_contains_ensures_if_eq_matches_deep_equality,
    lemma_hash_set_get_ensures_if_eq_matches_equality,
    lemma_hash_set_get_ensures_if_eq_matches_deep_equality,
    lemma_hash_set_remove_ensures_if_eq_matches_equality,
    lemma_hash_set_remove_ensures_if_eq_matches_deep_equality,
    axiom_borrowed_key_hashing_matches_self,
    axiom_borrowed_key_hashing_matches_ref,
    axiom_borrowed_key_hashing_matches_box,
    axiom_borrowed_key_hashing_matches_string,
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
    axiom_i64_obeys_hash_table_key_model,
    axiom_i128_obeys_hash_table_key_model,
    axiom_isize_obeys_hash_table_key_model,
    axiom_box_bool_obeys_hash_table_key_model,
    axiom_box_integer_type_obeys_hash_table_key_model,
    axiom_random_state_builds_valid_hashers,
    axiom_spec_hash_map_len,
    axiom_spec_hash_set_len,
    axiom_hashmap_decreases,
    axiom_hashset_decreases,
    axiom_has_resolved_occupied_entry,
    axiom_has_resolved_vacant_entry,
    axiom_has_resolved_entry,
}

} // verus!
