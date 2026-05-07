//! This code adds specifications for the standard-library types
//! `std::collections::HashMap` and `std::collections::HashSet`.
//!
//! Most of the specification only applies if you use `HashMap<Key,
//! Value>` or `HashSet<Key>`. If you use some custom build hasher,
//! e.g., with`HashMap<Key, Value, CustomBuildHasher>`, the
//! specification won't specify much.
//!
//! Likewise, the specification is only meaningful when the `Key`
//! obeys our hash table model, i.e., (1) `Key::hash` is
//! deterministic, (2) any two `Key`s are identical if and only if the
//! executable `==` operator considers them equal, and (3)
//! `Key::clone` produces a result equal to its input. We have an
//! axiom that all primitive types and `Box`es thereof obey this
//! model. But if you want to use some other key type `MyKey`, you
//! need to explicitly state your assumption that it does so with
//! `assume(vstd::std_specs::hash::obeys_key_model::<MyKey>());`. In
//! the future, we plan to devise a way for you to prove that it does
//! so, so that you don't have to make such an assumption.
//!
//! By default, the Verus standard library brings useful axioms
//! about the behavior of `HashMap` and `HashSet` into the ambient
//! reasoning context by broadcasting the group
//! `vstd::std_specs::hash::group_hash_axioms`.
use super::super::prelude::*;
use super::iter::IteratorSpec;

use core::alloc::Allocator;
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
/// The three requirements are (1) the hash function is deterministic,
/// (2) any two keys of type `Key` are identical if and only if they
/// are considered equal by the executable `==` operator, and (3) the
/// executable `Key::clone` function produces a result identical to
/// its input. Requirement (1) isn't satisfied by having `Key`
/// implement `Hash`, since this trait doesn't mandate determinism.
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

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_keys(*self) == IteratorSpec::remaining(self).unref()
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

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_values(*self) == IteratorSpec::remaining(self).unref()
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

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter(*self) == IteratorSpec::remaining(self).unref()
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

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)]` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_hash_map_iter<'a, Key, Value, S, A: Allocator>(
    m: &'a HashMap<Key, Value, S, A>,
) -> (r: hash_map::Iter<'a, Key, Value>);

pub broadcast proof fn axiom_spec_hash_map_iter<'a, Key, Value, S>(m: &'a HashMap<Key, Value, S>)
    ensures
        ({
            let v = #[trigger] spec_hash_map_iter(m).remaining();
            &&& v.len() == m@.dom().len()
            &&& forall|i: int|
                #![trigger m@.contains_key(*v[i].0)]
                #![trigger m@[*v[i].0]]
                0 <= i < v.len() ==> m@.contains_key(*v[i].0) && m@[*v[i].0] == *v[i].1
            &&& forall|k: Key| #[trigger] m@.contains_key(k) ==> v.contains((&k, &m@[k]))
            &&& v.unref().to_set() == m@.kv_pairs()
        }),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_map_iter)]
pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::iter ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (iter: hash_map::Iter<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& iter == spec_hash_map_iter(m)
            &&& iter.remaining().no_duplicates()
            &&& IteratorSpec::decrease(&iter) is Some
            &&& IteratorSpec::initial_value_relation(&iter, &iter)
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

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher, A: Allocator>[ HashMap::<
    Key,
    Value,
    S,
    A,
>::reserve ](m: &mut HashMap<Key, Value, S, A>, additional: usize)
    ensures
        final(m)@ == old(m)@,
;

pub assume_specification<Key: Eq + Hash, Value, S: BuildHasher, A: Allocator>[ HashMap::<
    Key,
    Value,
    S,
    A,
>::insert ](m: &mut HashMap<Key, Value, S, A>, k: Key, v: Value) -> (result: Option<Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::contains_key::<Q> ](
    m: &HashMap<Key, Value, S, A>,
    k: &Q,
) -> (result: bool)
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::get::<Q> ](m: &'a HashMap<Key, Value, S, A>, k: &Q) -> (result:
    Option<&'a Value>)
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashMap::<Key, Value, S, A>::remove::<Q> ](m: &mut HashMap<Key, Value, S, A>, k: &Q) -> (result:
    Option<Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& borrowed_key_removed(old(m)@, final(m)@, k)
            &&& match result {
                Some(v) => maps_borrowed_key_to_value(old(m)@, k, v),
                None => !contains_borrowed_key(old(m)@, k),
            }
        },
;

pub assume_specification<Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::clear ](
    m: &mut HashMap<Key, Value, S, A>,
)
    ensures
        final(m)@ == Map::<Key, Value>::empty(),
;

// To allow reasoning about the ghost Keys iterator when the executable
// function `keys()` is invoked in a `for` loop header (e.g., in
// `for x in it: m.keys() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_keys_iter<'a, Key, Value, S, A: Allocator>(
    m: &'a HashMap<Key, Value, S, A>,
) -> (keys: Keys<'a, Key, Value>);

pub broadcast proof fn axiom_spec_keys_iter<'a, Key, Value, S, A: Allocator>(
    m: &'a HashMap<Key, Value, S, A>,
)
    ensures
        (#[trigger] spec_keys_iter(m).remaining()).unref().to_set() == m@.dom(),
        spec_keys_iter(m).remaining().no_duplicates(),
        spec_keys_iter(m).remaining().len() == m@.dom().len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_keys_iter)]
pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::keys ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (keys: Keys<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& keys == spec_keys_iter(m)
            &&& IteratorSpec::decrease(&keys) is Some
            &&& IteratorSpec::initial_value_relation(&keys, &keys)
        },
;

// To allow reasoning about the ghost Values iterator when the executable
// function `value()` is invoked in a `for` loop header (e.g., in
// `for x in it: m.keys() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_values_iter<'a, Key, Value, S, A: Allocator>(
    m: &'a HashMap<Key, Value, S, A>,
) -> (values: Values<'a, Key, Value>);

pub broadcast proof fn axiom_spec_values_iter<'a, Key, Value, S, A: Allocator>(
    m: &'a HashMap<Key, Value, S, A>,
)
    ensures
        (#[trigger] spec_values_iter(m).remaining()).unref().to_set() == m@.values(),
        spec_values_iter(m).remaining().len() == m@.dom().len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_values_iter)]
pub assume_specification<'a, Key, Value, S, A: Allocator>[ HashMap::<Key, Value, S, A>::values ](
    m: &'a HashMap<Key, Value, S, A>,
) -> (values: Values<'a, Key, Value>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& values == spec_values_iter(m)
            &&& IteratorSpec::decrease(&values) is Some
            &&& IteratorSpec::initial_value_relation(&values, &values)
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

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_hash_keys(*self) == IteratorSpec::remaining(self).unref()
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

pub assume_specification<Key: Eq + Hash, S: BuildHasher, A: Allocator>[ HashSet::<
    Key,
    S,
    A,
>::reserve ](m: &mut HashSet<Key, S, A>, additional: usize)
    ensures
        final(m)@ == old(m)@,
;

pub assume_specification<Key: Eq + Hash, S: BuildHasher, A: Allocator>[ HashSet::<
    Key,
    S,
    A,
>::insert ](m: &mut HashSet<Key, S, A>, k: Key) -> (result: bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::contains ](m: &HashSet<Key, S, A>, k: &Q) -> (result: bool)
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::get::<Q> ](m: &'a HashSet<Key, S, A>, k: &Q) -> (result: Option<&'a Key>)
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
    A: Allocator,
    Q: Hash + Eq + ?Sized,
>[ HashSet::<Key, S, A>::remove::<Q> ](m: &mut HashSet<Key, S, A>, k: &Q) -> (result: bool)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& sets_differ_by_borrowed_key(old(m)@, final(m)@, k)
            &&& result == set_contains_borrowed_key(old(m)@, k)
        },
;

pub assume_specification<Key, S, A: Allocator>[ HashSet::<Key, S, A>::clear ](
    m: &mut HashSet<Key, S, A>,
)
    ensures
        final(m)@ == Set::<Key>::empty(),
;

// To allow reasoning about the ghost keys in the HashSet iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: m.keys() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_hash_keys_iter<'a, Key, S, A: Allocator>(m: &'a HashSet<Key, S, A>) -> (r:
    hash_set::Iter<'a, Key>);

pub broadcast proof fn axiom_spec_hash_keys_iter<'a, Key, S, A: Allocator>(
    m: &'a HashSet<Key, S, A>,
)
    ensures
        (#[trigger] spec_hash_keys_iter(m).remaining()).unref().to_set() == m@,
        spec_hash_keys_iter(m).remaining().no_duplicates(),
        spec_hash_keys_iter(m).remaining().len() == m@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_hash_keys_iter)]
pub assume_specification<'a, Key, S, A: Allocator>[ HashSet::<Key, S, A>::iter ](
    m: &'a HashSet<Key, S, A>,
) -> (hash_keys: hash_set::Iter<'a, Key>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& hash_keys == spec_hash_keys_iter(m)
            &&& IteratorSpec::decrease(&hash_keys) is Some
            &&& IteratorSpec::initial_value_relation(&hash_keys, &hash_keys)
        },
;

pub broadcast proof fn axiom_hashset_decreases<Key, S, A: Allocator>(m: HashSet<Key, S, A>)
    ensures
        #[trigger] (decreases_to!(m => m@)),
{
    admit();
}

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
    axiom_i64_obeys_hash_table_key_model,
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
    axiom_spec_hash_keys_iter,
    axiom_spec_keys_iter,
    axiom_spec_values_iter,
    axiom_hashmap_decreases,
    axiom_hashset_decreases,
}

} // verus!
