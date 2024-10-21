/// This code adds specifications for the standard-library type
/// `std::collections::HashMap`.
///
/// Most of the specification only applies if you use `HashMap<Key,
/// Value>`. If you use some custom build hasher, e.g.,
/// with`HashMap<Key, Value, CustomBuildHasher>`, the specification
/// won't specify much.
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
/// To make most use of the specification, you should use `broadcast
/// use vstd::std_specs::hash::group_hash_axioms;`. This will bring
/// various useful axioms about the behavior of a `HashMap` into the
/// ambient reasoning context. In the future, if we find that having
/// these axioms in scope doesn't impact performance, we may put them
/// into the global ambient context so you don't have to explicitly
/// `broadcast use` them.
use super::super::prelude::*;

use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash, Hasher};
use core::option::Option;
use core::option::Option::None;
use std::collections::hash_map::{DefaultHasher, RandomState};
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
    closed spec fn view(&self) -> Seq<Seq<u8>>;
}

pub trait DefaultHasherAdditionalSpecFns {
    spec fn spec_finish(s: Seq<Seq<u8>>) -> u64;
}

impl DefaultHasherAdditionalSpecFns for DefaultHasher {
    #[verifier::external_body]
    spec fn spec_finish(s: Seq<Seq<u8>>) -> u64;
}

// This is the specification of behavior for `DefaultHasher::new()`.
#[verifier::external_fn_specification]
pub fn ex_default_hasher_new() -> (result: DefaultHasher)
    ensures
        result@ == Seq::<Seq<u8>>::empty(),
{
    DefaultHasher::new()
}

// This is the specification of behavior for `DefaultHasher::write(&[u8])`.
#[verifier::external_fn_specification]
pub fn ex_default_hasher_write(state: &mut DefaultHasher, bytes: &[u8])
    ensures
        state@ == old::<&mut _>(state)@.push(bytes@),
{
    state.write(bytes)
}

// This is the specification of behavior for `DefaultHasher::finish()`.
#[verifier::external_fn_specification]
pub fn ex_default_hasher_finish(state: &DefaultHasher) -> (result: u64)
    ensures
        result == DefaultHasher::spec_finish(state@),
{
    state.finish()
}

// This function specifies whether a type obeys the requirements
// to be a key in a hash table and have that hash table conform to our
// hash-table model. The two requirements are (1) the hash function
// has to be deterministic and (2) any two elements considered equal
// by the executable `==` operator must be identical. Requirement (1)
// isn't satisfied by having `Key` implement `Hash`, since this trait
// doesn't mandate determinism.
#[verifier::external_body]
pub spec fn obeys_key_model<Key: ?Sized>() -> bool;

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
pub spec fn builds_valid_hashers<T: ?Sized>() -> bool;

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

// We now specify the behavior of `HashMap`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
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

    #[verifier::external_body]
    closed spec fn view(&self) -> Map<Key, Value>;
}

pub open spec fn spec_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>) -> usize;

pub broadcast proof fn axiom_spec_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_map_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_hash_map_len)]
pub fn ex_hash_map_len<Key, Value, S>(m: &HashMap<Key, Value, S>) -> (len: usize)
    ensures
        len == spec_hash_map_len(m),
{
    m.len()
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_new<Key, Value>() -> (m: HashMap<Key, Value, RandomState>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    HashMap::<Key, Value>::new()
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_with_capacity<Key, Value>(capacity: usize) -> (m: HashMap<
    Key,
    Value,
    RandomState,
>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    HashMap::<Key, Value>::with_capacity(capacity)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_reserve<Key, Value, S>(m: &mut HashMap<Key, Value, S>, additional: usize) where
    Key: Eq + Hash,
    S: BuildHasher,

    ensures
        m@ == old(m)@,
{
    m.reserve(additional)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_insert<Key, Value, S>(
    m: &mut HashMap<Key, Value, S>,
    k: Key,
    v: Value,
) -> (result: Option<Value>) where Key: Eq + Hash, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& m@ == old(m)@.insert(k, v)
            &&& match result {
                Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
                None => !old(m)@.contains_key(k),
            }
        },
{
    m.insert(k, v)
}

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
pub spec fn contains_borrowed_key<Key, Value, Q: ?Sized>(m: Map<Key, Value>, k: &Q) -> bool;

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

#[verifier::external_fn_specification]
pub fn ex_hash_contains_key<Key, Value, S, Q>(m: &HashMap<Key, Value, S>, k: &Q) -> (result:
    bool) where Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> result == contains_borrowed_key(
            m@,
            k,
        ),
{
    m.contains_key(k)
}

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
pub spec fn maps_borrowed_key_to_value<Key, Value, Q: ?Sized>(
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

#[verifier::external_fn_specification]
pub fn ex_hash_map_get<'a, Key, Value, S, Q>(m: &'a HashMap<Key, Value, S>, k: &Q) -> (result:
    Option<&'a Value>) where Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> match result {
            Some(v) => maps_borrowed_key_to_value(m@, k, *v),
            None => !contains_borrowed_key(m@, k),
        },
{
    m.get(k)
}

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
pub spec fn borrowed_key_removed<Key, Value, Q: ?Sized>(
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

#[verifier::external_fn_specification]
pub fn ex_hash_map_remove<Key, Value, S, Q>(m: &mut HashMap<Key, Value, S>, k: &Q) -> (result:
    Option<Value>) where Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& borrowed_key_removed(old(m)@, m@, k)
            &&& match result {
                Some(v) => maps_borrowed_key_to_value(old(m)@, k, v),
                None => !contains_borrowed_key(old(m)@, k),
            }
        },
{
    m.remove(k)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_clear<Key, Value, S>(m: &mut HashMap<Key, Value, S>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    m.clear()
}

// We now specify the behavior of `HashSet`.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(S)]
pub struct ExHashSet<Key, S>(HashSet<Key, S>);

impl<Key, S> View for HashSet<Key, S> {
    type V = Set<Key>;

    #[verifier::external_body]
    closed spec fn view(&self) -> Set<Key>;
}

pub open spec fn spec_hash_set_len<Key, S>(m: &HashSet<Key, S>) -> usize;

pub broadcast proof fn axiom_spec_hash_set_len<Key, S>(m: &HashSet<Key, S>)
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> #[trigger] spec_hash_set_len(m)
            == m@.len(),
{
    admit();
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_hash_set_len)]
pub fn ex_hash_set_len<Key, S>(m: &HashSet<Key, S>) -> (len: usize)
    ensures
        len == spec_hash_set_len(m),
{
    m.len()
}

#[verifier::external_fn_specification]
pub fn ex_hash_set_new<Key>() -> (m: HashSet<Key, RandomState>)
    ensures
        m@ == Set::<Key>::empty(),
{
    HashSet::<Key>::new()
}

#[verifier::external_fn_specification]
pub fn ex_hash_set_with_capacity<Key>(capacity: usize) -> (m: HashSet<Key, RandomState>)
    ensures
        m@ == Set::<Key>::empty(),
{
    HashSet::<Key>::with_capacity(capacity)
}

#[verifier::external_fn_specification]
pub fn ex_hash_set_reserve<Key, S>(m: &mut HashSet<Key, S>, additional: usize) where
    Key: Eq + Hash,
    S: BuildHasher,

    ensures
        m@ == old(m)@,
{
    m.reserve(additional)
}

#[verifier::external_fn_specification]
pub fn ex_hash_set_insert<Key, S>(m: &mut HashSet<Key, S>, k: Key) -> (result: bool) where
    Key: Eq + Hash,
    S: BuildHasher,

    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& m@ == old(m)@.insert(k)
            &&& result == !old(m)@.contains(k)
        },
{
    m.insert(k)
}

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
pub spec fn set_contains_borrowed_key<Key, Q: ?Sized>(m: Set<Key>, k: &Q) -> bool;

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

#[verifier::external_fn_specification]
pub fn ex_hash_set_contains<Key, S, Q>(m: &HashSet<Key, S>, k: &Q) -> (result: bool) where
    Key: Borrow<Q> + Hash + Eq,
    Q: Hash + Eq + ?Sized,
    S: BuildHasher,

    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> result
            == set_contains_borrowed_key(m@, k),
{
    m.contains(k)
}

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
pub spec fn sets_borrowed_key_to_key<Key, Q: ?Sized>(m: Set<Key>, k: &Q, v: &Key) -> bool;

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

#[verifier::external_fn_specification]
pub fn ex_hash_set_get<'a, Key, S, Q>(m: &'a HashSet<Key, S>, k: &Q) -> (result: Option<
    &'a Key,
>) where Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized, S: BuildHasher
    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> match result {
            Some(v) => sets_borrowed_key_to_key(m@, k, v),
            None => !set_contains_borrowed_key(m@, k),
        },
{
    m.get(k)
}

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
pub spec fn sets_differ_by_borrowed_key<Key, Q: ?Sized>(
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

#[verifier::external_fn_specification]
pub fn ex_hash_set_remove<Key, S, Q>(m: &mut HashSet<Key, S>, k: &Q) -> (result: bool) where
    Key: Borrow<Q> + Hash + Eq,
    Q: Hash + Eq + ?Sized,
    S: BuildHasher,

    ensures
        obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> {
            &&& sets_differ_by_borrowed_key(old(m)@, m@, k)
            &&& result == set_contains_borrowed_key(old(m)@, k)
        },
{
    m.remove(k)
}

#[verifier::external_fn_specification]
pub fn ex_hash_set_clear<Key, S>(m: &mut HashSet<Key, S>)
    ensures
        m@ == Set::<Key>::empty(),
{
    m.clear()
}

pub broadcast group group_hash_axioms {
    axiom_box_key_removed,
    axiom_contains_deref_key,
    axiom_contains_box,
    axiom_deref_key_removed,
    axiom_maps_deref_key_to_value,
    axiom_maps_box_key_to_value,
    axiom_bool_obeys_hash_table_key_model,
    axiom_u8_obeys_hash_table_key_model,
    axiom_u16_obeys_hash_table_key_model,
    axiom_u32_obeys_hash_table_key_model,
    axiom_u64_obeys_hash_table_key_model,
    axiom_u128_obeys_hash_table_key_model,
    axiom_i8_obeys_hash_table_key_model,
    axiom_i16_obeys_hash_table_key_model,
    axiom_i32_obeys_hash_table_key_model,
    axiom_i164_obeys_hash_table_key_model,
    axiom_i128_obeys_hash_table_key_model,
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
}

} // verus!
