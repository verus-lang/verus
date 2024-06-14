/// This code adds specifications for the standard-library type
/// `std::collections::HashMap`.
///
/// Most of the specification only applies if you use `HashMap<Key,
/// Value>`. If you use some custom build hasher, e.g.,
/// with`HashMap<Key, Value, CustomBuildHasher>`, the specification
/// won't specify much.
///
/// Likewise, the specification is only meaningful when you know that
/// the `Key` has a deterministic hash. We have an axiom that all
/// primitive types and `Box`es thereof have a deterministic hash. But
/// if you want to use some other key type `MyKey`, you need to
/// explicitly state your assumption that it has a deterministic hash
/// with
/// `assume(vstd::std_specs::hash::does_type_have_deterministic_hash::<MyKey>());`.
/// In the future, we plan to devise a way for you to prove that it
/// has a deterministic hash so you don't have to make such an
/// assumption.
///
/// To make most use of the specification, you should use `broadcast
/// use vstd::std_specs::hash::group_hash_axioms;`. This will bring
/// various useful axioms about the behavior of a `HashMap` into the
/// ambient reasoning context. In the future, if we find that having
/// these axioms in scope doesn't impact performance, we may put them
/// into the global ambient context so you don't have to explicitly
/// `broadcast use` them.
use super::super::prelude::*;

use core::hash::{BuildHasher, Hash, Hasher};
use core::option::Option;
use core::option::Option::None;
use std::borrow::Borrow;
use std::collections::hash_map::{DefaultHasher, RandomState};
use std::collections::HashMap;

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

// Just because a type implements `Hash`, that doesn't mean it satisfies
// our model of `Hash`. Our model of `Hash` is that it's deterministic:
// If you hash the same element multiple times, each time it will hash
// as the same sequence of bytes.
#[verifier::external_body]
pub spec fn does_type_have_deterministic_hash<T: ?Sized>() -> bool;

pub broadcast proof fn axiom_primitive_types_have_deterministic_hash()
    ensures
        does_type_have_deterministic_hash::<bool>(),
        does_type_have_deterministic_hash::<u8>(),
        does_type_have_deterministic_hash::<u16>(),
        does_type_have_deterministic_hash::<u32>(),
        does_type_have_deterministic_hash::<u64>(),
        does_type_have_deterministic_hash::<u128>(),
        does_type_have_deterministic_hash::<i8>(),
        does_type_have_deterministic_hash::<i16>(),
        does_type_have_deterministic_hash::<i32>(),
        does_type_have_deterministic_hash::<i64>(),
        does_type_have_deterministic_hash::<i128>(),
        does_type_have_deterministic_hash::<Box<bool>>(),
        does_type_have_deterministic_hash::<Box<u8>>(),
        does_type_have_deterministic_hash::<Box<u16>>(),
        does_type_have_deterministic_hash::<Box<u32>>(),
        does_type_have_deterministic_hash::<Box<u64>>(),
        does_type_have_deterministic_hash::<Box<u128>>(),
        does_type_have_deterministic_hash::<Box<i8>>(),
        does_type_have_deterministic_hash::<Box<i16>>(),
        does_type_have_deterministic_hash::<Box<i32>>(),
        does_type_have_deterministic_hash::<Box<i64>>(),
        does_type_have_deterministic_hash::<Box<i128>>(),
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
// `does_type_conform_to_build_hasher_model::<T>()` holds.
#[verifier::external_trait_specification]
pub trait ExBuildHasher {
    type ExternalTraitSpecificationFor: BuildHasher;

    type Hasher: Hasher;
}

#[verifier::external_body]
pub spec fn does_type_conform_to_build_hasher_model<T: ?Sized>() -> bool;

// A commonly used type of trait `BuildHasher` is `RandomState`. We
// model that type here. In particular, we have an axiom that
// `RandomState` conforms to our model of how `BuildHasher` behaves.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRandomState(RandomState);

pub broadcast proof fn axiom_random_state_conforms_to_build_hasher_model()
    ensures
        does_type_conform_to_build_hasher_model::<RandomState>(),
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
        does_type_have_deterministic_hash::<Key>() && does_type_conform_to_build_hasher_model::<S>()
            ==> #[trigger] spec_hash_map_len(m) == m@.len(),
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
        m@ == old(m)@.insert(k, v),
        does_type_have_deterministic_hash::<Key>() && does_type_conform_to_build_hasher_model::<S>()
            ==> match result {
            Some(v) => old(m)@.contains_key(k) && v == old(m)[k],
            None => !old(m)@.contains_key(k),
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
// (2) `Key = Box<Q>`. (TODO: Include another axiom for the case `Key
// = String, Q = str`.)
pub spec fn map_contains_borrowed_key<Key, Value, Q: ?Sized>(m: Map<Key, Value>, k: &Q) -> bool;

pub broadcast proof fn axiom_hash_map_contains_deref_key<Q, Value>(m: Map<Q, Value>, k: &Q)
    ensures
        #[trigger] map_contains_borrowed_key::<Q, Value, Q>(m, k) <==> m.contains_key(*k),
{
    admit();
}

pub broadcast proof fn axiom_hash_map_contains_box<Q, Value>(m: Map<Box<Q>, Value>, k: &Q)
    ensures
        #[trigger] map_contains_borrowed_key::<Box<Q>, Value, Q>(m, k) <==> m.contains_key(
            Box::new(*k),
        ),
{
    admit();
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_contains_key<Key, Value, S, Q>(m: &HashMap<Key, Value, S>, k: &Q) -> (result:
    bool) where Key: Borrow<Q> + Hash + Eq, Q: Hash + Eq + ?Sized, S: BuildHasher
    ensures
        does_type_have_deterministic_hash::<Key>() && does_type_conform_to_build_hasher_model::<S>()
            ==> result == map_contains_borrowed_key(m@, k),
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
// `map_contains_borrowed_key`, discussed above.) But this isn't very
// helpful by itself, since there's no body to that specification
// function. So we have special-case axioms that say what this means
// in two important circumstances: (1) `Key = Q` and (2) `Key =
// Box<Q>`. (TODO: Include another axiom for the case `Key = String, Q
// = str`.)
pub spec fn map_maps_borrowed_key_to_value<Key, Value, Q: ?Sized>(
    m: Map<Key, Value>,
    k: &Q,
    v: Value,
) -> bool;

pub broadcast proof fn axiom_hash_map_maps_deref_key_to_value<Q, Value>(
    m: Map<Q, Value>,
    k: &Q,
    v: Value,
)
    ensures
        #[trigger] map_maps_borrowed_key_to_value::<Q, Value, Q>(m, k, v) <==> m.contains_key(*k)
            && m[*k] == v,
{
    admit();
}

pub broadcast proof fn axiom_hash_map_maps_box_key_to_value<Q, Value>(
    m: Map<Box<Q>, Value>,
    q: &Q,
    v: Value,
)
    ensures
        #[trigger] map_maps_borrowed_key_to_value::<Box<Q>, Value, Q>(m, q, v) <==> {
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
        does_type_have_deterministic_hash::<Key>() && does_type_conform_to_build_hasher_model::<S>()
            ==> match result {
            Some(v) => map_maps_borrowed_key_to_value(m@, k, *v),
            None => !map_contains_borrowed_key(m@, k),
        },
{
    m.get(k)
}

#[verifier::external_fn_specification]
pub fn ex_hash_map_clear<Key, Value, S>(m: &mut HashMap<Key, Value, S>)
    ensures
        m@ == Map::<Key, Value>::empty(),
{
    m.clear()
}

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_hash_axioms {
    axiom_hash_map_contains_deref_key,
    axiom_hash_map_contains_box,
    axiom_hash_map_maps_deref_key_to_value,
    axiom_hash_map_maps_box_key_to_value,
    axiom_primitive_types_have_deterministic_hash,
    axiom_random_state_conforms_to_build_hasher_model,
    axiom_spec_hash_map_len,
}

} // verus!
