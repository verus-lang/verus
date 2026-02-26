use super::gset::{Finite, Finiteness, GSet, Infinite};
use super::iset::ISet;
use super::set::{
    Set,
    lemma_set_ext_equal_eq,
};
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

pub(crate) type GenericMap<K, V, FINITE> = super::gmap::GMap<K, V, FINITE>;

#[doc(hidden)]
pub use super::gmap::{
    map,
    imap,
    map_internal,
    imap_internal,
    assert_maps_equal,
    assert_maps_equal_internal,
};

verus! {

#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct Map<K, V>(pub super::gmap::GMap<K, V, Finite>);

#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct IMap<K, V>(pub super::gmap::GMap<K, V, Infinite>);

impl<K, V> Map<K, V> {
    pub open spec fn from_set(key_set: Set<K>, fv: spec_fn(K) -> V) -> Self {
        Map(super::gmap::GMap::from_set(key_set.0, fv))
    }

    pub(crate) open spec fn from_gset(key_set: GSet<K, Finite>, fv: spec_fn(K) -> V) -> Self {
        Map(super::gmap::GMap::from_set(key_set, fv))
    }

    #[verifier::inline]
    pub open spec fn new(key_set: Set<K>, fv: spec_fn(K) -> V) -> Self {
        Map::from_set(key_set, fv)
    }

    pub open spec fn empty() -> Self {
        Map(super::gmap::GMap::empty())
    }

    pub open spec fn idom(self) -> ISet<K> {
        self.0.idom()
    }

    pub open spec fn dom(self) -> Set<K> {
        Set(self.0.dom())
    }

    pub open spec fn contains_key(self, k: K) -> bool {
        self.0.contains_key(k)
    }

    pub open spec fn contains_value(self, v: V) -> bool {
        self.0.contains_value(v)
    }

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.0.contains_pair(k, v)
    }

    #[verifier::inline]
    pub open spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.0.index(key)
    }

    #[verifier::inline]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    pub open spec fn insert(self, key: K, value: V) -> Self {
        Map(self.0.insert(key, value))
    }

    pub open spec fn remove(self, key: K) -> Self {
        Map(self.0.remove(key))
    }

    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        Map(self.0.union_prefer_right(m2.0))
    }

    pub open spec fn remove_keys(self, keys: Set<K>) -> Self {
        Map(self.0.remove_keys(keys.0))
    }

    pub open spec fn restrict(self, keys: Set<K>) -> Self {
        Map(self.0.restrict(keys.0))
    }

    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> Map<K, W> {
        Map(self.0.map_entries(f))
    }

    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> Map<K, W> {
        Map(self.0.map_values(f))
    }

    pub open spec fn invert(self) -> Map<V, K> {
        Map(self.0.invert())
    }

    pub open spec fn values(self) -> Set<V> {
        Set(self.0.values())
    }

    pub open spec fn submap_of(self, m2: Self) -> bool {
        self.0.submap_of(m2.0)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    pub open spec fn is_equal_on_key(self, m2: Self, key: K) -> bool {
        self.0.is_equal_on_key(m2.0, key)
    }

    pub open spec fn agrees(self, m2: Self) -> bool {
        self.0.agrees(m2.0)
    }

    pub open spec fn is_injective(self) -> bool {
        self.0.is_injective()
    }

    pub open spec fn congruent(self, m2: Self) -> bool {
        self.0.congruent(m2.0)
    }

    pub(crate) open spec fn congruent_generic<FINITE2: Finiteness>(self, m2: GenericMap<K, V, FINITE2>) -> bool {
        self.0.congruent(m2)
    }

    pub open spec fn to_infinite(self) -> IMap<K, V> {
        IMap(self.0.to_infinite())
    }

    pub proof fn lemma_union_prefer_right(self, m2: Self)
        ensures
            #![trigger (self.union_prefer_right(m2))]
            self.union_prefer_right(m2).dom().to_infinite()
                == self.dom().to_infinite().union(m2.dom().to_infinite()),
            self.union_prefer_right(m2).dom().to_infinite().congruent(
                self.dom().to_infinite().union(m2.dom().to_infinite()),
            ),
            forall|k|
                #![auto]
                self.union_prefer_right(m2).dom().contains(k) ==> self.union_prefer_right(m2)[k]
                    == if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
    {
        self.0.lemma_union_prefer_right(m2.0);
    }

    pub proof fn lemma_remove_keys_len(self, keys: Set<K>)
        requires
            keys <= self.dom(),
            keys.finite(),
            self.dom().finite(),
        ensures
            self.remove_keys(keys).dom().len() == self.dom().len() - keys.len(),
        decreases keys.len(),
    {
        self.0.lemma_remove_keys_len(keys.0);
    }

    pub axiom fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == Map(super::gmap::GMap::<K, V, Finite>::empty()),
    ;

    pub axiom fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == old(self).insert(key, value),
    ;

    pub axiom fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == old(self).remove(key),
            v == old(self)[key],
    ;

    pub axiom fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    ;

    pub axiom fn tracked_remove_keys(tracked &mut self, keys: Set<K>) -> (tracked out_map: Self)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            *self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    ;

    pub axiom fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    ;

    pub axiom fn tracked_map_keys_in_place(tracked &mut self, key_map: Map<K, K>)
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old(self).dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> key_map.index(j1) != key_map.index(j2),
        ensures
            forall|j| #[trigger] self.dom().contains(j) == key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> self.dom().contains(j) && #[trigger] self.index(j)
                    == old(self).index(key_map.index(j)),
    ;
}

impl<K, V> IMap<K, V> {
    pub open spec fn from_set(key_set: ISet<K>, fv: spec_fn(K) -> V) -> Self {
        IMap(super::gmap::GMap::from_set(key_set.0, fv))
    }

    pub(crate) open spec fn from_gset<FINITE2: Finiteness>(key_set: GSet<K, FINITE2>, fv: spec_fn(K) -> V) -> Self {
        IMap(super::gmap::GMap::from_set(key_set.to_infinite(), fv))
    }

    pub open spec fn new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V) -> Self {
        IMap(super::gmap::IMap::new(fk, fv))
    }

    pub open spec fn total(fv: spec_fn(K) -> V) -> Self {
        IMap::new(|k| true, fv)
    }

    pub open spec fn empty() -> Self {
        IMap(super::gmap::GMap::empty())
    }

    pub open spec fn idom(self) -> ISet<K> {
        self.0.idom()
    }

    pub open spec fn dom(self) -> ISet<K> {
        ISet(self.0.dom())
    }

    pub open spec fn contains_key(self, k: K) -> bool {
        self.0.contains_key(k)
    }

    pub open spec fn contains_value(self, v: V) -> bool {
        self.0.contains_value(v)
    }

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.0.contains_pair(k, v)
    }

    #[verifier::inline]
    pub open spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.0.index(key)
    }

    #[verifier::inline]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    pub open spec fn insert(self, key: K, value: V) -> Self {
        IMap(self.0.insert(key, value))
    }

    pub open spec fn remove(self, key: K) -> Self {
        IMap(self.0.remove(key))
    }

    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        IMap(self.0.union_prefer_right(m2.0))
    }

    pub open spec fn remove_keys(self, keys: ISet<K>) -> Self {
        IMap(self.0.remove_keys(keys.0))
    }

    pub open spec fn restrict(self, keys: ISet<K>) -> Self {
        IMap(self.0.restrict(keys.0))
    }

    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> IMap<K, W> {
        IMap(self.0.map_entries(f))
    }

    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> IMap<K, W> {
        IMap(self.0.map_values(f))
    }

    pub open spec fn invert(self) -> IMap<V, K> {
        IMap(self.0.invert())
    }

    pub open spec fn values(self) -> ISet<V> {
        ISet(self.0.values())
    }

    pub open spec fn submap_of(self, m2: Self) -> bool {
        self.0.submap_of(m2.0)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    pub open spec fn congruent(self, m2: Self) -> bool {
        self.0.congruent(m2.0)
    }

    pub(crate) open spec fn congruent_generic<FINITE2: Finiteness>(self, m2: GenericMap<K, V, FINITE2>) -> bool {
        self.0.congruent(m2)
    }

    pub open spec fn to_finite(self) -> Map<K, V>
        recommends
            self.dom().finite(),
    {
        Map(self.0.to_finite())
    }
}

pub broadcast proof fn axiom_map_finite_from_type<K, V>(m: Map<K, V>)
    ensures
        #[trigger] m.idom().finite(),
        #[trigger] m.dom().finite(),
{
    super::gmap::axiom_map_finite_from_type(m.0);
}

pub broadcast axiom fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
;

pub broadcast axiom fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
;

pub broadcast proof fn lemma_infinite_new_ensures<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #![trigger(IMap::new(fk, fv))]
        forall|k|
            #![auto]
            fk(k) <==> IMap::new(fk, fv).dom().contains(k),
        forall|k| #![auto] fk(k) ==> IMap::new(fk, fv)[k] == fv(k),
        IMap::new(fk, fv).dom() == ISet::new(fk),
{
    super::gmap::lemma_infinite_new_ensures(fk, fv);
}

pub broadcast proof fn lemma_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
    broadcast use super::gmap::lemma_map_empty;
}

pub broadcast proof fn lemma_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    super::gmap::lemma_map_insert_domain(m.0, key, value);
    reveal(Set::insert);
    assert forall|k: K| #[trigger] m.insert(key, value).dom().contains(k) == m.dom().insert(key).contains(k) by {
        assert(m.insert(key, value).dom().contains(k) == m.0.insert(key, value).dom().contains(k));
        assert(m.0.insert(key, value).dom().contains(k) == m.0.dom().insert(key).contains(k));
        assert(m.dom().insert(key).contains(k) == m.0.dom().insert(key).contains(k));
    }
    lemma_set_ext_equal_eq(m.insert(key, value).dom(), m.dom().insert(key));
}

pub broadcast proof fn lemma_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
    super::gmap::lemma_map_insert_same(m.0, key, value);
}

pub broadcast proof fn lemma_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
    super::gmap::lemma_map_insert_different(m.0, key1, key2, value);
}

pub broadcast proof fn lemma_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    super::gmap::lemma_map_remove_domain(m.0, key);
    reveal(Set::remove);
    assert forall|k: K| #[trigger] m.remove(key).dom().contains(k) == m.dom().remove(key).contains(k) by {
        assert(m.remove(key).dom().contains(k) == m.0.remove(key).dom().contains(k));
        assert(m.0.remove(key).dom().contains(k) == m.0.dom().remove(key).contains(k));
        assert(m.dom().remove(key).contains(k) == m.0.dom().remove(key).contains(k));
    }
    lemma_set_ext_equal_eq(m.remove(key).dom(), m.dom().remove(key));
}

pub broadcast proof fn lemma_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
    super::gmap::lemma_map_remove_different(m.0, key1, key2);
}

pub broadcast proof fn lemma_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    super::gmap::lemma_map_ext_equal(m1.0, m2.0);
}

pub broadcast proof fn lemma_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    lemma_map_ext_equal(m1, m2);
}

pub broadcast proof fn lemma_congruence_extensionality<K, V, FINITE: Finiteness>(
    x: GenericMap<K, V, FINITE>,
    y: GenericMap<K, V, FINITE>,
)
    requires
        #[trigger] x.congruent(y),
    ensures
        x == y,
{
    super::gmap::lemma_congruence_extensionality(x, y);
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V>(m: Map<K, V>) -> Map<K, V> {
    m
}

pub broadcast group group_map_axioms {
    super::gmap::lemma_new_from_set_ensures,
    lemma_infinite_new_ensures,
    super::gmap::lemma_map_empty,
    super::gmap::lemma_map_insert_domain,
    super::gmap::lemma_map_insert_same,
    super::gmap::lemma_map_insert_different,
    super::gmap::lemma_map_remove_domain,
    super::gmap::lemma_map_remove_different,
    super::gmap::lemma_map_ext_equal,
    super::gmap::lemma_map_ext_equal_deep,
    super::gmap::GMap::lemma_remove_keys,
    super::gmap::GMap::lemma_invert_ensures,
    super::gmap::GMap::lemma_restrict,
    super::gmap::GMap::lemma_map_entries,
    super::gmap::GMap::lemma_map_values_ensures,
    axiom_map_index_decreases_finite,
    axiom_map_index_decreases_infinite,
    lemma_map_empty,
    lemma_map_insert_domain,
    lemma_map_insert_same,
    lemma_map_insert_different,
    lemma_map_remove_domain,
    lemma_map_remove_different,
    lemma_map_ext_equal,
    lemma_map_ext_equal_deep,
    super::gmap::GMap::lemma_union_prefer_right,
    lemma_congruence_extensionality,
}

} // verus!
