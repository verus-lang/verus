//! Maps that support ownership of keys
//!
//! - [`GhostMapAuth<K, V>`] represents authoritative ownership of the entire map;
//! - [`GhostSubmap<K, V>`] represents client ownership of a submap;
//! - [`GhostPersistentSubmap<K, V>`] represents duplicable client knowledge of a submap which will never change;
//! - [`GhostPointsTo<K, V>`] represents client ownership of a single key-value pair.
//! - [`GhostPersistentPointsTo<K, V>`] represents duplicable client knowledge of a single key-value pair which will never change.
//!
//! Updating the authoritative `GhostMapAuth<K, V>` requires a `GhostSubmap<K, V>` containing the keys being updated.
//!
//! `GhostSubmap<K, V>`s can be combined or split.
//! Whenever a `GhostSubmap<K, V>` can be used, we can instead use a `GhostPointsTo<K, V>` (but not vice-versa).
//!
//! `GhostPersistentSubmap<K, V>`s can be combined or split.
//! Whenever a `GhostPersistentSubmap<K, V>` can be used, we can instead use a `GhostPersistentPointsTo<K, V>` (but not vice-versa).
//!
//! ### Example
//!
//! ```
//! fn example_use() {
//!     let tracked (mut auth, mut sub) = GhostMapAuth::new(map![1u8 => 1u64, 2u8 => 2u64, 3u8 => 3u64]);
//!
//!     // Allocate some more keys in the auth map, receiving a new submap.
//!     let tracked sub2 = auth.insert_map(map![4u8 => 4u64, 5u8 => 5u64]);
//!     proof { sub.combine(sub2); }
//!
//!     // Allocate a single key in the auth map, receiving a points to
//!     let tracked pt1 = auth.insert(6u8, 6u64);
//!     proof { sub.combine_points_to(pt1); }
//!
//!     // Delete some keys in the auth map, by returning corresponding submap.
//!     let tracked sub3 = sub.split(set![3u8, 4u8]);
//!     proof { auth.delete(sub3); }
//!
//!     // Split the submap into a points to and a submap
//!     let tracked pt2 = sub.split_points_to(1u8);
//!     let tracked sub4 = sub.split(set![5u8, 6u8]);
//!
//!     // In general, we might need to call agree() to establish the fact that
//!     // a points-to/submap has the same values as the auth map.  Here, Verus
//!     // doesn't need agree because it can track where both the auth, points-to
//!     // and submap came from.
//!     proof { sub.agree(&auth); }
//!     proof { pt2.agree(&auth); }
//!     proof { sub4.agree(&auth); }
//!
//!     assert(pt2.key() == 1u8);
//!     assert(pt2.value() == auth[1u8]);
//!     assert(sub4[5u8] == auth[5u8]);
//!     assert(sub4[6u8] == auth[6u8]);
//!     assert(sub[2u8] == auth[2u8]);
//!
//!     // Update keys using ownership of submaps.
//!     proof { sub.update(&mut auth, map![2u8 => 22u64]); }
//!     proof { pt2.update(&mut auth, 11u64); }
//!     proof { sub4.update(&mut auth, map![5u8 => 55u64, 6u8 => 66u8]); }
//!     assert(auth[1u8] == 11u64);
//!     assert(auth[2u8] == 22u64);
//!     assert(auth[5u8] == 55u64);
//!     assert(auth[6u8] == 66u64);
//!
//!     // Persist and duplicate the submap
//!     let mut psub1 = sub.persist();
//!     assert(psub1[2u8] == 22u64);
//!     let psub2 = psub1.duplicate();
//!     assert(psub2[2u8] == 22u64);
//!
//!     // Not shown in this simple example is the main use case of this resource:
//!     // maintaining an invariant between GhostMapAuth<K, V> and some exec-mode
//!     // shared state with a map view (e.g., HashMap<K, V>), which states that
//!     // the Map<K, V> view of GhostMapAuth<K, V> is the same as the view of the
//!     // HashMap<K, V>, and then handing out a GhostSubmap<K, V> to different
//!     // clients that might need to operate on different keys in this map.
//! }
//! ```
use super::super::map::*;
use super::super::map_lib::*;
use super::super::modes::*;
use super::super::pcm::*;
use super::super::prelude::*;
use super::super::set_lib::*;

verus! {

broadcast use super::super::group_vstd_default;

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
enum AuthCarrier<K, V> {
    Auth(Map<K, V>),
    Frac,
    Invalid,
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
enum FracCarrier<K, V> {
    Frac { owning: Map<K, V>, dup: Map<K, V> },
    Invalid,
}

impl<K, V> AuthCarrier<K, V> {
    spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    spec fn map(self) -> Map<K, V>
        recommends
            self.valid(),
    {
        match self {
            AuthCarrier::Auth(m) => m,
            AuthCarrier::Frac => Map::empty(),
            AuthCarrier::Invalid => Map::empty(),
        }
    }
}

impl<K, V> FracCarrier<K, V> {
    spec fn valid(self) -> bool {
        match self {
            FracCarrier::Invalid => false,
            FracCarrier::Frac { owning, dup } => owning.dom().disjoint(dup.dom()),
        }
    }

    spec fn owning_map(self) -> Map<K, V> {
        match self {
            FracCarrier::Frac { owning, .. } => owning,
            FracCarrier::Invalid => Map::empty(),
        }
    }

    spec fn dup_map(self) -> Map<K, V> {
        match self {
            FracCarrier::Frac { dup, .. } => dup,
            FracCarrier::Invalid => Map::empty(),
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
// This struct represents the underlying resource algebra for GhostMaps
struct MapCarrier<K, V> {
    auth: AuthCarrier<K, V>,
    frac: FracCarrier<K, V>,
}

impl<K, V> PCM for MapCarrier<K, V> {
    closed spec fn valid(self) -> bool {
        match (self.auth, self.frac) {
            (AuthCarrier::Invalid, _) => false,
            (_, FracCarrier::Invalid) => false,
            (AuthCarrier::Auth(auth), FracCarrier::Frac { owning, dup }) => {
                &&& owning <= auth
                &&& dup <= auth
                &&& owning.dom().disjoint(dup.dom())
            },
            (AuthCarrier::Frac, FracCarrier::Frac { owning, dup }) => owning.dom().disjoint(
                dup.dom(),
            ),
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        let auth = match (self.auth, other.auth) {
            // Invalid carriers absorb
            (AuthCarrier::Invalid, _) => AuthCarrier::Invalid,
            (_, AuthCarrier::Invalid) => AuthCarrier::Invalid,
            // There can't be two auths
            (AuthCarrier::Auth(_), AuthCarrier::Auth(_)) => AuthCarrier::Invalid,
            // Fracs remain the same
            (AuthCarrier::Frac, AuthCarrier::Frac) => AuthCarrier::Frac,
            // Whoever is the auth has precedence
            (AuthCarrier::Auth(_), _) => self.auth,
            (_, AuthCarrier::Auth(_)) => other.auth,
        };

        let frac = match (self.frac, other.frac) {
            // Invalid fracs remain invalid
            (FracCarrier::Invalid, _) => FracCarrier::Invalid,
            (_, FracCarrier::Invalid) => FracCarrier::Invalid,
            // We can mix two owning fracs iff they are disjoint -- we get the union
            // There is a tricky element here:
            //  - one of the fracs may be invalid due to their maps overlapping
            //  - there is no real way to express this in the typesystem
            //  - we need to allow that through (because it does not equal Invalid)
            (
                FracCarrier::Frac { owning: self_owning, dup: self_dup },
                FracCarrier::Frac { owning: other_owning, dup: other_dup },
            ) => {
                let non_overlapping = {
                    &&& self_owning.dom().disjoint(other_dup.dom())
                    &&& other_owning.dom().disjoint(self_dup.dom())
                    &&& self_owning.dom().disjoint(other_owning.dom())
                };
                let aggreement = self_dup.agrees(other_dup);
                if non_overlapping && aggreement {
                    FracCarrier::Frac {
                        owning: self_owning.union_prefer_right(other_owning),
                        dup: self_dup.union_prefer_right(other_dup),
                    }
                } else {
                    FracCarrier::Invalid
                }
            },
        };

        MapCarrier { auth, frac }
    }

    closed spec fn unit() -> Self {
        MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac { owning: Map::empty(), dup: Map::empty() },
        }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        broadcast use lemma_submap_of_trans;

        let ab = MapCarrier::op(a, b);
        lemma_submap_of_op_frac(a, b);
        // derive contradiction that the items are disjoint
        if !a.frac.owning_map().dom().disjoint(a.frac.dup_map().dom()) {
            // The intersection is not empty
            lemma_disjoint_iff_empty_intersection(
                a.frac.owning_map().dom(),
                a.frac.dup_map().dom(),
            );
            let a_k = choose|k: K|
                a.frac.owning_map().dom().intersect(a.frac.dup_map().dom()).contains(k);
            assert(ab.frac.owning_map().dom().intersect(ab.frac.dup_map().dom()).contains(a_k));  // CONTRADICTION
        };
    }

    proof fn commutative(a: Self, b: Self) {
        let ab = Self::op(a, b);
        let ba = Self::op(b, a);
        assert(ab == ba);
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        let bc = Self::op(b, c);
        let ab = Self::op(a, b);
        let a_bc = Self::op(a, bc);
        let ab_c = Self::op(ab, c);
        assert(a_bc == ab_c);
    }

    proof fn op_unit(a: Self) {
        let x = Self::op(a, Self::unit());
        assert(a == x);
    }

    proof fn unit_valid() {
    }
}

proof fn lemma_submap_of_op_frac<K, V>(a: MapCarrier<K, V>, b: MapCarrier<K, V>)
    requires
        MapCarrier::op(a, b).valid(),
    ensures
        a.frac.owning_map() <= MapCarrier::op(a, b).frac.owning_map(),
        a.frac.dup_map() <= MapCarrier::op(a, b).frac.dup_map(),
        b.frac.owning_map() <= MapCarrier::op(a, b).frac.owning_map(),
        b.frac.dup_map() <= MapCarrier::op(a, b).frac.dup_map(),
{
    let ab = MapCarrier::op(a, b);
    assert(ab.frac.owning_map() == a.frac.owning_map().union_prefer_right(b.frac.owning_map()));
    assert(ab.frac.dup_map() == a.frac.dup_map().union_prefer_right(b.frac.dup_map()));
    assert(a.frac.owning_map().dom().disjoint(b.frac.owning_map().dom()));
}

broadcast proof fn lemma_submap_of_op<K, V>(a: MapCarrier<K, V>, b: MapCarrier<K, V>)
    requires
        #[trigger] MapCarrier::op(a, b).valid(),
    ensures
        a.frac.owning_map() <= MapCarrier::op(a, b).frac.owning_map(),
        a.frac.dup_map() <= MapCarrier::op(a, b).frac.dup_map(),
        a.auth.map() <= MapCarrier::op(a, b).auth.map(),
        b.frac.owning_map() <= MapCarrier::op(a, b).frac.owning_map(),
        b.frac.dup_map() <= MapCarrier::op(a, b).frac.dup_map(),
        b.auth.map() <= MapCarrier::op(a, b).auth.map(),
        a.valid(),
        b.valid(),
{
    lemma_submap_of_op_frac(a, b);
    MapCarrier::closed_under_incl(a, b);
    MapCarrier::commutative(a, b);
    MapCarrier::closed_under_incl(b, a);
    let ab = MapCarrier::op(a, b);
    assert(ab.auth.map() == a.auth.map().union_prefer_right(b.auth.map()));
}

/// A resource that has the authoritative ownership on the entire map
#[verifier::reject_recursive_types(K)]
pub struct GhostMapAuth<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/// A resource that asserts client ownership of a submap.
///
/// The existence of a [`GhostSubmap`] implies that:
///  - Those keys will remain in the map (unless the onwer of the [`GhostSubmap`] deletes it using [`GhostMapAuth::delete`]);
///  - Those keys will remain pointing to the same values (unless the onwer of the [`GhostSubmap`] updates them using [`GhostSubmap::update`])
///  - All other [`GhostSubmap`]/[`GhostPointsTo`]/[`GhostPersistentSubmap`]/[`GhostPersistentPointsTo`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(K)]
pub struct GhostSubmap<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/// A resource representing duplicable client knowledge of a persistent submap.
///
/// The existence of a [`GhostPersistentSubmap`] implies that:
///  - Those keys will remain in the map, pointing to the same values, forever;
///  - All other [`GhostSubmap`]/[`GhostPointsTo`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(K)]
pub struct GhostPersistentSubmap<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/// A resource that asserts client ownership over a single key in the map.
///
/// The existence of a [`GhostPointsTo`] implies that:
///  - Those key will remain in the map (unless the onwer of the [`GhostPointsTo`] deletes it using [`GhostMapAuth::delete_points_to`]);
///  - Those key will remain pointing to the same value (unless the onwer of the [`GhostPointsTo`] updates them using [`GhostPointsTo::update`])
///  - All other [`GhostSubmap`]/[`GhostPointsTo`]/[`GhostPersistentSubmap`]/[`GhostPersistentPointsTo`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(K)]
pub struct GhostPointsTo<K, V> {
    submap: GhostSubmap<K, V>,
}

/// A resource representing duplicable client knowledge of a single key in the map.
///
/// The existence of a [`GhostPersistentPointsTo`] implies that:
///  - The key-value pair will remain in the map, forever;
///  - All other [`GhostSubmap`]/[`GhostPointsTo`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(K)]
pub struct GhostPersistentPointsTo<K, V> {
    submap: GhostPersistentSubmap<K, V>,
}

impl<K, V> GhostMapAuth<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is Auth
        &&& self.r.value().frac == FracCarrier::Frac {
            owning: Map::<K, V>::empty(),
            dup: Map::<K, V>::empty(),
        }
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Logically underlying [`Map`]
    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().auth.map()
    }

    /// Domain of the [`GhostMapAuth`]
    pub open spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    /// Indexing operation `auth[key]`
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    /// Instantiate a dummy [`GhostMapAuth`]
    pub proof fn dummy() -> (tracked result: GhostMapAuth<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        auth
    }

    /// Extract the [`GhostMapAuth`] from a mutable reference
    pub proof fn take(tracked &mut self) -> (tracked result: GhostMapAuth<K, V>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);
        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

    /// Create an empty [`GhostSubmap`]
    pub proof fn empty(tracked &self) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == self.id(),
            result@ == Map::<K, V>::empty(),
    {
        use_type_invariant(self);
        GhostSubmap::<K, V>::empty(self.id())
    }

    /// Insert a [`Map`] of values, receiving the [`GhostSubmap`] that asserts ownership over the key
    /// domain inserted.
    ///
    /// ```
    /// proof fn insert_map_example(tracked mut m: GhostMapAuth<int, int>) -> (tracked r: GhostSubmap<int, int>)
    ///     requires
    ///         !m.dom().contains(1int),
    ///         !m.dom().contains(2int),
    /// {
    ///     let tracked submap = m.insert_map(map![1int => 1int, 2int => 4int]);
    ///     // do something with the submap
    ///     submap
    /// }
    /// ```
    pub proof fn insert_map(tracked &mut self, m: Map<K, V>) -> (tracked result: GhostSubmap<K, V>)
        requires
            old(self)@.dom().disjoint(m.dom()),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union_prefer_right(m),
            result.id() == self.id(),
            result@ == m,
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_submap_of_op;

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);

        use_type_invariant(&mself);
        assert(mself.inv());
        let tracked mut self_r = mself.r;

        let full_carrier = MapCarrier {
            auth: AuthCarrier::Auth(self_r.value().auth.map().union_prefer_right(m)),
            frac: FracCarrier::Frac { owning: m, dup: Map::empty() },
        };

        assert(full_carrier.valid());
        let tracked updated_r = self_r.update(full_carrier);

        let auth_carrier = MapCarrier {
            auth: updated_r.value().auth,
            frac: FracCarrier::Frac { owning: Map::empty(), dup: Map::empty() },
        };
        let frac_carrier = MapCarrier { auth: AuthCarrier::Frac, frac: updated_r.value().frac };

        assert(updated_r.value() == MapCarrier::op(auth_carrier, frac_carrier));
        let tracked (auth_r, frac_r) = updated_r.split(auth_carrier, frac_carrier);
        self.r = auth_r;
        GhostSubmap { r: frac_r }
    }

    /// Insert a key-value pair, receiving the [`GhostPointsTo`] that asserts ownerships over the key.
    ///
    /// ```
    /// proof fn insert_example(tracked mut m: GhostMapAuth<int, int>) -> (tracked r: GhostPointsTo<int, int>)
    ///     requires
    ///         !m.dom().contains(1int),
    /// {
    ///     let tracked points_to = m.insert(1, 1);
    ///     // do something with the points_to
    ///     points_to
    /// }
    /// ```
    pub proof fn insert(tracked &mut self, k: K, v: V) -> (tracked result: GhostPointsTo<K, V>)
        requires
            !old(self)@.contains_key(k),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(k, v),
            result.id() == self.id(),
            result@ == (k, v),
    {
        let tracked submap = self.insert_map(map![k => v]);
        GhostPointsTo { submap }
    }

    /// Delete a set of keys
    /// ```
    /// proof fn delete(tracked mut auth: GhostMapAuth<int, int>)
    ///     requires
    ///         auth.dom().contains(1int),
    ///         auth.dom().contains(2int),
    ///     ensures
    ///         old(auth)@ == auth@
    /// {
    ///     let tracked submap = auth.insert_map(map![1int => 1int, 2int => 4int]);
    ///     // do something with the submap
    ///     auth.delete(submap)
    /// }
    /// ```
    pub proof fn delete(tracked &mut self, tracked submap: GhostSubmap<K, V>)
        requires
            submap.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.remove_keys(submap@.dom()),
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_submap_of_op;

        use_type_invariant(&*self);
        use_type_invariant(&submap);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut self_r = mself.r;

        // join the resource with the original carrier
        self_r = self_r.join(submap.r);

        // remove keys from the map
        let auth_map = self_r.value().auth.map();
        let new_auth_map = auth_map.remove_keys(submap@.dom());

        let new_r = MapCarrier {
            auth: AuthCarrier::Auth(new_auth_map),
            frac: FracCarrier::Frac { owning: Map::empty(), dup: Map::empty() },
        };

        // update the resource
        self.r = self_r.update(new_r);
    }

    /// Delete a single key from the map
    /// ```
    /// proof fn delete_key(tracked mut auth: GhostMapAuth<int, int>)
    ///     requires
    ///         auth.dom().contains(1int),
    ///     ensures
    ///         old(auth)@ == auth@
    /// {
    ///     let tracked points_to = auth.insert(1, 1);
    ///     // do something with the submap
    ///     auth.delete_points_to(points_to)
    /// }
    /// ```
    pub proof fn delete_points_to(tracked &mut self, tracked p: GhostPointsTo<K, V>)
        requires
            p.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.remove(p.key()),
    {
        use_type_invariant(&p);
        p.lemma_map_view();
        self.delete(p.submap);
    }

    /// Create a new [`GhostMapAuth`] from a [`Map`].
    /// Gives the other half of ownership in the form of a [`GhostSubmap`].
    ///
    /// ```
    /// fn example() {
    ///     let m = map![1int => 1int, 2int => 4int, 3int => 9int];
    ///     let tracked (auth, sub) = GhostMapAuth::new(m);
    ///     assert(auth@ == m);
    ///     assert(sub.dom() == m.dom());
    /// }
    /// ```
    pub proof fn new(m: Map<K, V>) -> (tracked result: (GhostMapAuth<K, V>, GhostSubmap<K, V>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == m,
            result.1@ == m,
    {
        let tracked full_r = Resource::alloc(
            MapCarrier {
                auth: AuthCarrier::Auth(m),
                frac: FracCarrier::Frac { owning: m, dup: Map::empty() },
            },
        );

        let auth_carrier = MapCarrier {
            auth: AuthCarrier::Auth(m),
            frac: FracCarrier::Frac { owning: Map::empty(), dup: Map::empty() },
        };

        let frac_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac { owning: m, dup: Map::empty() },
        };

        assert(full_r.value() == MapCarrier::op(auth_carrier, frac_carrier));
        let tracked (auth_r, frac_r) = full_r.split(auth_carrier, frac_carrier);
        (GhostMapAuth { r: auth_r }, GhostSubmap { r: frac_r })
    }
}

impl<K, V> GhostSubmap<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is Frac
        &&& self.r.value().frac is Frac
        &&& self.r.value().frac.dup_map().is_empty()
    }

    /// Checks whether the [`GhostSubmap`] refers to a single key (and thus can be converted to a
    /// [`GhostPointsTo`]).
    pub open spec fn is_points_to(self) -> bool {
        &&& self@.len() == 1
        &&& self.dom().finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Logically underlying [`Map`]
    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().frac.owning_map()
    }

    /// Domain of the [`GhostSubmap`]
    pub open spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    /// Indexing operation `submap[key]`
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    /// Instantiate a dummy [`GhostSubmap`]
    pub proof fn dummy() -> (tracked result: GhostSubmap<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        submap
    }

    /// Instantiate an empty [`GhostSubmap`] of a particular id
    pub proof fn empty(id: int) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == id,
            result@ == Map::<K, V>::empty(),
    {
        let tracked r = Resource::create_unit(id);
        GhostSubmap { r }
    }

    /// Extract the [`GhostSubmap`] from a mutable reference, leaving behind an empty map.
    pub proof fn take(tracked &mut self) -> (tracked result: GhostSubmap<K, V>)
        ensures
            old(self).id() == self.id(),
            self@.is_empty(),
            result == *old(self),
            result.id() == self.id(),
    {
        use_type_invariant(&*self);

        let tracked mut r = Self::empty(self.id());
        tracked_swap(self, &mut r);
        r
    }

    /// Agreement between a [`GhostSubmap`] and a corresponding [`GhostMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostMapAuth`] and a corresponding [`GhostSubmap`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostSubmap`] is a submap of the [`GhostMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostMapAuth<int, int>, tracked &sub: GhostSubmap<int, int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         sub.dom().contains(1int),
    ///         sub[1int] == 1int,
    ///     ensures
    ///         auth[1int] == 1int
    /// {
    ///     sub.agree(auth);
    ///     assert(sub@ <= auth@);
    ///     assert(auth[1int] == 1int);
    /// }
    /// ```
    pub proof fn agree(tracked self: &GhostSubmap<K, V>, tracked auth: &GhostMapAuth<K, V>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        broadcast use lemma_submap_of_trans;

        use_type_invariant(self);
        use_type_invariant(auth);

        let tracked joined = self.r.join_shared(&auth.r);
        joined.validate();
        assert(self.r.value().frac.owning_map() <= joined.value().frac.owning_map());
    }

    /// Combining two [`GhostSubmap`]s is possible.
    /// We consume the input [`GhostSubmap`] and merge it into the first.
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked &mut self, tracked other: GhostSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union_prefer_right(other@),
            old(self)@.dom().disjoint(other@.dom()),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);

        let tracked mut r = Resource::alloc(MapCarrier::unit());
        tracked_swap(&mut self.r, &mut r);
        r.validate_2(&other.r);
        self.r = r.join(other.r);
    }

    /// Combining a [`GhostPointsTo`] into [`GhostSubmap`] is possible, in a similar way to the way to combine
    /// [`GhostSubmap`]s.
    pub proof fn combine_points_to(tracked &mut self, tracked other: GhostPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(other.key(), other.value()),
            !old(self)@.contains_key(other.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);

        other.lemma_map_view();
        self.combine(other.submap);
    }

    /// When we have two [`GhostSubmap`]s we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.dom().disjoint(other@.dom()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_2(&other.r);
    }

    /// When we have a [`GhostSubmap`] and a [`GhostPersistentSubmap`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent(tracked &mut self, tracked other: &GhostPersistentSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.dom().disjoint(other@.dom()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_2(&other.r);
    }

    /// When we have a [`GhostSubmap`] and a [`GhostPointsTo`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_points_to(tracked &mut self, tracked other: &GhostPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains_key(other.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.disjoint(&other.submap);
    }

    /// When we have a [`GhostSubmap`] and a [`GhostPersistentPointsTo`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent_points_to(
        tracked &mut self,
        tracked other: &GhostPersistentPointsTo<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains_key(other.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.disjoint_persistent(&other.submap);
    }

    /// We can split a [`GhostSubmap`] based on a set of keys in its domain.
    pub proof fn split(tracked &mut self, s: Set<K>) -> (tracked result: GhostSubmap<K, V>)
        requires
            s <= old(self)@.dom(),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.union_prefer_right(result@),
            result@.dom() =~= s,
            self@.dom() =~= old(self)@.dom() - s,
    {
        use_type_invariant(&*self);

        let tracked mut r = Resource::alloc(MapCarrier::<K, V>::unit());
        tracked_swap(&mut self.r, &mut r);

        let self_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: r.value().frac.owning_map().remove_keys(s),
                dup: r.value().frac.dup_map(),
            },
        };

        let res_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: r.value().frac.owning_map().restrict(s),
                dup: r.value().frac.dup_map(),
            },
        };

        assert(r.value().frac == MapCarrier::op(self_carrier, res_carrier).frac);
        let tracked (self_r, res_r) = r.split(self_carrier, res_carrier);
        self.r = self_r;
        GhostSubmap { r: res_r }
    }

    /// We can separate a single key out of a [`GhostSubmap`]
    pub proof fn split_points_to(tracked &mut self, k: K) -> (tracked result: GhostPointsTo<K, V>)
        requires
            old(self)@.contains_key(k),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.insert(result.key(), result.value()),
            result.key() == k,
            self@ == old(self)@.remove(k),
    {
        use_type_invariant(&*self);

        let tracked submap = self.split(set![k]);
        GhostPointsTo { submap }
    }

    /// When we have both the [`GhostMapAuth`] and a [`GhostSubmap`] we can update the values for a
    /// subset of keys in our submap.
    /// ```
    /// proof fn test(tracked auth: &mut GhostMapAuth<int, int>, tracked sub: &mut GhostSubmap<int, int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         sub.dom() == set![1int, 2int, 3int]
    ///     ensures
    ///         auth[1int] == 9int
    ///         auth[2int] == 10int
    ///         auth[3int] == 11int
    /// {
    ///     // need to agree on the subset
    ///     sub.agree(auth);
    ///     assert(sub@ <= auth@);
    ///     sub.update(map![1int => 9int, 2int => 10int, 3int => 11int]);
    /// }
    /// ```
    pub proof fn update(tracked &mut self, tracked auth: &mut GhostMapAuth<K, V>, m: Map<K, V>)
        requires
            m.dom() <= old(self)@.dom(),
            old(self).id() == old(auth).id(),
        ensures
            self.id() == old(self).id(),
            auth.id() == old(auth).id(),
            self@ == old(self)@.union_prefer_right(m),
            auth@ == old(auth)@.union_prefer_right(m),
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_submap_of_op;

        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut frac_r = mself.r;

        let tracked mut mauth = GhostMapAuth::<K, V>::dummy();
        tracked_swap(auth, &mut mauth);
        let tracked mut auth_r = mauth.r;

        frac_r.validate_2(&auth_r);
        let tracked mut full_r = frac_r.join(auth_r);

        assert(full_r.value().frac.owning_map() == frac_r.value().frac.owning_map());

        let auth_carrier = AuthCarrier::Auth(full_r.value().auth.map().union_prefer_right(m));
        let frac_carrier = FracCarrier::Frac {
            owning: full_r.value().frac.owning_map().union_prefer_right(m),
            dup: Map::empty(),
        };
        let new_full_carrier = MapCarrier { auth: auth_carrier, frac: frac_carrier };

        assert(new_full_carrier.valid());
        let tracked r_upd = full_r.update(new_full_carrier);

        let new_auth_carrier = MapCarrier {
            auth: r_upd.value().auth,
            frac: FracCarrier::Frac { owning: Map::empty(), dup: Map::empty() },
        };
        let new_frac_carrier = MapCarrier { auth: AuthCarrier::Frac, frac: r_upd.value().frac };
        assert(r_upd.value().frac == MapCarrier::op(new_auth_carrier, new_frac_carrier).frac);
        assert(r_upd.value() == MapCarrier::op(new_auth_carrier, new_frac_carrier));

        let tracked (new_auth_r, new_frac_r) = r_upd.split(new_auth_carrier, new_frac_carrier);
        auth.r = new_auth_r;
        self.r = new_frac_r;
    }

    /// Converting a [`GhostSubmap`] into a [`GhostPointsTo`]
    pub proof fn points_to(tracked self) -> (tracked r: GhostPointsTo<K, V>)
        requires
            self.is_points_to(),
        ensures
            self@ == map![r.key() => r.value()],
            self.id() == r.id(),
    {
        let tracked r = GhostPointsTo { submap: self };
        r.lemma_map_view();
        r
    }

    /// Convert a [`GhostSubmap`] into a [`GhostPersistentSubmap`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentSubmap<K, V>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_submap_of_op;

        use_type_invariant(&self);

        let tracked mut r = self.r;

        let self_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: self.r.value().frac.owning_map(),
                dup: self.r.value().frac.dup_map(),
            },
        };

        let res_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: self.r.value().frac.dup_map(),
                dup: self.r.value().frac.owning_map(),
            },
        };

        let tracked r = r.update(res_carrier);
        GhostPersistentSubmap { r }
    }
}

impl<K, V> GhostPersistentSubmap<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is Frac
        &&& self.r.value().frac is Frac
        &&& self.r.value().frac.owning_map().is_empty()
    }

    /// Checks whether the [`GhostPersistentSubmap`] refers to a single key (and thus can be converted to a
    /// [`GhostPersistentPointsTo`]).
    pub open spec fn is_points_to(self) -> bool {
        &&& self@.len() == 1
        &&& self.dom().finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Logically underlying [`Map`]
    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().frac.dup_map()
    }

    /// Domain of the [`GhostPersistentSubmap`]
    pub open spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    /// Indexing operation `submap[key]`
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    /// Instantiate a dummy [`GhostPersistentSubmap`]
    pub proof fn dummy() -> (tracked result: GhostPersistentSubmap<K, V>) {
        let tracked owned = GhostSubmap::<K, V>::dummy();
        owned.persist()
    }

    /// Instantiate an empty [`GhostPersistentSubmap`] of a particular id
    pub proof fn empty(id: int) -> (tracked result: GhostPersistentSubmap<K, V>)
        ensures
            result.id() == id,
            result@ == Map::<K, V>::empty(),
    {
        let tracked r = Resource::create_unit(id);
        GhostPersistentSubmap { r }
    }

    /// Duplicate the [`GhostPersistentSubmap`]
    pub proof fn duplicate(tracked &mut self) -> (tracked result: GhostPersistentSubmap<K, V>)
        ensures
            self.id() == result.id(),
            old(self).id() == self.id(),
            old(self)@ == self@,
            result@ == self@,
    {
        use_type_invariant(&*self);

        let tracked mut owned = Self::empty(self.id());
        let carrier = self.r.value();
        assert(carrier == MapCarrier::op(carrier, carrier));

        tracked_swap(self, &mut owned);
        let tracked (mut orig, new) = owned.r.split(carrier, carrier);
        tracked_swap(&mut self.r, &mut orig);
        GhostPersistentSubmap { r: new }
    }

    /// Agreement between a [`GhostPersistentSubmap`] and a corresponding [`GhostMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostMapAuth`] and a corresponding [`GhostPersistentSubmap`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentSubmap`] is a submap of the [`GhostMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostMapAuth<int, int>, tracked &sub: GhostPersistentSubmap<int, int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         sub.dom().contains(1int),
    ///         sub[1int] == 1int,
    ///     ensures
    ///         auth[1int] == 1int
    /// {
    ///     sub.agree(auth);
    ///     assert(sub@ <= auth@);
    ///     assert(auth[1int] == 1int);
    /// }
    /// ```
    pub proof fn agree(
        tracked self: &GhostPersistentSubmap<K, V>,
        tracked auth: &GhostMapAuth<K, V>,
    )
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        broadcast use lemma_submap_of_trans;

        use_type_invariant(self);
        use_type_invariant(auth);

        let tracked joined = self.r.join_shared(&auth.r);
        joined.validate();
        assert(self.r.value().frac.dup_map() <= joined.value().frac.dup_map());
    }

    /// Combining two [`GhostPersistentSubmap`]s is possible.
    /// We consume the input [`GhostPersistentSubmap`] and merge it into the first.
    /// We also learn that they agreed
    pub proof fn combine(tracked &mut self, tracked other: GhostPersistentSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union_prefer_right(other@),
            old(self)@.agrees(other@),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);

        let tracked mut r = Resource::alloc(MapCarrier::unit());
        tracked_swap(&mut self.r, &mut r);
        r.validate_2(&other.r);
        self.r = r.join(other.r);
    }

    /// Combining a [`GhostPersistentPointsTo`] into [`GhostPersistentSubmap`] is possible, in a similar way to the way to combine
    /// [`GhostPersistentSubmap`]s.
    pub proof fn combine_points_to(tracked &mut self, tracked other: GhostPersistentPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(other.key(), other.value()),
            old(self)@.contains_key(other.key()) ==> old(self)@[other.key()] == other.value(),
    {
        use_type_invariant(&*self);
        use_type_invariant(&other);

        other.lemma_map_view();
        self.combine(other.submap);
    }

    /// When we have a [`GhostPersistentSubmap`] and a [`GhostSubmap`] we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.dom().disjoint(other@.dom()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_2(&other.r);
    }

    /// When we have two [`GhostPersistentSubmap`]s we can prove that they agree on their intersection.
    pub proof fn intersection_agrees(tracked &mut self, tracked other: &GhostPersistentSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.agrees(other@),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.r.validate_2(&other.r);
    }

    /// When we have a [`GhostPersistentSubmap`] and a [`GhostPointsTo`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_points_to(tracked &mut self, tracked other: &GhostPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains_key(other.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.disjoint(&other.submap);
    }

    /// When we have a [`GhostPersistentSubmap`] and a [`GhostPersistentPointsTo`],
    /// we can prove that either they are disjoint domains or the key-value pair is in the
    /// persistent submap.
    pub proof fn intersection_agrees_points_to(
        tracked &mut self,
        tracked other: &GhostPersistentPointsTo<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.contains_key(other.key()) ==> self@[other.key()] == other.value(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.intersection_agrees(&other.submap);
    }

    /// We can split a [`GhostPersistentSubmap`] based on a set of keys in its domain.
    pub proof fn split(tracked &mut self, s: Set<K>) -> (tracked result: GhostPersistentSubmap<
        K,
        V,
    >)
        requires
            s <= old(self)@.dom(),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.union_prefer_right(result@),
            result@.dom() =~= s,
            self@.dom() =~= old(self)@.dom() - s,
    {
        use_type_invariant(&*self);

        let tracked mut r = Resource::alloc(MapCarrier::<K, V>::unit());
        tracked_swap(&mut self.r, &mut r);

        let self_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: r.value().frac.owning_map(),
                dup: r.value().frac.dup_map().remove_keys(s),
            },
        };

        let res_carrier = MapCarrier {
            auth: AuthCarrier::Frac,
            frac: FracCarrier::Frac {
                owning: r.value().frac.owning_map(),
                dup: r.value().frac.dup_map().restrict(s),
            },
        };

        assert(r.value().frac == MapCarrier::op(self_carrier, res_carrier).frac);
        let tracked (self_r, res_r) = r.split(self_carrier, res_carrier);
        self.r = self_r;
        GhostPersistentSubmap { r: res_r }
    }

    /// We can separate a single key out of a [`GhostPersistentSubmap`]
    pub proof fn split_points_to(tracked &mut self, k: K) -> (tracked result:
        GhostPersistentPointsTo<K, V>)
        requires
            old(self)@.contains_key(k),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.insert(result.key(), result.value()),
            result.key() == k,
            self@ == old(self)@.remove(k),
    {
        use_type_invariant(&*self);

        let tracked submap = self.split(set![k]);
        GhostPersistentPointsTo { submap }
    }

    /// Convert a [`GhostPersistentSubmap`] into a [`GhostPersistentPointsTo`]
    pub proof fn points_to(tracked self) -> (tracked r: GhostPersistentPointsTo<K, V>)
        requires
            self.is_points_to(),
        ensures
            self@ == map![r.key() => r.value()],
            self.id() == r.id(),
    {
        let tracked r = GhostPersistentPointsTo { submap: self };
        r.lemma_map_view();
        r
    }
}

impl<K, V> GhostPointsTo<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.submap.is_points_to()
    }

    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.submap.id()
    }

    /// Key-Value pair underlying the points to relationship
    pub open spec fn view(self) -> (K, V) {
        (self.key(), self.value())
    }

    /// Key of the points to
    pub closed spec fn key(self) -> K {
        self.submap.dom().choose()
    }

    /// Pointed-to value
    pub closed spec fn value(self) -> V {
        self.submap[self.key()]
    }

    /// Agreement between a [`GhostPointsTo`] and a corresponding [`GhostMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostMapAuth`] and a corresponding [`GhostPointsTo`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPointsTo`] is a key-value pair in the [`GhostMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostMapAuth<int, int>, tracked &pt: GhostPointsTo<int, int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         pt@ == (1int, 1int)
    ///     ensures
    ///         auth[1int] == 1int
    /// {
    ///     pt.agree(auth);
    ///     assert(auth[1int] == 1int);
    /// }
    /// ```
    pub proof fn agree(tracked self: &GhostPointsTo<K, V>, tracked auth: &GhostMapAuth<K, V>)
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains_pair(self.key(), self.value()),
    {
        use_type_invariant(self);
        use_type_invariant(auth);

        self.lemma_map_view();
        self.submap.agree(auth);
        assert(self.submap@ <= auth@);
        assert(self.submap@.contains_key(self.key()));
        assert(self.submap@.contains_pair(self.key(), self.value()));
    }

    /// We can combine two [`GhostPointsTo`]s into a [`GhostSubmap`]
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked self, tracked other: GhostPointsTo<K, V>) -> (tracked r:
        GhostSubmap<K, V>)
        requires
            self.id() == other.id(),
        ensures
            r.id() == self.id(),
            r@ == map![self.key() => self.value(), other.key() => other.value()],
            self.key() != other.key(),
    {
        use_type_invariant(&self);
        use_type_invariant(&other);

        let tracked mut submap = self.submap();
        submap.combine_points_to(other);

        submap
    }

    /// Shows that if a two [`GhostPointsTo`]s are not owning the same key
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self.key() != other.key(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.disjoint(&other.submap);
    }

    /// Shows that if a [`GhostPointsTo`] and a [`GhostSubmap`] are not owning the same key
    pub proof fn disjoint_submap(tracked &mut self, tracked other: &GhostSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other.dom().contains(self.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.disjoint(other);
    }

    /// Shows that if a [`GhostPointsTo`] and a [`GhostPersistentSubmap`] are not owning the same key
    pub proof fn disjoint_persistent_submap(
        tracked &mut self,
        tracked other: &GhostPersistentSubmap<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other.dom().contains(self.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.disjoint_persistent(other);
    }

    /// Shows that if a [`GhostPointsTo`] and a [`GhostPersistentPointsTo`] are not owning the same key
    pub proof fn disjoint_persistent(
        tracked &mut self,
        tracked other: &GhostPersistentPointsTo<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self.key() != other.key(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.disjoint_persistent_points_to(other);
    }

    /// Update pointed to value
    pub proof fn update(tracked &mut self, tracked auth: &mut GhostMapAuth<K, V>, v: V)
        requires
            old(self).id() == old(auth).id(),
        ensures
            self.id() == old(self).id(),
            auth.id() == old(auth).id(),
            self.key() == old(self).key(),
            self@ == (self.key(), v),
            auth@ == old(auth)@.union_prefer_right(map![self.key() => v]),
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_submap_of_op;

        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        let ghost old_dom = self.submap.dom();
        self.lemma_map_view();
        let m = map![self.key() => v];
        assert(self.submap@.union_prefer_right(m) == m);
        self.submap.update(auth, m);
    }

    /// Convert the [`GhostPointsTo`] a [`GhostSubmap`]
    pub proof fn submap(tracked self) -> (tracked r: GhostSubmap<K, V>)
        ensures
            r.id() == self.id(),
            r@ == map![self.key() => self.value()],
    {
        self.lemma_map_view();
        self.submap
    }

    proof fn lemma_map_view(tracked &self)
        ensures
            self.submap@ == map![self.key() => self.value()],
    {
        use_type_invariant(self);
        let key = self.key();
        let target_dom = set![key];

        assert(self.submap@.dom().len() == 1);
        assert(target_dom.len() == 1);

        assert(self.submap@.dom().finite());
        assert(target_dom.finite());

        assert(self.submap@.dom().contains(key));
        assert(target_dom.contains(key));

        assert(self.submap@.dom().remove(key).len() == 0);
        assert(target_dom.remove(key).len() == 0);

        assert(self.submap@.dom() =~= target_dom);
        assert(self.submap@ == map![self.key() => self.value()]);
    }

    /// Can be used to learn what the key-value pair of [`GhostPointsTo`] is
    pub proof fn lemma_view(self)
        ensures
            self@ == (self.key(), self.value()),
    {
    }

    /// Convert a [`GhostPointsTo`] into a [`GhostPersistentPointsTo`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentPointsTo<K, V>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        use_type_invariant(&self);
        self.submap.persist().points_to()
    }
}

impl<K, V> GhostPersistentPointsTo<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.submap.is_points_to()
    }

    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.submap.id()
    }

    /// Key-Value pair underlying the points to relationship
    pub open spec fn view(self) -> (K, V) {
        (self.key(), self.value())
    }

    /// Key of the points to
    pub closed spec fn key(self) -> K {
        self.submap.dom().choose()
    }

    /// Pointed-to value
    pub closed spec fn value(self) -> V {
        self.submap[self.key()]
    }

    /// Duplicate the [`GhostPersistentPointsTo`]
    pub proof fn duplicate(tracked &mut self) -> (tracked result: GhostPersistentPointsTo<K, V>)
        ensures
            self.id() == result.id(),
            old(self).id() == self.id(),
            old(self)@ == self@,
            result@ == self@,
    {
        use_type_invariant(&*self);
        let tracked submap = self.submap.duplicate();
        GhostPersistentPointsTo { submap }
    }

    /// Agreement between a [`GhostPersistentPointsTo`] and a corresponding [`GhostMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostMapAuth`] and a corresponding [`GhostPersistentPointsTo`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentPointsTo`] is a key-value pair in the [`GhostMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostMapAuth<int, int>, tracked &pt: GhostPersistentPointsTo<int, int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         pt@ == (1int, 1int)
    ///     ensures
    ///         auth[1int] == 1int
    /// {
    ///     pt.agree(auth);
    ///     assert(auth[1int] == 1int);
    /// }
    /// ```
    pub proof fn agree(
        tracked self: &GhostPersistentPointsTo<K, V>,
        tracked auth: &GhostMapAuth<K, V>,
    )
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains_pair(self.key(), self.value()),
    {
        use_type_invariant(self);
        use_type_invariant(auth);

        self.lemma_map_view();
        self.submap.agree(auth);
        assert(self.submap@ <= auth@);
        assert(self.submap@.contains_key(self.key()));
    }

    /// We can combine two [`GhostPersistentPointsTo`]s into a [`GhostPersistentSubmap`]
    pub proof fn combine(
        tracked self,
        tracked other: GhostPersistentPointsTo<K, V>,
    ) -> (tracked submap: GhostPersistentSubmap<K, V>)
        requires
            self.id() == other.id(),
        ensures
            submap.id() == self.id(),
            submap@ == map![self.key() => self.value(), other.key() => other.value()],
            self.key() != other.key() ==> submap@.len() == 2,
            self.key() == other.key() ==> submap@.len() == 1,
    {
        use_type_invariant(&self);
        use_type_invariant(&other);

        let tracked mut submap = self.submap();
        submap.combine_points_to(other);

        submap
    }

    /// When we have a [`GhostPersistentPointsTo`] and a [`GhostPointsTo`], we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostPointsTo<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self.key() != other.key(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.disjoint_submap(&other.submap);
    }

    /// When we have a [`GhostPersistentPointsTo`] and a [`GhostSubmap`], we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_submap(tracked &mut self, tracked other: &GhostSubmap<K, V>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other@.contains_key(self.key()),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.disjoint(&other);
    }

    /// Shows that if a client has two [`GhostPersistentPointsTo`]s they are either disjoint or
    /// agreeing in values in the intersection
    pub proof fn intersection_agrees(
        tracked &mut self,
        tracked other: &GhostPersistentPointsTo<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self.key() == other.key() ==> self.value() == other.value(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.intersection_agrees_points_to(&other);
    }

    /// Shows that if a [`GhostPersistentPointsTo`] and a [`GhostSubmap`] are not owning the same key
    pub proof fn intersection_agrees_submap(
        tracked &mut self,
        tracked other: &GhostPersistentSubmap<K, V>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            other@.contains_key(self.key()) ==> other@[self.key()] == self.value(),
    {
        use_type_invariant(&*self);
        use_type_invariant(other);
        self.submap.intersection_agrees(other);
    }

    /// Convert the [`GhostPersistentPointsTo`] a [`GhostPersistentSubmap`]
    pub proof fn submap(tracked self) -> (tracked r: GhostPersistentSubmap<K, V>)
        ensures
            r.id() == self.id(),
            r@ == map![self.key() => self.value()],
    {
        self.lemma_map_view();
        self.submap
    }

    proof fn lemma_map_view(tracked &self)
        ensures
            self.submap@ == map![self.key() => self.value()],
    {
        use_type_invariant(self);
        let key = self.key();
        let target_dom = set![key];

        assert(self.submap@.dom().len() == 1);
        assert(target_dom.len() == 1);

        assert(self.submap@.dom().finite());
        assert(target_dom.finite());

        assert(self.submap@.dom().contains(key));
        assert(target_dom.contains(key));

        assert(self.submap@.dom().remove(key).len() == 0);
        assert(target_dom.remove(key).len() == 0);

        assert(self.submap@.dom() =~= target_dom);
        assert(self.submap@ == map![self.key() => self.value()]);
    }

    /// Can be used to learn what the key-value pair of [`GhostPersistentPointsTo`] is
    pub proof fn lemma_view(self)
        ensures
            self@ == (self.key(), self.value()),
    {
    }
}

} // verus!
