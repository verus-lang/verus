//! Maps that support ownership of keys
//!
//! - [`GhostMapAuth<K, V>`] represents authoritative ownership of the entire map;
//! - [`GhostSubmap<K, V>`] represents client ownership of a submap;
//! - [`GhostPointsTo<K, V>`] represents client ownership of a single key-value pair.
//!
//! Updating the authoritative `GhostMapAuth<K, V>` requires a `GhostSubmap<K,
//! V>` containing the keys being updated.
//!
//! `GhostSubmap<K, V>`s can be combined or split.
//! Whenever a `GhostSubmap<K, V>` can be used, we can instead use a `GhostPointsTo<K, V>` (but not vice-versa).
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
// This struct represents the underlying resource algebra for GhostMaps
struct MapCarrier<K, V> {
    auth: Option<Option<Map<K, V>>>,
    frac: Option<Map<K, V>>,
}

impl<K, V> PCM for MapCarrier<K, V> {
    closed spec fn valid(self) -> bool {
        match self.frac {
            None => false,
            Some(f) => match self.auth {
                None => true,
                Some(None) => false,
                Some(Some(a)) => f.submap_of(a),
            },
        }
    }

    closed spec fn op(self, other: Self) -> Self {
        MapCarrier {
            auth: if self.auth is Some {
                if other.auth is Some {
                    Some(None)
                } else {
                    self.auth
                }
            } else {
                other.auth
            },
            frac: match self.frac {
                None => None,
                Some(sfr) => match other.frac {
                    None => None,
                    Some(ofr) => {
                        if sfr.dom().disjoint(ofr.dom()) {
                            Some(sfr.union_prefer_right(ofr))
                        } else {
                            None
                        }
                    },
                },
            },
        }
    }

    closed spec fn unit() -> Self {
        MapCarrier { auth: None, frac: Some(Map::empty()) }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_op_frac_submap_of;

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

broadcast proof fn lemma_op_frac_submap_of<K, V>(a: MapCarrier<K, V>, b: MapCarrier<K, V>)
    requires
        #[trigger] MapCarrier::op(a, b).valid(),
    ensures
        a.frac.unwrap() <= MapCarrier::op(a, b).frac.unwrap(),
        b.frac.unwrap() <= MapCarrier::op(a, b).frac.unwrap(),
{
}

/// A resource that has the authoritative ownership on the entire map
#[verifier::reject_recursive_types(K)]
pub struct GhostMapAuth<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/// A resource that has client ownership of a submap
#[verifier::reject_recursive_types(K)]
pub struct GhostSubmap<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/// A resource that has client ownership of a single key-value pair
#[verifier::reject_recursive_types(K)]
pub struct GhostPointsTo<K, V> {
    submap: GhostSubmap<K, V>,
}

/// An implementation of a resource for owning a subset of keys in a map.
///
impl<K, V> GhostMapAuth<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is Some
        &&& self.r.value().auth.unwrap() is Some
        &&& self.r.value().frac == Some(Map::<K, V>::empty())
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Logically underlying [`Map`]
    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().auth.unwrap().unwrap()
    }

    /// Domain of the `GhostMapAuth`
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

    /// Instantiate a dummy `GhostMapAuth`
    pub proof fn dummy() -> (tracked result: GhostMapAuth<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        auth
    }

    /// Extract the `GhostMapAuth` from a mutable reference
    pub proof fn take(tracked &mut self) -> (tracked result: GhostMapAuth<K, V>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);
        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

    /// Create an empty `GhostSubmap`
    pub proof fn empty(tracked &self) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == self.id(),
            result@ == Map::<K, V>::empty(),
    {
        use_type_invariant(self);
        GhostSubmap::<K, V>::empty(self.id())
    }

    /// Insert a `Map` of values, receiving the `GhostSubmap` that asserts ownership over the key
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
        broadcast use lemma_op_frac_submap_of;

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);

        use_type_invariant(&mself);
        assert(mself.inv());
        let tracked mut r = mself.r;

        let rr = MapCarrier {
            auth: Some(Some(r.value().auth.unwrap().unwrap().union_prefer_right(m))),
            frac: Some(m),
        };

        let tracked r_upd = r.update(rr);

        let arr = MapCarrier { auth: r_upd.value().auth, frac: Some(Map::empty()) };

        let frr = MapCarrier { auth: None, frac: r_upd.value().frac };

        assert(r_upd.value() == MapCarrier::op(arr, frr));
        let tracked (ar, fr) = r_upd.split(arr, frr);
        self.r = ar;
        GhostSubmap { r: fr }
    }

    /// Insert a key-value pair, receiving the `GhostPointsTo` that asserts ownerships over the key.
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
    pub proof fn delete(tracked &mut self, tracked f: GhostSubmap<K, V>)
        requires
            f.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.remove_keys(f@.dom()),
    {
        broadcast use lemma_submap_of_trans;
        broadcast use lemma_op_frac_submap_of;

        use_type_invariant(&*self);
        use_type_invariant(&f);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut r = mself.r;

        r = r.join(f.r);

        let ra = r.value().auth.unwrap().unwrap();
        let ra_new = ra.remove_keys(f@.dom());

        let rnew = MapCarrier { auth: Some(Some(ra_new)), frac: Some(Map::empty()) };

        self.r = r.update(rnew);
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

    /// Create a new `GhostMapAuth` from a `Map`.
    /// Gives the other half of ownership in the form of a `GhostSubmap`.
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
        let tracked rr = Resource::alloc(MapCarrier { auth: Some(Some(m)), frac: Some(m) });

        let arr = MapCarrier { auth: Some(Some(m)), frac: Some(Map::empty()) };

        let frr = MapCarrier { auth: None, frac: Some(m) };

        assert(rr.value() == MapCarrier::op(arr, frr));
        let tracked (ar, fr) = rr.split(arr, frr);
        (GhostMapAuth { r: ar }, GhostSubmap { r: fr })
    }
}

/// A resource representing ownership of a subset of the domain of the map
/// The existence of a `GhostSubmap` implies that:
///  - Those keys will remain in the map;
///  - Those keys will remain pointing to the same values (unless explicitely `update`d)
///  - All other `GhostSubmap`/`GhostPointsTo` are disjoint subsets of the domain
impl<K, V> GhostSubmap<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is None
        &&& self.r.value().frac is Some
    }

    /// Checks whether the `GhostSubmap` refers to a single key (and thus can be converted to a
    /// `GhostPointsTo`).
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
        self.r.value().frac.unwrap()
    }

    /// Domain of the `GhostSubmap`
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

    /// Instantiate a dummy `GhostSubmap`
    pub proof fn dummy() -> (tracked result: GhostSubmap<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        submap
    }

    /// Instantiate an empty `GhostSubmap` of a particular id
    pub proof fn empty(id: int) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == id,
            result@ == Map::<K, V>::empty(),
    {
        let tracked r = Resource::create_unit(id);
        GhostSubmap { r }
    }

    /// Extract the `GhostSubmap` from a mutable reference, leaving behind an empty map.
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

    /// Agreement between a `GhostSubmap` and a corresponding `GhostMapAuth`
    ///
    /// Verus might not have full context of the `GhostMapAuth` and a corresponding `GhostSubmap`.
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the `GhostSubmap` is a submap of the `GhostMapAuth`.
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
        assert(self.r.value().frac.unwrap() <= joined.value().frac.unwrap());
    }

    /// Combining two `GhostSubmap`s is possible.
    /// We consume the input `GhostSubmap` and merge it into the first.
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

    /// Combining a `GhostPointsTo` into `GhostSubmap` is possible, in a similar way to the way to combine
    /// `GhostSubmap`s.
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

    /// When we have two `GhostSubmap`s we can prove that they have disjoint domains.
    /// This can be used to prove contradictions.
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

    /// When we have a `GhostSubmap` and a `GhostPointsTo`, we can prove that they are in disjoint
    /// domains. This can be used to prove contradictions.
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

    /// We can split a `GhostSubmap` based on a set of keys in its domain.
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

        let rr1 = MapCarrier { auth: None, frac: Some(r.value().frac.unwrap().remove_keys(s)) };

        let rr2 = MapCarrier { auth: None, frac: Some(r.value().frac.unwrap().restrict(s)) };

        assert(r.value().frac == MapCarrier::op(rr1, rr2).frac);
        let tracked (r1, r2) = r.split(rr1, rr2);
        self.r = r1;
        GhostSubmap { r: r2 }
    }

    /// We can separate a single key out of a `GhostSubmap`
    pub proof fn split_points_to(tracked &mut self, k: K) -> (tracked result: GhostPointsTo<K, V>)
        requires
            old(self)@.contains_key(k),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.insert(result.key(), result.value()),
            result.key() == k,
            self@.dom() =~= old(self)@.dom().remove(k),
    {
        use_type_invariant(&*self);

        let tracked submap = self.split(set![k]);
        GhostPointsTo { submap }
    }

    /// When we have both the `GhostMapAuth` and a `GhostSubmap` we can update the values for a
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
        broadcast use lemma_op_frac_submap_of;

        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        let tracked mut mself = Self::dummy();
        tracked_swap(self, &mut mself);
        let tracked mut fr = mself.r;

        let tracked mut mauth = GhostMapAuth::<K, V>::dummy();
        tracked_swap(auth, &mut mauth);
        let tracked mut ar = mauth.r;

        fr.validate_2(&ar);
        let tracked mut r = fr.join(ar);

        assert(r.value().frac == fr.value().frac);

        let rr = MapCarrier {
            auth: Some(Some(r.value().auth.unwrap().unwrap().union_prefer_right(m))),
            frac: Some(r.value().frac.unwrap().union_prefer_right(m)),
        };

        let tracked r_upd = r.update(rr);

        let arr = MapCarrier { auth: r_upd.value().auth, frac: Some(Map::empty()) };

        let frr = MapCarrier { auth: None, frac: r_upd.value().frac };

        assert(r_upd.value().frac == MapCarrier::op(arr, frr).frac);
        let tracked (ar, fr) = r_upd.split(arr, frr);
        auth.r = ar;
        self.r = fr;
    }

    /// Converting a `GhostSubmap` into a `GhostPointsTo`
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
}

/// A resource representing ownership over a single key in the domain of the map
/// The existence of a `GhostPointsTo` implies that:
///  - The key will remain in the map;
///  - The key will remain pointing to the same value (unless explicitely `update`d)
///  - All other `GhostSubmap`/`GhostPointsTo` are disjoint subsets of the domain
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

    /// Agreement between a `GhostPointsTo` and a corresponding `GhostMapAuth`
    ///
    /// Verus might not have full context of the `GhostMapAuth` and a corresponding `GhostPointsTo`.
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the `GhostPointsTo` is a submap of the `GhostMapAuth`.
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

        self.submap.agree(auth);
        assert(self.submap@ <= auth@);
        assert(self.submap@.contains_key(self.key()));
    }

    /// We can combine two `GhostPointsTo`s into a `GhostSubmap`
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

    /// Shows that if a two `GhostPointsTo`s are not owning the same key
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

    /// Shows that if a `GhostPointsTo` and a `GhostSubmap` are not owning the same key
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
        broadcast use lemma_op_frac_submap_of;

        use_type_invariant(&*self);
        use_type_invariant(&*auth);

        let ghost old_dom = self.submap.dom();
        self.lemma_map_view();
        let m = map![self.key() => v];
        assert(self.submap@.union_prefer_right(m) == m);
        self.submap.update(auth, m);
        // assert(self.submap@ == m);
    }

    /// Convert the `GhostPointsTo` a `GhostSubset`
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

    /// Can be used to learn what the key-value pair of `GhostPointsTo` is
    pub proof fn lemma_view(self)
        ensures
            self@ == (self.key(), self.value()),
    {
    }
}

} // verus!
