//! Implementation of a resource for ownership of subsets of values in a set
//!
//! - [`GhostSetAuth<T>`] represents authoritative ownership of the entire set;
//! - [`GhostSubset<T>`] represents client ownership of some subset;
//! - [`GhostPersistentSubset<T>`] represents duplicable client knowledge of some persistent subset;
//! - [`GhostSingleton<T>`] represents client ownership of a singleton.
//! - [`GhostPersistentSingleton<T>`] represents duplicable client knowledge of a persistent singleton;
//!
//! Updating the authoritative `GhostSetAuth<T>` requires a `GhostSubset<T>` containing
//! the values being updated.
//!
//! `GhostSubset<T>`s can be combined or split.
//! Whenever a `GhostSubset<T>` can be used, we can instead use a `GhostSingleton<T>` (but not vice-versa).
//!
//! `GhostPersistentSubset<T>`s can be combined or split.
//! Whenever a `GhostPersistentSubset<T>` can be used, we can instead use a `GhostPersistentSingleton<T>` (but not vice-versa).
//!
//! ### Example
//!
//! ```
//! fn example_use() {
//!     let tracked (mut auth, mut sub) = GhostSetAuth::new(set![1u8, 2u8, 3u8]);
//!
//!     // Allocate some more values in the auth set, receiving a new subset.
//!     let tracked sub2 = auth.insert_set(set![4u8, 5u8]);
//!     proof { sub.combine(sub2); }
//!
//!     // Allocate a single value in the auth set, receiving a points to
//!     let tracked pt1 = auth.insert(6u8);
//!     proof { sub.combine_points_to(pt1); }
//!
//!     // Delete some values in the auth set, by returning corresponding subset.
//!     let tracked sub3 = sub.split(set![3u8, 4u8]);
//!     proof { auth.delete(sub3); }
//!
//!     // Split the subset into a singleton and a subset
//!     let tracked pt1 = sub.split_singleton(1u8);
//!     let tracked sub4 = sub.split(set![5u8, 6u8]);
//!
//!     // In general, we might need to call agree() to establish the fact that
//!     // a singleton/subset has the same values as the auth set.  Here, Verus
//!     // doesn't need agree because it can track where both the auth, singleton
//!     // and subset came from.
//!     proof { sub.agree(&auth); }
//!     proof { pt1.agree(&auth); }
//!     proof { sub4.agree(&auth); }
//!
//!     assert(auth@.contains(pt1@));
//!     assert(sub4@ <= auth@);
//!     assert(sub@ <= auth@);
//!
//!     // Persist and duplicate the submap
//!     let mut psub1 = sub.persist();
//!     assert(psub1.contains(2u8));
//!     let psub2 = psub1.duplicate();
//!     assert(psub2.contains(2u8));
//!
//!     // Not shown in this simple example is the main use case of this resource:
//!     // maintaining an invariant between GhostSetAuth<T> and some exec-mode
//!     // shared state with a map view (e.g., HashSet<T>), which states that
//!     // the Set<T> view of GhostSetAuth<T> is the same as the view of the
//!     // HashSet<T>, and then handing out a GhostSubset<T> to different
//!     // clients that might need to operate on different values in the set
//! }
//! ```
use super::super::map::*;
use super::super::map_lib::*;
use super::super::modes::*;
use super::super::pcm::*;
use super::super::prelude::*;
use super::super::set::*;
use super::super::set_lib::*;
use super::map::GhostMapAuth;
use super::map::GhostPersistentPointsTo;
use super::map::GhostPersistentSubmap;
use super::map::GhostPointsTo;
use super::map::GhostSubmap;

verus! {

broadcast use super::super::group_vstd_default;

/// A resource that has the authoritative ownership on the entire set
///
/// For ownership of only a subset of values, see [`GhostSubset`].
/// For ownership of a single value, see [`GhostSingleton`].
#[verifier::reject_recursive_types(T)]
pub struct GhostSetAuth<T> {
    map: GhostMapAuth<T, ()>,
}

/// A resource that has client ownership of a subset
///
/// The existence of a [`GhostSubset`] implies that:
///  - Those values will remain in the set unless ;
///  - Those values will remain in the set (unless the onwer of the [`GhostSubset`] deletes it using [`GhostSetAuth::delete`]);
///  - All other [`GhostSubset`]/[`GhostSingleton`] are disjoint from it
#[verifier::reject_recursive_types(T)]
pub struct GhostSubset<T> {
    map: GhostSubmap<T, ()>,
}

/// A resource that asserts duplicable client knowledge of a persistent subset
///
/// For the authoritative resource of the whole set, see [`GhostSetAuth`]
#[verifier::reject_recursive_types(T)]
pub struct GhostPersistentSubset<T> {
    map: GhostPersistentSubmap<T, ()>,
}

/// A resource that has client ownership of a singleton
///
/// The existence of a [`GhostSingleton`] implies that:
///  - The value will remain in the set;
///  - All other [`GhostSubset`]/[`GhostSingleton`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(T)]
pub struct GhostSingleton<T> {
    map: GhostPointsTo<T, ()>,
}

/// A resource that asserts duplicable client knowledge of a persistent singleton
///
/// For the authoritative resource of the whole set, see [`GhostSetAuth`]
#[verifier::reject_recursive_types(T)]
pub struct GhostPersistentSingleton<T> {
    map: GhostPersistentPointsTo<T, ()>,
}

impl<T> GhostSetAuth<T> {
    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`Set`]
    pub closed spec fn view(self) -> Set<T> {
        self.map@.dom()
    }

    /// Create a new [`GhostSetAuth`] from a [`Set`].
    /// Gives the other half of ownership in the form of a [`GhostSubset`]
    ///
    /// ```
    /// fn example() {
    ///     let s = set![1int, 2int];
    ///     let tracked (auth, sub) = GhostSetAuth::new(s);
    ///     assert(auth@ == s);
    ///     assert(sub@ == auth@);
    /// }
    /// ```
    pub proof fn new(s: Set<T>) -> (tracked result: (GhostSetAuth<T>, GhostSubset<T>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == s,
            result.1@ == s,
    {
        let m = s.mk_map(|k: T| ());
        let tracked (map, submap) = GhostMapAuth::new(m);
        (GhostSetAuth { map }, GhostSubset { map: submap })
    }

    /// Instantiate a dummy [`GhostSetAuth`]
    pub proof fn dummy() -> (tracked result: GhostSetAuth<T>) {
        let tracked map = GhostMapAuth::dummy();
        GhostSetAuth { map }
    }

    /// Extract the [`GhostSetAuth`] from a mutable reference
    pub proof fn take(tracked &mut self) -> (tracked result: GhostSetAuth<T>)
        ensures
            result == *old(self),
    {
        let tracked map = self.map.take();
        GhostSetAuth { map }
    }

    /// Create an empty [`GhostSubset`]
    pub proof fn empty(tracked &self) -> (tracked result: GhostSubset<T>)
        ensures
            result.id() == self.id(),
            result@ == Set::<T>::empty(),
    {
        let tracked map = self.map.empty();
        GhostSubset { map }
    }

    /// Insert a [`Set`] of values, receiving the [`GhostSubset`] that asserts ownership over the set inserted.
    ///
    /// ```
    /// proof fn insert_set_example(tracked mut m: GhostSetAuth<int>) -> (tracked r: GhostSubset<int>)
    ///     requires
    ///         m@.contains(1int),
    ///         m@.contains(2int),
    /// {
    ///     let tracked subset = m.insert_set(set![1int, 2int]);
    ///     // do something with the subset
    ///     subset
    /// }
    /// ```
    pub proof fn insert_set(tracked &mut self, s: Set<T>) -> (tracked result: GhostSubset<T>)
        requires
            old(self)@.disjoint(s),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union(s),
            result.id() == self.id(),
            result@ == s,
    {
        let m = s.mk_map(|k: T| ());
        let tracked submap = self.map.insert_map(m);
        GhostSubset { map: submap }
    }

    /// Insert a value, receiving the [`GhostSingleton`] that asserts ownerships over the value.
    ///
    /// ```
    /// proof fn insert_example(tracked mut s: GhostSetAuth<int>) -> (tracked r: GhostSingleton<int>)
    ///     requires
    ///         !m@.contains(1int),
    /// {
    ///     let tracked singleton = m.insert(1);
    ///     // do something with the singleton
    ///     singleton
    /// }
    /// ```
    pub proof fn insert(tracked &mut self, v: T) -> (tracked result: GhostSingleton<T>)
        requires
            !old(self)@.contains(v),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(v),
            result.id() == self.id(),
            result@ == v,
    {
        let tracked map = self.map.insert(v, ());
        GhostSingleton { map }
    }

    /// Delete a set of values
    /// ```
    /// proof fn delete(tracked mut auth: GhostSetAuth<int>)
    ///     requires
    ///         auth@.contains(1int),
    ///         auth@.contains(2int),
    ///     ensures
    ///         old(auth)@ == auth@
    /// {
    ///     let tracked submap = auth.insert_set(set![1int, 2int]);
    ///     // do something with the submap
    ///     auth.delete(submap)
    /// }
    /// ```
    pub proof fn delete(tracked &mut self, tracked f: GhostSubset<T>)
        requires
            f.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.difference(f@),
    {
        self.map.delete(f.map);
    }

    /// Delete a single key from the map
    /// ```
    /// proof fn delete_key(tracked mut auth: GhostSetAuth<int>)
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
    pub proof fn delete_singleton(tracked &mut self, tracked p: GhostSingleton<T>)
        requires
            p.id() == old(self).id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.remove(p@),
    {
        self.map.delete_points_to(p.map);
    }
}

impl<T> GhostSubset<T> {
    /// Checks whether the [`GhostSubset`] refers to a single value (and thus can be converted to a
    /// [`GhostSingleton`]).
    pub open spec fn is_singleton(self) -> bool {
        &&& self@.len() == 1
        &&& self@.finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`Set`]
    pub closed spec fn view(self) -> Set<T> {
        self.map@.dom()
    }

    /// Instantiate a dummy [`GhostSubset`]
    pub proof fn dummy() -> (tracked result: GhostSubset<T>) {
        let tracked map = GhostSubmap::dummy();
        GhostSubset { map }
    }

    /// Instantiate an empty [`GhostSubset`] of a particular id
    pub proof fn empty(id: int) -> (tracked result: GhostSubset<T>)
        ensures
            result.id() == id,
            result@ == Set::<T>::empty(),
    {
        let tracked map = GhostSubmap::empty(id);
        GhostSubset { map }
    }

    /// Extract the [`GhostSubset`] from a mutable reference, leaving behind an empty map.
    pub proof fn take(tracked &mut self) -> (tracked result: GhostSubset<T>)
        ensures
            old(self).id() == self.id(),
            self@.is_empty(),
            result == *old(self),
            result.id() == self.id(),
    {
        let tracked map = self.map.take();
        GhostSubset { map }
    }

    /// Agreement between a [`GhostSubset`] and a corresponding [`GhostSetAuth`]
    ///
    /// Verus might not have full context of the [`GhostSetAuth`] and a corresponding [`GhostSubset`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostSubset`] is a submap of the [`GhostSetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostSetAuth<int>, tracked &sub: GhostSubset<int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         sub@.contains(1int),
    ///     ensures
    ///         auth@.contains(1int),
    /// {
    ///     sub.agree(auth);
    ///     assert(sub@ <= auth@);
    ///     assert(auth.contains(1int));
    /// }
    /// ```
    pub proof fn agree(tracked self: &GhostSubset<T>, tracked auth: &GhostSetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        self.map.agree(&auth.map);
    }

    /// Combining two [`GhostSubset`]s is possible.
    /// We consume the input [`GhostSubset`] and merge it into the first.
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked &mut self, tracked other: GhostSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union(other@),
            old(self)@.disjoint(other@),
    {
        self.map.combine(other.map);
    }

    /// Combining a [`GhostSingleton`] into [`GhostSubset`] is possible, in a similar way to the way to combine
    /// [`GhostSubset`]s.
    pub proof fn combine_singleton(tracked &mut self, tracked other: GhostSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(other@),
            !old(self)@.contains(other@),
    {
        self.map.combine_points_to(other.map);
    }

    /// When we have two [`GhostSubset`]s we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.disjoint(other@),
    {
        self.map.disjoint(&other.map);
    }

    /// When we have a [`GhostSubset`] and a [`GhostPersistentSubset`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent(tracked &mut self, tracked other: &GhostPersistentSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.disjoint(other@),
    {
        self.map.disjoint_persistent(&other.map);
    }

    /// When we have a [`GhostSubset`] and a [`GhostSingleton`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_singleton(tracked &mut self, tracked other: &GhostSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains(other@),
    {
        self.map.disjoint_points_to(&other.map);
    }

    /// When we have a [`GhostSubset`] and a [`GhostPersistentSingleton`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent_singleton(
        tracked &mut self,
        tracked other: &GhostPersistentSingleton<T>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains(other@),
    {
        self.map.disjoint_persistent_points_to(&other.map);
    }

    /// We can split a [`GhostSubset`] based on a set of values
    pub proof fn split(tracked &mut self, s: Set<T>) -> (tracked result: GhostSubset<T>)
        requires
            s <= old(self)@,
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.union(result@),
            result@ =~= s,
            self@ =~= old(self)@ - s,
    {
        let tracked map = self.map.split(s);
        GhostSubset { map }
    }

    /// We can separate a single value out of a [`GhostSubset`]
    pub proof fn split_singleton(tracked &mut self, v: T) -> (tracked result: GhostSingleton<T>)
        requires
            old(self)@.contains(v),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.insert(result@),
            result@ == v,
            self@ =~= old(self)@.remove(v),
    {
        let tracked map = self.map.split_points_to(v);
        GhostSingleton { map }
    }

    /// Converting a [`GhostSubset`] into a [`GhostSingleton`]
    pub proof fn singleton(tracked self) -> (tracked r: GhostSingleton<T>)
        requires
            self.is_singleton(),
        ensures
            self@ == set![r@],
            self.id() == r.id(),
    {
        let tracked map = self.map.points_to();
        GhostSingleton { map }
    }

    /// Converting a [`GhostSubset`] into a [`GhostPersistentSubset`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentSubset<T>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        let tracked map = self.map.persist();
        GhostPersistentSubset { map }
    }
}

impl<T> GhostPersistentSubset<T> {
    /// Checks whether the [`GhostPersistentSubset`] refers to a single key (and thus can be converted to a
    /// [`GhostPersistentPointsTo`]).
    pub open spec fn is_singleton(self) -> bool {
        &&& self@.len() == 1
        &&& self@.finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`Set`]
    pub closed spec fn view(self) -> Set<T> {
        self.map@.dom()
    }

    /// Instantiate a dummy [`GhostPersistentSubset`]
    pub proof fn dummy() -> (tracked result: GhostPersistentSubset<T>) {
        let tracked map = GhostPersistentSubmap::dummy();
        GhostPersistentSubset { map }
    }

    /// Instantiate an empty [`GhostPersistentSubset`] of a particular id
    pub proof fn empty(id: int) -> (tracked result: GhostPersistentSubset<T>)
        ensures
            result.id() == id,
            result@ == Set::<T>::empty(),
    {
        let tracked map = GhostPersistentSubmap::empty(id);
        GhostPersistentSubset { map }
    }

    /// Duplicate the [`GhostPersistentSubset`]
    pub proof fn duplicate(tracked &mut self) -> (tracked result: GhostPersistentSubset<T>)
        ensures
            self.id() == result.id(),
            old(self).id() == self.id(),
            old(self)@ == self@,
            result@ == self@,
    {
        let tracked map = self.map.duplicate();
        GhostPersistentSubset { map }
    }

    /// Agreement between a [`GhostPersistentSubset`] and a corresponding [`GhostMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostMapAuth`] and a corresponding [`GhostPersistentSubset`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentSubset`] is a subset of the [`GhostMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostMapAuth<int, int>, tracked &sub: GhostPersistentSubset<int, int>)
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
    pub proof fn agree(tracked self: &GhostPersistentSubset<T>, tracked auth: &GhostSetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        self.map.agree(&auth.map);
    }

    /// Combining two [`GhostPersistentSubset`]s is possible.
    /// We consume the input [`GhostPersistentSubset`] and merge it into the first.
    /// We also learn that they agreed
    pub proof fn combine(tracked &mut self, tracked other: GhostPersistentSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.union(other@),
    {
        self.map.combine(other.map);
    }

    /// Combining a [`GhostPersistentSingleton`] into [`GhostPersistentSubset`] is possible, in a similar way to the way to combine
    /// [`GhostPersistentSubset`]s.
    pub proof fn combine_points_to(tracked &mut self, tracked other: GhostPersistentSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@.insert(other@),
    {
        self.map.combine_points_to(other.map);
    }

    /// When we have a [`GhostPersistentSubset`] and a [`GhostSubset`] we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@.disjoint(other@),
    {
        self.map.disjoint(&other.map);
    }

    /// When we have a [`GhostPersistentSubset`] and a [`GhostSingleton`], we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_singleton(tracked &mut self, tracked other: &GhostSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !self@.contains(other@),
    {
        self.map.disjoint_points_to(&other.map);
    }

    /// We can split a [`GhostPersistentSubset`] based on a set of keys in its domain.
    pub proof fn split(tracked &mut self, s: Set<T>) -> (tracked result: GhostPersistentSubset<T>)
        requires
            s <= old(self)@,
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.union(result@),
            result@ =~= s,
            self@ =~= old(self)@ - s,
    {
        let tracked map = self.map.split(s);
        GhostPersistentSubset { map }
    }

    /// We can separate a single value out of a [`GhostPersistentSubset`]
    pub proof fn split_singleton(tracked &mut self, v: T) -> (tracked result:
        GhostPersistentSingleton<T>)
        requires
            old(self)@.contains(v),
        ensures
            self.id() == old(self).id(),
            result.id() == self.id(),
            old(self)@ == self@.insert(result@),
            result@ == v,
            self@ =~= old(self)@.remove(v),
    {
        let tracked map = self.map.split_points_to(v);
        GhostPersistentSingleton { map }
    }

    /// Convert a [`GhostPersistentSubset`] into a [`GhostPersistentSingleton`]
    pub proof fn singleton(tracked self) -> (tracked r: GhostPersistentSingleton<T>)
        requires
            self.is_singleton(),
        ensures
            self@ == set![r@],
            self.id() == r.id(),
    {
        let tracked map = self.map.points_to();
        GhostPersistentSingleton { map }
    }
}

impl<T> GhostSingleton<T> {
    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Value owned by the singleton
    pub closed spec fn view(self) -> T {
        self.map@.0
    }

    /// Agreement between a [`GhostSingleton`] and a corresponding [`GhostSetAuth`]
    ///
    /// Verus might not have full context of the [`GhostSetAuth`] and a corresponding [`GhostSingleton`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostSingleton`] is a subset of the [`GhostSetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostSetAuth<int>, tracked &pt: GhostSingleton<int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         pt@ == 1int
    ///     ensures
    ///         auth@.contains(1int)
    /// {
    ///     pt.agree(auth);
    ///     assert(auth@.contains(1int));
    /// }
    /// ```
    pub proof fn agree(tracked self: &GhostSingleton<T>, tracked auth: &GhostSetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains(self@),
    {
        self.map.agree(&auth.map);
    }

    /// We can combine two [`GhostSingleton`]s into a [`GhostSubset`]
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked self, tracked other: GhostSingleton<T>) -> (tracked r: GhostSubset<
        T,
    >)
        requires
            self.id() == other.id(),
        ensures
            r.id() == self.id(),
            r@ == set![self@, other@],
            self@ != other@,
    {
        let tracked map = self.map.combine(other.map);
        GhostSubset { map }
    }

    /// Shows that if a two [`GhostSingleton`]s are not owning the same value
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ != other@,
    {
        self.map.disjoint(&other.map)
    }

    /// Shows that if a [`GhostSingleton`] and a [`GhostPersistentSingleton`] are not owning the same value
    pub proof fn disjoint_persistent(tracked &mut self, tracked other: &GhostPersistentSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ != other@,
    {
        self.map.disjoint_persistent(&other.map)
    }

    /// Shows that if a [`GhostSingleton`] and a [`GhostSubset`] are not owning the same value
    pub proof fn disjoint_subset(tracked &mut self, tracked other: &GhostSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other@.contains(self@),
    {
        self.map.disjoint_submap(&other.map);
    }

    /// Shows that if a [`GhostSingleton`] and a [`GhostPersistentSubset`] are not owning the same value
    pub proof fn disjoint_persistent_subset(
        tracked &mut self,
        tracked other: &GhostPersistentSubset<T>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other@.contains(self@),
    {
        self.map.disjoint_persistent_submap(&other.map);
    }

    /// Convert the [`GhostSingleton`] a [`GhostSubset`]
    pub proof fn subset(tracked self) -> (tracked r: GhostSubset<T>)
        ensures
            r.id() == self.id(),
            r@ == set![self@],
    {
        let tracked map = self.map.submap();
        GhostSubset { map }
    }

    /// Converting a [`GhostSingleton`] into a [`GhostPersistentSingleton`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentSingleton<T>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        let tracked map = self.map.persist();
        GhostPersistentSingleton { map }
    }
}

impl<T> GhostPersistentSingleton<T> {
    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Value known by the singleton
    pub closed spec fn view(self) -> T {
        self.map@.0
    }

    /// Duplicate the [`GhostPersistentSingleton`]
    pub proof fn duplicate(tracked &mut self) -> (tracked result: GhostPersistentSingleton<T>)
        ensures
            self.id() == result.id(),
            old(self).id() == self.id(),
            old(self)@ == self@,
            result@ == self@,
    {
        let tracked map = self.map.duplicate();
        GhostPersistentSingleton { map }
    }

    /// Agreement between a [`GhostPersistentSingleton`] and a corresponding [`GhostSetAuth`]
    ///
    /// Verus might not have full context of the [`GhostSetAuth`] and a corresponding [`GhostPersistentSingleton`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentSingleton`] is a subset of the [`GhostSetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostSetAuth<int>, tracked &pt: GhostPersistentSingleton<int>)
    ///     requires
    ///         auth.id() == sub.id(),
    ///         pt@ == 1int
    ///     ensures
    ///         auth@.contains(1int)
    /// {
    ///     pt.agree(auth);
    ///     assert(auth@.contains(1int));
    /// }
    /// ```
    pub proof fn agree(tracked self: &GhostPersistentSingleton<T>, tracked auth: &GhostSetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains(self@),
    {
        self.map.agree(&auth.map);
    }

    /// We can combine two [`GhostPersistentSingleton`]s into a [`GhostPersistentSubset`]
    pub proof fn combine(tracked self, tracked other: GhostPersistentSingleton<T>) -> (tracked r:
        GhostPersistentSubset<T>)
        requires
            self.id() == other.id(),
        ensures
            r.id() == self.id(),
            r@ == set![self@, other@],
            self@ != other@ ==> r@.len() == 2,
            self@ == other@ ==> r@.len() == 1,
    {
        let tracked map = self.map.combine(other.map);
        GhostPersistentSubset { map }
    }

    /// Shows that a [`GhostPersistentSingleton`] and a [`GhostSingleton`] are not owning the same value
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostSingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ != other@,
    {
        self.map.disjoint(&other.map)
    }

    /// Shows that if a [`GhostPersistentSingleton`] and a [`GhostSubset`] are not owning the same value
    pub proof fn disjoint_subset(tracked &mut self, tracked other: &GhostSubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            !other@.contains(self@),
    {
        self.map.disjoint_submap(&other.map);
    }

    /// Convert the [`GhostPersistentSingleton`] a [`GhostPersistentSubset`]
    pub proof fn subset(tracked self) -> (tracked r: GhostPersistentSubset<T>)
        ensures
            r.id() == self.id(),
            r@ == set![self@],
    {
        let tracked map = self.map.submap();
        GhostPersistentSubset { map }
    }
}

} // verus!
