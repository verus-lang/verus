//! Implementation of a resource for ownership of subsets of values in a set
//!
//! - [`GhostISetAuth<T>`] represents authoritative ownership of the entire set;
//! - [`GhostISubset<T>`] represents client ownership of some subset;
//! - [`GhostPersistentISubset<T>`] represents duplicable client knowledge of some persistent subset;
//! - [`GhostISingleton<T>`] represents client ownership of a singleton.
//! - [`GhostPersistentISingleton<T>`] represents duplicable client knowledge of a persistent singleton;
//!
//! Updating the authoritative `GhostISetAuth<T>` requires a `GhostISubset<T>` containing
//! the values being updated.
//!
//! `GhostISubset<T>`s can be combined or split.
//! Whenever a `GhostISubset<T>` can be used, we can instead use a `GhostISingleton<T>` (but not vice-versa).
//!
//! `GhostPersistentISubset<T>`s can be combined or split.
//! Whenever a `GhostPersistentISubset<T>` can be used, we can instead use a `GhostPersistentISingleton<T>` (but not vice-versa).
//!
//! ### Example
//!
//! ```
//! fn example_use() {
//!     let tracked (mut auth, mut sub) = GhostISetAuth::new(set![1u8, 2u8, 3u8]);
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
//!     // maintaining an invariant between GhostISetAuth<T> and some exec-mode
//!     // shared state with a map view (e.g., HashISet<T>), which states that
//!     // the ISet<T> view of GhostISetAuth<T> is the same as the view of the
//!     // HashISet<T>, and then handing out a GhostISubset<T> to different
//!     // clients that might need to operate on different values in the set
//! }
//! ```
use super::super::super::map::*;
use super::super::super::map_lib::*;
use super::super::super::modes::*;
use super::super::super::prelude::*;
use super::super::super::set::*;
use super::super::super::set_lib::*;
use super::super::Loc;
use super::imap::GhostIMapAuth;
use super::imap::GhostIPointsTo;
use super::imap::GhostISubmap;
use super::imap::GhostPersistentIPointsTo;
use super::imap::GhostPersistentISubmap;

verus! {

broadcast use super::super::super::group_vstd_default;

/// A resource that has the authoritative ownership on the entire set
///
/// For ownership of only a subset of values, see [`GhostISubset`].
/// For ownership of a single value, see [`GhostISingleton`].
#[verifier::reject_recursive_types(T)]
pub struct GhostISetAuth<T> {
    map: GhostIMapAuth<T, ()>,
}

/// A resource that has client ownership of a subset
///
/// The existence of a [`GhostISubset`] implies that:
///  - Those values will remain in the set unless ;
///  - Those values will remain in the set (unless the onwer of the [`GhostISubset`] deletes it using [`GhostISetAuth::delete`]);
///  - All other [`GhostISubset`]/[`GhostISingleton`] are disjoint from it
#[verifier::reject_recursive_types(T)]
pub struct GhostISubset<T> {
    map: GhostISubmap<T, ()>,
}

/// A resource that asserts duplicable client knowledge of a persistent subset
///
/// For the authoritative resource of the whole set, see [`GhostISetAuth`]
#[verifier::reject_recursive_types(T)]
pub struct GhostPersistentISubset<T> {
    map: GhostPersistentISubmap<T, ()>,
}

/// A resource that has client ownership of a singleton
///
/// The existence of a [`GhostISingleton`] implies that:
///  - The value will remain in the set;
///  - All other [`GhostISubset`]/[`GhostISingleton`] are disjoint subsets of the domain
#[verifier::reject_recursive_types(T)]
pub struct GhostISingleton<T> {
    map: GhostIPointsTo<T, ()>,
}

/// A resource that asserts duplicable client knowledge of a persistent singleton
///
/// For the authoritative resource of the whole set, see [`GhostISetAuth`]
#[verifier::reject_recursive_types(T)]
pub struct GhostPersistentISingleton<T> {
    map: GhostPersistentIPointsTo<T, ()>,
}

impl<T> GhostISetAuth<T> {
    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`ISet`]
    pub closed spec fn view(self) -> ISet<T> {
        self.map@.dom()
    }

    /// Create a new [`GhostISetAuth`] from a [`ISet`].
    /// Gives the other half of ownership in the form of a [`GhostISubset`]
    ///
    /// ```
    /// fn example() {
    ///     let s = set![1int, 2int];
    ///     let tracked (auth, sub) = GhostISetAuth::new(s);
    ///     assert(auth@ == s);
    ///     assert(sub@ == auth@);
    /// }
    /// ```
    pub proof fn new(s: ISet<T>) -> (tracked result: (GhostISetAuth<T>, GhostISubset<T>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == s,
            result.1@ == s,
    {
        let m = s.mk_map(|k: T| ());
        let tracked (map, submap) = GhostIMapAuth::new(m);
        (GhostISetAuth { map }, GhostISubset { map: submap })
    }

    /// Instantiate a dummy [`GhostISetAuth`]
    pub proof fn dummy() -> (tracked result: GhostISetAuth<T>) {
        let tracked map = GhostIMapAuth::dummy();
        GhostISetAuth { map }
    }

    /// Extract the [`GhostISetAuth`] from a mutable reference
    pub proof fn take(tracked &mut self) -> (tracked result: GhostISetAuth<T>)
        ensures
            result == *old(self),
    {
        let tracked map = self.map.take();
        GhostISetAuth { map }
    }

    /// Create an empty [`GhostISubset`]
    pub proof fn empty(tracked &self) -> (tracked result: GhostISubset<T>)
        ensures
            result.id() == self.id(),
            result@ == ISet::<T>::empty(),
    {
        let tracked map = self.map.empty();
        GhostISubset { map }
    }

    /// Insert a [`ISet`] of values, receiving the [`GhostISubset`] that asserts ownership over the set inserted.
    ///
    /// ```
    /// proof fn insert_set_example(tracked mut m: GhostISetAuth<int>) -> (tracked r: GhostISubset<int>)
    ///     requires
    ///         m@.contains(1int),
    ///         m@.contains(2int),
    /// {
    ///     let tracked subset = m.insert_set(set![1int, 2int]);
    ///     // do something with the subset
    ///     subset
    /// }
    /// ```
    pub proof fn insert_set(tracked &mut self, s: ISet<T>) -> (tracked result: GhostISubset<T>)
        requires
            old(self)@.disjoint(s),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.union(s),
            result.id() == final(self).id(),
            result@ == s,
    {
        let m = s.mk_map(|k: T| ());
        let tracked submap = self.map.insert_map(m);
        GhostISubset { map: submap }
    }

    /// Insert a value, receiving the [`GhostISingleton`] that asserts ownerships over the value.
    ///
    /// ```
    /// proof fn insert_example(tracked mut s: GhostISetAuth<int>) -> (tracked r: GhostISingleton<int>)
    ///     requires
    ///         !m@.contains(1int),
    /// {
    ///     let tracked singleton = m.insert(1);
    ///     // do something with the singleton
    ///     singleton
    /// }
    /// ```
    pub proof fn insert(tracked &mut self, v: T) -> (tracked result: GhostISingleton<T>)
        requires
            !old(self)@.contains(v),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(v),
            result.id() == final(self).id(),
            result@ == v,
    {
        let tracked map = self.map.insert(v, ());
        GhostISingleton { map }
    }

    /// Delete a set of values
    /// ```
    /// proof fn delete(tracked mut auth: GhostISetAuth<int>)
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
    pub proof fn delete(tracked &mut self, tracked f: GhostISubset<T>)
        requires
            f.id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.difference(f@),
    {
        self.map.delete(f.map);
    }

    /// Delete a single key from the map
    /// ```
    /// proof fn delete_key(tracked mut auth: GhostISetAuth<int>)
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
    pub proof fn delete_singleton(tracked &mut self, tracked p: GhostISingleton<T>)
        requires
            p.id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.remove(p@),
    {
        self.map.delete_points_to(p.map);
    }
}

impl<T> GhostISubset<T> {
    /// Checks whether the [`GhostISubset`] refers to a single value (and thus can be converted to a
    /// [`GhostISingleton`]).
    pub open spec fn is_singleton(self) -> bool {
        &&& self@.len() == 1
        &&& self@.finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`ISet`]
    pub closed spec fn view(self) -> ISet<T> {
        self.map@.dom()
    }

    /// Instantiate a dummy [`GhostISubset`]
    pub proof fn dummy() -> (tracked result: GhostISubset<T>) {
        let tracked map = GhostISubmap::dummy();
        GhostISubset { map }
    }

    /// Create an empty [`GhostISubset`]
    pub proof fn empty(tracked &self) -> (tracked result: GhostISubset<T>)
        ensures
            result.id() == self.id(),
            result@ == ISet::<T>::empty(),
    {
        let tracked map = self.map.empty();
        GhostISubset { map }
    }

    /// Extract the [`GhostISubset`] from a mutable reference, leaving behind an empty map.
    pub proof fn take(tracked &mut self) -> (tracked result: GhostISubset<T>)
        ensures
            old(self).id() == final(self).id(),
            final(self)@.is_empty(),
            result == *old(self),
            result.id() == final(self).id(),
    {
        let tracked map = self.map.take();
        GhostISubset { map }
    }

    /// Agreement between a [`GhostISubset`] and a corresponding [`GhostISetAuth`]
    ///
    /// Verus might not have full context of the [`GhostISetAuth`] and a corresponding [`GhostISubset`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostISubset`] is a submap of the [`GhostISetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostISetAuth<int>, tracked &sub: GhostISubset<int>)
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
    pub proof fn agree(tracked self: &GhostISubset<T>, tracked auth: &GhostISetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        self.map.agree(&auth.map);
    }

    /// Combining two [`GhostISubset`]s is possible.
    /// We consume the input [`GhostISubset`] and merge it into the first.
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked &mut self, tracked other: GhostISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.union(other@),
            old(self)@.disjoint(other@),
    {
        self.map.combine(other.map);
    }

    /// Combining a [`GhostISingleton`] into [`GhostISubset`] is possible, in a similar way to the way to combine
    /// [`GhostISubset`]s.
    pub proof fn combine_singleton(tracked &mut self, tracked other: GhostISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(other@),
            !old(self)@.contains(other@),
    {
        self.map.combine_points_to(other.map);
    }

    /// When we have two [`GhostISubset`]s we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@.disjoint(other@),
    {
        self.map.disjoint(&other.map);
    }

    /// When we have a [`GhostISubset`] and a [`GhostPersistentISubset`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent(tracked &mut self, tracked other: &GhostPersistentISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@.disjoint(other@),
    {
        self.map.disjoint_persistent(&other.map);
    }

    /// When we have a [`GhostISubset`] and a [`GhostISingleton`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_singleton(tracked &mut self, tracked other: &GhostISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !final(self)@.contains(other@),
    {
        self.map.disjoint_points_to(&other.map);
    }

    /// When we have a [`GhostISubset`] and a [`GhostPersistentISingleton`] we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_persistent_singleton(
        tracked &mut self,
        tracked other: &GhostPersistentISingleton<T>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !final(self)@.contains(other@),
    {
        self.map.disjoint_persistent_points_to(&other.map);
    }

    /// We can split a [`GhostISubset`] based on a set of values
    pub proof fn split(tracked &mut self, s: ISet<T>) -> (tracked result: GhostISubset<T>)
        requires
            s <= old(self)@,
        ensures
            final(self).id() == old(self).id(),
            result.id() == final(self).id(),
            old(self)@ == final(self)@.union(result@),
            result@ =~= s,
            final(self)@ =~= old(self)@ - s,
    {
        let tracked map = self.map.split(s);
        GhostISubset { map }
    }

    /// We can separate a single value out of a [`GhostISubset`]
    pub proof fn split_singleton(tracked &mut self, v: T) -> (tracked result: GhostISingleton<T>)
        requires
            old(self)@.contains(v),
        ensures
            final(self).id() == old(self).id(),
            result.id() == final(self).id(),
            old(self)@ == final(self)@.insert(result@),
            result@ == v,
            final(self)@ =~= old(self)@.remove(v),
    {
        let tracked map = self.map.split_points_to(v);
        GhostISingleton { map }
    }

    /// Converting a [`GhostISubset`] into a [`GhostISingleton`]
    pub proof fn singleton(tracked self) -> (tracked r: GhostISingleton<T>)
        requires
            self.is_singleton(),
        ensures
            self@ == iset![r@],
            self.id() == r.id(),
    {
        let tracked map = self.map.points_to();
        GhostISingleton { map }
    }

    /// Converting a [`GhostISubset`] into a [`GhostPersistentISubset`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentISubset<T>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        let tracked map = self.map.persist();
        GhostPersistentISubset { map }
    }
}

impl<T> GhostPersistentISubset<T> {
    /// Checks whether the [`GhostPersistentISubset`] refers to a single key (and thus can be converted to a
    /// [`GhostPersistentIPointsTo`]).
    pub open spec fn is_singleton(self) -> bool {
        &&& self@.len() == 1
        &&& self@.finite()
        &&& !self@.is_empty()
    }

    /// Resource location
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Logically underlying [`ISet`]
    pub closed spec fn view(self) -> ISet<T> {
        self.map@.dom()
    }

    /// Instantiate a dummy [`GhostPersistentISubset`]
    pub proof fn dummy() -> (tracked result: GhostPersistentISubset<T>) {
        let tracked map = GhostPersistentISubmap::dummy();
        GhostPersistentISubset { map }
    }

    /// Create an empty [`GhostPersistentISubset`]
    pub proof fn empty(tracked &self) -> (tracked result: GhostPersistentISubset<T>)
        ensures
            result.id() == self.id(),
            result@ == ISet::<T>::empty(),
    {
        let tracked map = self.map.empty();
        GhostPersistentISubset { map }
    }

    /// Duplicate the [`GhostPersistentISubset`]
    pub proof fn duplicate(tracked &self) -> (tracked result: GhostPersistentISubset<T>)
        ensures
            result@ == self@,
            result.id() == self.id(),
    {
        let tracked map = self.map.duplicate();
        GhostPersistentISubset { map }
    }

    /// Agreement between a [`GhostPersistentISubset`] and a corresponding [`GhostIMapAuth`]
    ///
    /// Verus might not have full context of the [`GhostIMapAuth`] and a corresponding [`GhostPersistentISubset`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentISubset`] is a subset of the [`GhostIMapAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostIMapAuth<int, int>, tracked &sub: GhostPersistentISubset<int, int>)
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
    pub proof fn agree(tracked self: &GhostPersistentISubset<T>, tracked auth: &GhostISetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            self@ <= auth@,
    {
        self.map.agree(&auth.map);
    }

    /// Combining two [`GhostPersistentISubset`]s is possible.
    /// We consume the input [`GhostPersistentISubset`] and merge it into the first.
    /// We also learn that they agreed
    pub proof fn combine(tracked &mut self, tracked other: GhostPersistentISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.union(other@),
    {
        self.map.combine(other.map);
    }

    /// Combining a [`GhostPersistentISingleton`] into [`GhostPersistentISubset`] is possible, in a similar way to the way to combine
    /// [`GhostPersistentISubset`]s.
    pub proof fn combine_points_to(tracked &mut self, tracked other: GhostPersistentISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@.insert(other@),
    {
        self.map.combine_points_to(other.map);
    }

    /// When we have a [`GhostPersistentISubset`] and a [`GhostISubset`] we can prove that they have disjoint domains.
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@.disjoint(other@),
    {
        self.map.disjoint(&other.map);
    }

    /// When we have a [`GhostPersistentISubset`] and a [`GhostISingleton`], we can prove that they are in disjoint
    /// domains.
    pub proof fn disjoint_singleton(tracked &mut self, tracked other: &GhostISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !final(self)@.contains(other@),
    {
        self.map.disjoint_points_to(&other.map);
    }

    /// We can split a [`GhostPersistentISubset`] based on a set of keys in its domain.
    pub proof fn split(tracked &mut self, s: ISet<T>) -> (tracked result: GhostPersistentISubset<T>)
        requires
            s <= old(self)@,
        ensures
            final(self).id() == old(self).id(),
            result.id() == final(self).id(),
            old(self)@ == final(self)@.union(result@),
            result@ =~= s,
            final(self)@ =~= old(self)@ - s,
    {
        let tracked map = self.map.split(s);
        GhostPersistentISubset { map }
    }

    /// We can separate a single value out of a [`GhostPersistentISubset`]
    pub proof fn split_singleton(tracked &mut self, v: T) -> (tracked result:
        GhostPersistentISingleton<T>)
        requires
            old(self)@.contains(v),
        ensures
            final(self).id() == old(self).id(),
            result.id() == final(self).id(),
            old(self)@ == final(self)@.insert(result@),
            result@ == v,
            final(self)@ =~= old(self)@.remove(v),
    {
        let tracked map = self.map.split_points_to(v);
        GhostPersistentISingleton { map }
    }

    /// Convert a [`GhostPersistentISubset`] into a [`GhostPersistentISingleton`]
    pub proof fn singleton(tracked self) -> (tracked r: GhostPersistentISingleton<T>)
        requires
            self.is_singleton(),
        ensures
            self@ == iset![r@],
            self.id() == r.id(),
    {
        let tracked map = self.map.points_to();
        GhostPersistentISingleton { map }
    }
}

impl<T> GhostISingleton<T> {
    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Value owned by the singleton
    pub closed spec fn view(self) -> T {
        self.map@.0
    }

    /// Agreement between a [`GhostISingleton`] and a corresponding [`GhostISetAuth`]
    ///
    /// Verus might not have full context of the [`GhostISetAuth`] and a corresponding [`GhostISingleton`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostISingleton`] is a subset of the [`GhostISetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostISetAuth<int>, tracked &pt: GhostISingleton<int>)
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
    pub proof fn agree(tracked self: &GhostISingleton<T>, tracked auth: &GhostISetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains(self@),
    {
        self.map.agree(&auth.map);
    }

    /// We can combine two [`GhostISingleton`]s into a [`GhostISubset`]
    /// We also learn that they were disjoint.
    pub proof fn combine(tracked self, tracked other: GhostISingleton<T>) -> (tracked r:
        GhostISubset<T>)
        requires
            self.id() == other.id(),
        ensures
            r.id() == self.id(),
            r@ == iset![self@, other@],
            self@ != other@,
    {
        let tracked map = self.map.combine(other.map);
        GhostISubset { map }
    }

    /// Shows that if a two [`GhostISingleton`]s are not owning the same value
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ != other@,
    {
        self.map.disjoint(&other.map)
    }

    /// Shows that if a [`GhostISingleton`] and a [`GhostPersistentISingleton`] are not owning the same value
    pub proof fn disjoint_persistent(
        tracked &mut self,
        tracked other: &GhostPersistentISingleton<T>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ != other@,
    {
        self.map.disjoint_persistent(&other.map)
    }

    /// Shows that if a [`GhostISingleton`] and a [`GhostISubset`] are not owning the same value
    pub proof fn disjoint_subset(tracked &mut self, tracked other: &GhostISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !other@.contains(final(self)@),
    {
        self.map.disjoint_submap(&other.map);
    }

    /// Shows that if a [`GhostISingleton`] and a [`GhostPersistentISubset`] are not owning the same value
    pub proof fn disjoint_persistent_subset(
        tracked &mut self,
        tracked other: &GhostPersistentISubset<T>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !other@.contains(final(self)@),
    {
        self.map.disjoint_persistent_submap(&other.map);
    }

    /// Convert the [`GhostISingleton`] a [`GhostISubset`]
    pub proof fn subset(tracked self) -> (tracked r: GhostISubset<T>)
        ensures
            r.id() == self.id(),
            r@ == iset![self@],
    {
        let tracked map = self.map.submap();
        GhostISubset { map }
    }

    /// Converting a [`GhostISingleton`] into a [`GhostPersistentISingleton`]
    pub proof fn persist(tracked self) -> (tracked r: GhostPersistentISingleton<T>)
        ensures
            self@ == r@,
            self.id() == r.id(),
    {
        let tracked map = self.map.persist();
        GhostPersistentISingleton { map }
    }
}

impl<T> GhostPersistentISingleton<T> {
    /// Location of the underlying resource
    pub closed spec fn id(self) -> Loc {
        self.map.id()
    }

    /// Value known by the singleton
    pub closed spec fn view(self) -> T {
        self.map@.0
    }

    /// Duplicate the [`GhostPersistentISingleton`]
    pub proof fn duplicate(tracked &self) -> (tracked result: GhostPersistentISingleton<T>)
        ensures
            result@ == self@,
            result.id() == self.id(),
    {
        let tracked map = self.map.duplicate();
        GhostPersistentISingleton { map }
    }

    /// Agreement between a [`GhostPersistentISingleton`] and a corresponding [`GhostISetAuth`]
    ///
    /// Verus might not have full context of the [`GhostISetAuth`] and a corresponding [`GhostPersistentISingleton`].
    /// However, whenever we know that they refer to the same resource (i.e., have matching ids) we
    /// can assert that the [`GhostPersistentISingleton`] is a subset of the [`GhostISetAuth`].
    /// ```
    /// proof fn test(tracked &auth: GhostISetAuth<int>, tracked &pt: GhostPersistentISingleton<int>)
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
    pub proof fn agree(tracked self: &GhostPersistentISingleton<T>, tracked auth: &GhostISetAuth<T>)
        requires
            self.id() == auth.id(),
        ensures
            auth@.contains(self@),
    {
        self.map.agree(&auth.map);
    }

    /// We can combine two [`GhostPersistentISingleton`]s into a [`GhostPersistentISubset`]
    pub proof fn combine(tracked self, tracked other: GhostPersistentISingleton<T>) -> (tracked r:
        GhostPersistentISubset<T>)
        requires
            self.id() == other.id(),
        ensures
            r.id() == self.id(),
            r@ == iset![self@, other@],
            self@ != other@ ==> r@.len() == 2,
            self@ == other@ ==> r@.len() == 1,
    {
        let tracked map = self.map.combine(other.map);
        GhostPersistentISubset { map }
    }

    /// Shows that a [`GhostPersistentISingleton`] and a [`GhostISingleton`] are not owning the same value
    pub proof fn disjoint(tracked &mut self, tracked other: &GhostISingleton<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ != other@,
    {
        self.map.disjoint(&other.map)
    }

    /// Shows that if a [`GhostPersistentISingleton`] and a [`GhostISubset`] are not owning the same value
    pub proof fn disjoint_subset(tracked &mut self, tracked other: &GhostISubset<T>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            !other@.contains(final(self)@),
    {
        self.map.disjoint_submap(&other.map);
    }

    /// Convert the [`GhostPersistentISingleton`] a [`GhostPersistentISubset`]
    pub proof fn subset(tracked self) -> (tracked r: GhostPersistentISubset<T>)
        ensures
            r.id() == self.id(),
            r@ == iset![self@],
    {
        let tracked map = self.map.submap();
        GhostPersistentISubset { map }
    }
}

} // verus!
