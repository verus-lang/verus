use super::super::map::*;
use super::super::map_lib::*;
use super::super::modes::*;
use super::super::pcm::*;
use super::super::prelude::*;

// This implements a resource for ownership of subsets of keys in a map.

verus! {

broadcast use super::super::group_vstd_default;

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
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

#[verifier::reject_recursive_types(K)]
pub struct GhostMapAuth<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

#[verifier::reject_recursive_types(K)]
pub struct GhostSubmap<K, V> {
    r: Resource<MapCarrier<K, V>>,
}

/** An implementation of a resource for owning a subset of keys in a map.

`GhostMapAuth<K, T>` represents authoritative ownership of the entire
map, and `GhostSubmap<K, T>` represents client ownership of some subset
of keys in the map.  Updating the authoritative `GhostMapAuth<K, T>`
requires a `GhostSubmap<K, T>` containing the keys being updated.
`GhostSubmap<K, T>`s can be combined or split.

### Example

```
fn example_use() {
    let tracked (mut auth, mut sub) = GhostMapAuth::new(map![1u8 => 1u64, 2u8 => 2u64, 3u8 => 3u64]);

    // Allocate some more keys in the auth map, receiving a new submap.
    let tracked sub2 = auth.insert(map![4u8 => 4u64, 5u8 => 5u64]);
    proof { sub.combine(sub2); }

    // Delete some keys in the auth map, by returning corresponding submap.
    let tracked sub3 = sub.split(set![3u8, 4u8]);
    proof { auth.delete(sub3); }

    // Split the submap into a multiple submaps.
    let tracked sub4 = sub.split(set![1u8, 5u8]);

    // In general, we might need to call agree() to establish the fact that
    // a submap has the same values as the auth map.  Here, Verus doesn't need
    // agree because it can track where both the auth and submap came from.
    proof { sub.agree(&auth); }
    proof { sub4.agree(&auth); }

    assert(sub4[1u8] == auth[1u8]);
    assert(sub4[5u8] == auth[5u8]);
    assert(sub[2u8] == auth[2u8]);

    // Update keys using ownership of submaps.
    proof { sub.update(&mut auth, map![2u8 => 22u64]); }
    proof { sub4.update(&mut auth, map![1u8 => 11u64]); }
    assert(auth[1u8] == 11u64);
    assert(auth[2u8] == 22u64);

    // Not shown in this simple example is the main use case of this resource:
    // maintaining an invariant between GhostMapAuth<K, V> and some exec-mode
    // shared state with a map view (e.g., HashMap<K, V>), which states that
    // the Map<K, V> view of GhostMapAuth<K, V> is the same as the view of the
    // HashMap<K, V>, and then handing out a GhostSubmap<K, V> to different
    // clients that might need to operate on different keys in this map.
}
```
*/

impl<K, V> GhostMapAuth<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is Some
        &&& self.r.value().auth.unwrap() is Some
        &&& self.r.value().frac == Some(Map::<K, V>::empty())
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().auth.unwrap().unwrap()
    }

    pub open spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    pub proof fn dummy() -> (tracked result: GhostMapAuth<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        auth
    }

    pub proof fn take(tracked &mut self) -> (tracked result: GhostMapAuth<K, V>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);
        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

    pub proof fn empty(tracked &self) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == self.id(),
            result@ == Map::<K, V>::empty(),
    {
        use_type_invariant(self);
        GhostSubmap::<K, V>::empty(self.id())
    }

    pub proof fn insert(tracked &mut self, m: Map<K, V>) -> (tracked result: GhostSubmap<K, V>)
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

impl<K, V> GhostSubmap<K, V> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value().auth is None
        &&& self.r.value().frac is Some
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> Map<K, V> {
        self.r.value().frac.unwrap()
    }

    pub open spec fn dom(self) -> Set<K> {
        self@.dom()
    }

    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self@[key]
    }

    pub proof fn dummy() -> (tracked result: GhostSubmap<K, V>) {
        let tracked (auth, submap) = GhostMapAuth::<K, V>::new(Map::empty());
        submap
    }

    pub proof fn empty(id: int) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result.id() == id,
            result@ == Map::<K, V>::empty(),
    {
        let tracked r = Resource::create_unit(id);
        GhostSubmap { r }
    }

    pub proof fn take(tracked &mut self) -> (tracked result: GhostSubmap<K, V>)
        ensures
            result == *old(self),
    {
        use_type_invariant(&*self);

        let tracked mut r = Self::dummy();
        tracked_swap(self, &mut r);
        r
    }

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
}

} // verus!
