#![allow(dead_code)]
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::{assert_by_contradiction, seq_lib::*, set_lib::*};

verus! {

pub trait VerusClone : Sized {
    fn clone(&self) -> (o: Self)
        ensures o == self;
}

// Based on Rust's Ordering
#[derive(Structural, PartialEq, Eq)]
pub enum Ordering {
    Less,
    Equal,
    Greater,
}

impl Ordering {
    pub open spec fn eq(self) -> bool {
        matches!(self, Ordering::Equal)
    }

    pub open spec fn ne(self) -> bool {
        !matches!(self, Ordering::Equal)
    }

    pub open spec fn lt(self) -> bool {
        matches!(self, Ordering::Less)
    }

    pub open spec fn gt(self) -> bool {
        matches!(self, Ordering::Greater)
    }

    pub open spec fn le(self) -> bool {
        !matches!(self, Ordering::Greater)
    }

    pub open spec fn ge(self) -> bool {
        !matches!(self, Ordering::Less)
    }

    pub fn is_eq(self) -> (b:bool) 
        ensures b == self.eq(),
    {
        matches!(self, Ordering::Equal)
    }

    pub fn is_ne(self) -> (b:bool) 
        ensures b == self.ne(),
    {
        !matches!(self, Ordering::Equal)
    }

    pub const fn is_lt(self) -> (b:bool) 
        ensures b == self.lt(),
    {
        matches!(self, Ordering::Less)
    }

    pub const fn is_gt(self) -> (b:bool) 
        ensures b == self.gt(),
    {
        matches!(self, Ordering::Greater)
    }

    pub const fn is_le(self) -> (b:bool) 
        ensures b == self.le(),
    {
        !matches!(self, Ordering::Greater)
    }

    pub const fn is_ge(self) -> (b:bool) 
        ensures b == self.ge(),
    {
        !matches!(self, Ordering::Less)
    }
}

pub trait Key : Sized {

    spec fn zero_spec() -> Self where Self: std::marker::Sized;

    proof fn zero_properties()
        ensures
            forall |k:Self| ({
                &&& k != Self::zero_spec() ==> (#[trigger] Self::zero_spec().cmp_spec(k)).lt()
                &&& (Self::zero_spec().cmp_spec(k)).le()
            });

    spec fn cmp_spec(self, other: Self) -> Ordering;

    proof fn cmp_properties()
        ensures 
        // Equality is eq  --- TODO: Without this we need to redefine Seq, Set, etc. operators that use ==
        forall |a:Self, b:Self| #![auto] a == b <==> a.cmp_spec(b).eq(),
        // Reflexivity of equality
        forall |a:Self| #![auto] a.cmp_spec(a).eq(),
        // Commutativity of equality
        forall |a:Self, b:Self| (#[trigger] a.cmp_spec(b)).eq() == b.cmp_spec(a).eq(),
        // Transitivity of equality
        forall |a:Self, b:Self, c:Self| 
            #[trigger] a.cmp_spec(b).eq() && #[trigger] b.cmp_spec(c).eq() ==> a.cmp_spec(c).eq(),
        // Inequality is asymmetric
        forall |a:Self, b:Self| 
            #[trigger] a.cmp_spec(b).lt() <==> b.cmp_spec(a).gt(),
        // Connected
        forall |a:Self, b:Self| 
            #![auto] a.cmp_spec(b).ne() ==> a.cmp_spec(b).lt() || b.cmp_spec(a).lt(),
        // Transitivity of inequality
        forall |a:Self, b:Self, c:Self| 
            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt(),
        forall |a:Self, b:Self, c:Self| 
            #[trigger] a.cmp_spec(b).lt() && #[trigger] b.cmp_spec(c).le() ==> a.cmp_spec(c).lt(),
        forall |a:Self, b:Self, c:Self| 
            #[trigger] a.cmp_spec(b).le() && #[trigger] b.cmp_spec(c).lt() ==> a.cmp_spec(c).lt();

    // zero should be smaller than all other keys
    fn zero() -> (z: Self)
        ensures z == Self::zero_spec();

    fn cmp(&self, other: &Self) -> (o: Ordering)
        requires true,
        ensures o == self.cmp_spec(*other);
}


// Stores the entries from smallest to largest
struct StrictlyOrderedVec<K: Key + VerusClone> {
    v: Vec<K>,
}


spec fn sorted<K: Key>(s: Seq<K>) -> bool
{
    forall |i, j| #![auto] 0 <= i < j < s.len() ==> s[i].cmp_spec(s[j]).lt()
}
/*
proof fn sorted_subrange<K: Key>(s: Seq<K>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        sorted(s),
    ensures
        sorted(s.subrange(i, j)),
{
    let sub = s.subrange(i, j);
    assert forall |m, n| 0 <= m < n < sub.len() implies #[trigger](sub[m].cmp_spec(sub[n]).lt()) by {
        K::cmp_properties();
    }
}
*/

impl<K: Key + VerusClone> StrictlyOrderedVec<K> {
    pub closed spec fn view(self) -> Seq<K> {
        self.v@
    }

    pub closed spec fn valid(self) -> bool {
        sorted(self@) && self@.no_duplicates()
    }

    proof fn to_set(self) -> (s: Set<K>)
        requires self.valid(),
        ensures s == self@.to_set(),
                s.finite(),
                s.len() == self@.len(),
    {
        seq_to_set_is_finite::<K>(self@);
        self@.unique_seq_to_set();
        self@.to_set()
    }

    fn new() -> (v: Self)
        ensures v@ == Seq::<K>::empty(),
                v.valid(),
    {
        StrictlyOrderedVec { v: Vec::new() }
    }

    fn len(&self) -> (len: usize )
        ensures len == self@.len()
    {
        self.v.len()
    }

    fn index(&self, i: usize) -> (k: K)
        requires i < self@.len(),
        ensures k == self@[i as int]
    {
        (self.v[i]).clone()
    }

    fn set(&mut self, i: usize, k: K) 
        requires old(self).valid(),
                 i < old(self)@.len(),
                 i > 0 ==> old(self)@[i as int - 1].cmp_spec(k).lt(),
                 i < old(self)@.len() - 1 ==> k.cmp_spec(old(self)@[i as int + 1]).lt(),
        ensures 
            self.valid(),
            self@ == old(self)@.update(i as int, k),
    {
        self.v.set(i, k);
        assert forall |m, n| 0 <= m < n < self@.len() implies #[trigger](self@[m].cmp_spec(self@[n]).lt()) by {
            K::cmp_properties();
        }

        assert forall |i, j| 0 <= i < self@.len() && 0 <= j < self@.len() && i != j implies self@[i] != self@[j] by {
            K::cmp_properties();
        }

    }

    fn remove(&mut self, i: usize) -> (k: K)
        requires 
            old(self).valid(),
            i < old(self)@.len(),
        ensures 
            self.valid(),
            k == old(self)@.index(i as int),
            self@ == old(self)@.remove(i as int),
            self@.to_set() == old(self)@.to_set().remove(k),
    {
        let k = self.v.remove(i);
        proof {
            let old_s = old(self)@.to_set().remove(k);
            let new_s = self@.to_set();
            assert forall |e| old_s.contains(e) implies new_s.contains(e) by {
                assert(old(self)@.to_set().contains(e));
                let n = choose |n: int| 0 <= n < old(self)@.len() && old(self)@[n] == e;
                if n < i {
                    assert(self@[n] == e);  // OBSERVE
                } else {
                    assert(self@[n-1] == e);  // OBSERVE
                }
            }
            assert_sets_equal!(self@.to_set(), old(self)@.to_set().remove(k));
        }
        k
    }

    /// Remove entries in the range [start, end)
    fn erase(&mut self, start: usize, end: usize) 
        requires
            old(self).valid(),
            start <= end <= old(self)@.len(),
        ensures
            self.valid(),
            self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(end as int, old(self)@.len() as int),
            // TODO: We might want to strengthen this further to say that the two sets on the RHS
            //       are disjoint
            old(self)@.to_set() == self@.to_set() + old(self)@.subrange(start as int, end as int).to_set(),
    {
        let mut deleted = 0;
        let ghost mut deleted_set;
        proof {
            deleted_set = Set::empty();
            assert_seqs_equal!(self@, 
                               old(self)@.subrange(0, start as int) + 
                               old(self)@.subrange(start as int + deleted as int, 
                                                   old(self)@.len() as int));
            assert_sets_equal!(deleted_set,
                               old(self)@.subrange(start as int, 
                                                   start as int + deleted as int).to_set()); 
            assert_sets_equal!(old(self)@.to_set(),
                               self@.to_set() + deleted_set);
        }
        while deleted < end - start
            invariant
                start <= end <= old(self)@.len(),
                self@.len() == old(self)@.len() - deleted,
                0 <= deleted <= end - start,
                old(self).valid(),
                self.valid(),
                self@ == old(self)@.subrange(0, start as int) + old(self)@.subrange(start as int + deleted as int, old(self)@.len() as int),
                deleted_set == old(self)@.subrange(start as int, start as int + deleted as int).to_set(), 
                deleted_set.len() == deleted,
                old(self)@.to_set() == self@.to_set() + deleted_set,
        {
            let ghost mut old_deleted_set;
            let ghost mut old_deleted_seq;
            let ghost mut target;
            proof {
                old_deleted_set = deleted_set;
                old_deleted_seq = old(self)@.subrange(start as int, start as int + deleted as int);
                target = self@[start as int];
                deleted_set = deleted_set.insert(self@[start as int]);
            }
            self.remove(start);
            deleted = deleted + 1;
            proof {
                assert_seqs_equal!(self@, 
                                   old(self)@.subrange(0, start as int) + 
                                   old(self)@.subrange(start as int + deleted as int, 
                                                       old(self)@.len() as int));
                let deleted_seq = old(self)@.subrange(start as int, 
                                                      start as int + deleted as int);
                seq_to_set_is_finite::<K>(deleted_seq);
                deleted_seq.unique_seq_to_set();

                assert forall |e| #[trigger] deleted_set.contains(e) 
                                  implies deleted_seq.to_set().contains(e) by {
                    if e == target {
                        assert(deleted_seq[deleted as int - 1] == e); // OBSERVE
                    } else {
                        assert(old_deleted_set.contains(e));
                        assert(old_deleted_seq.contains(e));
                        let i = choose |i| 0 <= i < old_deleted_seq.len() && old_deleted_seq[i] == e;
                        assert(deleted_seq[i] == e); // OBSERVE
                    }
                }
                assert forall |e| #[trigger] deleted_seq.to_set().contains(e)
                                  implies deleted_set.contains(e)  by {
                    if e == target {
                    } else {
                        let i = choose |i| 0 <= i < deleted_seq.len() && deleted_seq[i] == e;
                        assert(old_deleted_seq[i] == e);    // OBSERVE
                    }
                }
                assert_sets_equal!(deleted_set,
                                   deleted_seq.to_set()); 
                assert_sets_equal!(old(self)@.to_set(),
                                   self@.to_set() + deleted_set);
            }
        }

    }

    fn insert(&mut self, k: K) -> (i: usize)
        requires 
            old(self).valid(),
            !old(self)@.contains(k),
        ensures self.valid(),
            self@.len() == old(self)@.len() + 1,
            0 <= i < self@.len(),
            self@ == old(self)@.insert(i as int, k),
            self@.to_set() == old(self)@.to_set().insert(k),
    {
        // Find the index where we should insert k
        let mut index: usize = 0;
        while index < self.v.len() && self.v[index].cmp(&k).is_lt() 
            invariant 
                0 <= index <= self@.len(),
                forall |i| 0 <= i < index ==> (#[trigger] self@.index(i).cmp_spec(k)).lt()
        {
            index = index + 1;
        }
        self.v.insert(index, k);
        assert forall |m, n| 0 <= m < n < self@.len() implies #[trigger](self@[m].cmp_spec(self@[n]).lt()) by {
            K::cmp_properties();
        }
        assert(self@.to_set() == old(self)@.to_set().insert(k)) by {
            let new_s = self@.to_set();
            let old_s = old(self)@.to_set().insert(k);
            assert(self@[index as int] == k);   // OBSERVE
            assert forall |e| old_s.contains(e) implies new_s.contains(e) by {
                if e == k {
                } else {
                    let i = choose |i: int| 0 <= i < old(self)@.len() && old(self)@[i] == e; 
                    if i < index {
                        assert(self@[i] == e);      // OBSERVE
                    } else {
                        assert(self@[i+1] == e);    // OBSERVE
                    }
                }
            };
            assert_sets_equal!(new_s, old_s);
        };
        return index;
    }
}


pub struct KeyIterator<K: Key + VerusClone> {
    // None means we hit the end
    pub k: Option<K>,
}

impl<K: Key + VerusClone> KeyIterator<K> {
    pub open spec fn new_spec(k: K) -> Self {
        KeyIterator { k: Some(k) }
    }

    #[verifier(when_used_as_spec(new_spec))]
    pub fn new(k: K) -> (s: Self)
        ensures s.k == Some(k)
    {
        KeyIterator { k: Some(k) }
    }

    pub open spec fn end_spec() -> (s: Self) {
        KeyIterator { k: None }
    }

    #[verifier(when_used_as_spec(end_spec))]
    pub fn end() -> (s: Self)
        ensures s.k.is_None()
    {
        KeyIterator { k: None }
    }

    pub open spec fn is_end_spec(&self) -> bool {
        self.k.is_None()
    }

    #[verifier(when_used_as_spec(is_end_spec))]
    pub fn is_end(&self) -> (b: bool)
        ensures b == self.is_end_spec()
    {
        matches!(self.k, None)
    }

    pub open spec fn get_spec(&self) -> &K 
        recommends self.k.is_Some(),
    {
        &self.k.get_Some_0()
    }

    #[verifier(when_used_as_spec(get_spec))]
    pub fn get(&self) -> (k: &K)
        requires !self.is_end(),
        ensures k == self.get_spec(),
    {
        self.k.as_ref().unwrap()
    }
    
    pub open spec fn lt_spec(&self, other: &Self) -> bool {
        (!self.k.is_None() && other.k.is_None())
      || (!self.k.is_None() && !other.k.is_None() && self.k.get_Some_0().cmp_spec(other.k.get_Some_0()).lt())
    }

    #[verifier(when_used_as_spec(lt_spec))]
    fn lt(&self, other: &Self) -> (b: bool)
        ensures b == self.lt_spec(other),
    {
        (!self.is_end() && other.is_end())
            || (!self.is_end() && !other.is_end() && self.k.as_ref().unwrap().cmp(&other.k.as_ref().unwrap()).is_lt())
    }

    spec fn geq_spec(self, other: Self) -> bool {
        !self.lt_spec(&other) //|| self == other
    }

    spec fn geq_K(self, other: K) -> bool {
        !self.lt_spec(&KeyIterator::new_spec(other)) 
    }

    // Ivy calls this `done`
    spec fn above_spec(&self, k: K) -> bool {
        self.k.is_None() || k.cmp_spec(self.k.get_Some_0()).lt()
    }

    // Is this iterator strictly above the supplied value?
    #[verifier(when_used_as_spec(above_spec))]
    fn above(&self, k: K) -> (b: bool)
        ensures b == self.above_spec(k),
    {
        self.is_end() || k.cmp(&self.k.as_ref().unwrap()).is_lt()
    }
    

    // Is k in the range [lhs, rhs)
    pub open spec fn between(lhs: Self, ki: Self, rhs: Self) -> bool {
        !ki.lt_spec(&lhs) && ki.lt_spec(&rhs)
    }
}

pub fn vec_erase<A>(v: &mut Vec<A>, start: usize, end: usize) 
    requires
        start <= end <= old(v).len(),
    ensures
        true,
        v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(end as int, old(v)@.len() as int),
{
    let mut deleted = 0;
    proof {
        assert_seqs_equal!(v@, 
                           old(v)@.subrange(0, start as int) + 
                           old(v)@.subrange(start as int + deleted as int, 
                                               old(v)@.len() as int));
    }
    while deleted < end - start
        invariant
            start <= end <= old(v)@.len(),
            v@.len() == old(v)@.len() - deleted,
            0 <= deleted <= end - start,
            v@ == old(v)@.subrange(0, start as int) + old(v)@.subrange(start as int + deleted as int, old(v)@.len() as int),
    {
        v.remove(start);
        deleted = deleted + 1;
        proof {
            assert_seqs_equal!(v@, 
                               old(v)@.subrange(0, start as int) + 
                               old(v)@.subrange(start as int + deleted as int, 
                                                   old(v)@.len() as int));
        }
    }
}

struct StrictlyOrderedMap<#[verifier(maybe_negative)] K: Key + VerusClone, V> {
    keys: StrictlyOrderedVec<K>,
    vals: Vec<V>,
    m: Ghost<Map<K, V>>,
}

impl<K: Key + VerusClone, V: VerusClone> StrictlyOrderedMap<K, V> {
    pub closed spec fn view(self) -> Map<K,V> {
        self.m@
    }

    pub closed spec fn map_valid(self) -> bool 
        // recommends self.keys@.len() == self.vals.len()  // error: public function requires cannot refer to private items
    {
        // TODO(pranav) necessary with epr?
        &&& self.m@.dom().finite()
        &&& self.m@.dom() == self.keys@.to_set()
        &&& forall |i| 0 <= i < self.keys@.len() ==> #[trigger] (self.m@[self.keys@.index(i)]) == self.vals@.index(i)
    }

    pub closed spec fn valid(self) -> bool {
        // TODO(pranav) necessary with epr?
        &&& self.keys.valid() 
        &&& self.keys@.len() == self.vals.len()
        &&& self.map_valid()
    }

    /// We hold no keys in the range (lo, hi)
    spec fn gap(self, lo: KeyIterator<K>, hi: KeyIterator<K>) -> bool {
        forall |ki| lo.lt_spec(&ki) && ki.lt_spec(&hi) ==> !(#[trigger] self@.contains_key(*ki.get()))
    }

    // TODO(pranav) necessary with epr?
    proof fn mind_the_gap(self) 
        ensures 
            forall|w, x, y, z| self.gap(w, x) && self.gap(y, z) && #[trigger] y.lt_spec(&x) ==> #[trigger] self.gap(w, z),
            forall|w, x, y: KeyIterator<K>, z| #[trigger] self.gap(w, x) && y.geq_spec(w) && x.geq_spec(z) ==> #[trigger] self.gap(y, z),
            forall|l:KeyIterator<K>, k, m| #[trigger] self.gap(k, m) ==> !(k.lt_spec(&l) && l.lt_spec(&m) && #[trigger] self@.contains_key(*l.get()))
    {
        K::cmp_properties();
    }

    // TODO(pranav) necessary with epr?
    proof fn gap_means_empty(self, lo:KeyIterator<K>, hi:KeyIterator<K>, k:KeyIterator<K>) 
        requires 
            self.gap(lo, hi),
            lo.lt_spec(&k) && k.lt_spec(&hi),
            self@.contains_key(*k.get()),
        ensures
            false,
    {
        self.mind_the_gap();
    }

    // TODO(pranav) necessary with epr?
    proof fn choose_gap_violator(self, lo:KeyIterator<K>, hi:KeyIterator<K>) -> (r: KeyIterator<K>)
        requires
            !self.gap(lo, hi),
        ensures
            lo.lt_spec(&r) && r.lt_spec(&hi) && self@.contains_key(*r.get()),
    {
        choose |r| #![auto] lo.lt_spec(&r) && r.lt_spec(&hi) && self@.contains_key(*r.get_spec())
    }


    fn new() -> (s: Self)
        ensures 
            s.valid(),
            s@ == Map::<K,V>::empty(),
    {
        let keys = StrictlyOrderedVec::new();
        let m = Ghost(Map::empty());
        // TODO(pranav) prove with a lemma with an epr proof?
        proof {
            assert_sets_equal!(m@.dom(), keys@.to_set());
        }
        StrictlyOrderedMap {
            keys,
            vals: Vec::new(),
            m,
        }
    }

    fn find_key(&self, k: &K) -> (o: Option<usize>)
        requires self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(i) => 0 <= i < self.keys@.len() && self.keys@[i as int] == k,
            },
    {
        let mut i = 0;
        while i < self.keys.len()
            invariant forall |j| 0 <= j < i ==> self.keys@[j] != k,
        {
            //println!("Loop {} of find_key", i);
            if self.keys.index(i).cmp(k).is_eq() {
                proof {
                    K::cmp_properties();
                }
                return Some(i);
            } else {
                proof {
                    K::cmp_properties();
                } 
            }
            i = i + 1;
        }
        return None;
    }

    fn get(&self, k: &K) -> (o: Option<&V>)
        requires
            self.valid(),
        ensures
            match o {
                None => !self@.contains_key(*k),
                Some(v) => self@[*k] == v,
            }
    {
        match self.find_key(k) {
            None => None,
            Some(i) => Some(&self.vals[i]),
        }
    }

    fn set(&mut self, k: K, v: V) 
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@.insert(k, v),
            forall |lo, hi| self.gap(lo, hi) <==>
                            old(self).gap(lo, hi) 
                        && !(lo.lt_spec(&KeyIterator::new_spec(k))
                          && KeyIterator::new_spec(k).lt_spec(&hi)),
    {
        match self.find_key(&k) {
            Some(i) => {
                self.vals.set(i, v);
                self.m = Ghost(self.m@.insert(k, v));
                proof {
                    assert_sets_equal!(self.m@.dom() == self.keys@.to_set());
                }
            },
            None => {
                let index = self.keys.insert(k.clone());
                self.vals.insert(index, v);
                self.m = Ghost(self.m@.insert(k, v));
            }
        }

        assume(false); // TODO(pranav) prove with a lemma with an epr proof
    }

    // TODO(pranav) remove?
    spec fn greatest_lower_bound_spec(self, iter: KeyIterator<K>, glb: KeyIterator<K>) -> bool {
        (glb == iter || glb.lt_spec(&iter)) &&
        (forall |k| KeyIterator::new_spec(k) != glb && #[trigger] self@.contains_key(k) && iter.above(k) ==> glb.above(k)) &&
        (!iter.is_end_spec() ==> 
            glb.k.is_Some() && 
            self@.contains_key(glb.k.get_Some_0()) &&
            // There are no keys in the interval (glb, hi), and iter falls into that gap
            (exists |hi| #[trigger] self.gap(glb, hi) && #[trigger] KeyIterator::between(glb, iter, hi)))
    }

    // Finds the largest iterator <= iter
    fn greatest_lower_bound(&self, iter: &KeyIterator<K>) -> (glb: KeyIterator<K>)
        requires
            self.valid(),
            self@.contains_key(K::zero_spec()),
        ensures
            self.greatest_lower_bound_spec(*iter, glb),
    {
        let mut bound = 0;
        let mut i = 1;

        assume(false); // TODO(pranav) prove with a lemma with an epr proof

        // Find the glb's index (bound)
        while i < self.keys.len()
            invariant
                1 <= i <= self.keys@.len(),
                bound == i - 1,
                forall |j:nat| j < i ==> iter.geq_K(#[trigger]self.keys@.index(j as int)),
            ensures
                bound == i - 1,
                (i == self.keys@.len() && 
                 forall |j:nat| j < i ==> iter.geq_K(#[trigger]self.keys@.index(j as int)))
             || (i < self.keys@.len() && 
                 !iter.geq_K(self.keys@.index(i as int)) &&
                 forall |j:nat| j < i ==> iter.geq_K(#[trigger]self.keys@.index(j as int))),
        {
            if iter.lt(&KeyIterator::new(self.keys.index(i))) {
                // Reached a key that's too large
                break;
            }
            bound = i;
            i = i + 1;
        }

        assume(false); // TODO(pranav) prove with a lemma with an epr proof
        
        let glb = KeyIterator::new(self.keys.index(bound));
        return glb;
    }
    
    // Remove all keys in the range [lo, hi)
    fn erase(&mut self, lo: &KeyIterator<K>, hi: &KeyIterator<K>) 
        requires
            old(self).valid(),
        ensures
            self.valid(),
            forall |k| {
                let ki = KeyIterator::new_spec(k);
                (if ki.geq_spec(*lo) && ki.lt(hi) {
                    !(#[trigger] self@.contains_key(k))
                } else {
                    (old(self)@.contains_key(k) ==>
                         self@.contains_key(k) && self@[k] == old(self)@[k])
                    && (self@.contains_key(k) ==> old(self)@.contains_key(k))
                })},
            forall |x, y| self.gap(x, y) <==> ({
                         ||| old(self).gap(x, y)
                         ||| (old(self).gap(x, *lo) && 
                              old(self).gap(*hi, y) &&
                              (hi.geq_spec(y) || hi.is_end_spec() || !self@.contains_key(*hi.get())))
                        }),
    {
        // Find the point where keys are >= lo
        let mut start = 0;
        while start < self.keys.len() && lo.above(self.keys.index(start)) 
            invariant
                // TODO(pranav) epr ???
                self.valid(),
                0 <= start <= self.keys@.len(),
                forall |j| #![auto] 0 <= j < start ==> lo.above(self.keys@.index(j)) 
        {
            start = start + 1;
        }

        // Find the first point where keys are >= hi
        let mut end = start;
        while end < self.keys.len() && hi.above(self.keys.index(end)) 
            invariant
                // TODO(pranav) epr ???
                self.valid(),
                start <= end <= self.keys@.len(),
                forall |j| #![auto] start <= j < end ==> hi.above(self.keys@[j]) 
        {
            end = end + 1;
        }

        self.keys.erase(start, end);
        vec_erase(&mut self.vals, start, end);
        self.m = Ghost(Map::new(|k| self.keys@.to_set().contains(k),
                                |k| { let i = choose |i| 0 <= i < self.keys@.len() && self.keys@[i] == k;
                                      self.vals@[i]}));
        assume(false); // TODO(pranav) prove with a lemma with an epr proof
    }
}

struct DelegationMap<#[verifier(maybe_negative)] K: Key + VerusClone, ID> {
    // Our efficient implementation based on ranges
    lows: StrictlyOrderedMap<K, ID>,
    // Our spec version
    m: Ghost<Map<K, ID>>,

}

mod EPRModel {
    use crate::Key;
    use crate::VerusClone;
    use crate::DelegationMap;
    use crate::KeyIterator;
    use vstd::prelude::Map;
    use crate::StrictlyOrderedMap;

    /* Key type Abstraction */
    pub closed spec fn key_zero<K: Key>() -> K {
        K::zero_spec()
    }

    pub closed spec fn key_le<K : Key>(k1: K, k2: K) -> bool {
        k1.cmp_spec(k2).le()
    }
    pub proof fn key_le_properties<K : Key>()
        ensures
            forall | x : K | key_le(key_zero(), x),
            forall | x : K | key_le(x, x),
            forall | x : K, y : K, z : K | 
                #![no_triggers]
                key_le(x, y) && key_le(y, z) ==> key_le(x, z),
            forall | x : K, y : K | 
                #![no_triggers]
                key_le(x, y) && key_le(y, x) ==> x == y,
            forall | x : K, y : K |
                #![no_triggers]
                key_le(x, y) || key_le(y, x),
    {
        K::zero_properties();
        K::cmp_properties();
    }

    /* SOMap Abstraction */
    pub struct SOMapModel<#[verifier(maybe_negative)] K: Key + VerusClone, V>(StrictlyOrderedMap<K, V>);

    impl<K: Key + VerusClone, ID : VerusClone> SOMapModel<K, ID> {
        /**************************************
            primitives of the interface
        **************************************/
        pub closed spec fn m(&self, k : K, id : ID) -> bool {
            &&& self.0.m@.dom().contains(k) 
            &&& self.0.m@[k] == id
        }
        
        pub proof fn map_properties(&self)
            ensures 
                forall|k, id_1, id_2| #![all_triggers] self.m(k, id_1) && self.m(k, id_2) ==> id_1 == id_2,
        {}

        pub closed spec fn gap(&self, lo: K, hi: K) -> bool {
            self.0.gap(KeyIterator::new_spec(lo), KeyIterator::new_spec(hi))
        }
        
        // mind_the_gap translation
        pub proof fn gap_properties(&self)
            ensures
                forall|w, x, y, z| 
                    #![no_triggers]
                    self.gap(w, x) && self.gap(y, z) && !key_le(x, y) ==> self.gap(w, z),
                forall|x, y, z| 
                    #![no_triggers]
                    self.gap(x, y) && self.gap(y, z) && !self.gap(x, z) ==> self.contains(y),
                forall|w, x, y, z| 
                    #![no_triggers]
                    self.gap(w, x) && key_le(w, y) && key_le(z, x) ==> self.gap(y, z),
                forall|l, k, m, id| 
                    #![no_triggers]     // k < l < m                      l has an entry
                    self.gap(k, m) ==> !(!key_le(l, k) && !key_le(m, l) && self.m(l, id))
        {
            K::cmp_properties();
            assert forall|l, k, m, id| self.gap(k, m) implies !(!key_le(l, k) && !key_le(m, l) && self.m(l, id)) by {
                if !key_le(l, k) && !key_le(m, l) && self.m(l, id) {
                    self.0.gap_means_empty(KeyIterator::new_spec(k), KeyIterator::new_spec(m), KeyIterator::new_spec(l));
                }
            }
            assert forall|x, y, z| self.gap(x, y) && self.gap(y, z) && !self.gap(x, z) implies self.contains(y) by {
                if !self.contains(y) {
                    assert(!self.0.m@.contains_key(y)) by {
                        if self.0.m@.contains_key(y) {
                            let v = self.0.m@[y];
                            assert(self.m(y, v));
                        }
                    }
                }

            }
        }

        /**************************************
            transitions built on interface
        **************************************/

        #[verifier::inline_only]
        pub open spec fn erase(&self, new: Self, lo: K, hi: K) -> bool {
            &&& (forall|k,id| #![no_triggers] new.m(k, id) == (self.m(k, id) && !(key_le(lo, k) && !key_le(hi, k))))
            &&& (forall|x,y| #![no_triggers] new.gap(x,y) == (self.gap(x,y) || (self.gap(x,lo) && self.gap(hi,y) && (key_le(y, hi) || !self.contains(hi)))))
        }

        #[verifier::inline_only]
        pub open spec fn erase_unbounded(&self, new: Self, lo: K) -> bool {
            &&& (forall|k,id| #![no_triggers] new.m(k, id) == (self.m(k, id) && !(key_le(lo, k))))
            &&& (forall|x,y| #![no_triggers] new.gap(x,y) == (self.gap(x,y) || (self.gap(x,lo))))
        }

        #[verifier::inline_only]
        pub open spec fn set(&self, new: Self, key: K, val : ID)  -> bool {
            &&& (forall|k,id| #![no_triggers] new.m(k, id) == (if key == k { id == val } else { self.m(k, id) }))
            &&& (forall|x,y| #![no_triggers] new.gap(x,y) == (self.gap(x,y) && !(!key_le(key, x) && !key_le(y, key))))
        }


        
        /**************************************
            predicates built on interface
        **************************************/

        
        #[verifier::inline_only]
        pub open spec fn contains(&self, k : K) -> bool {
           exists|id| #![no_triggers] self.m(k, id) 
        }
        
        #[verifier::inline_only]
        pub open spec fn g_l_b(&self, k: K, glb: K) -> bool {
            // glb less than k
            &&& key_le(glb, k)
            // glb definition
            &&& (exists|id| #![no_triggers] self.m(glb, id))
            &&& ((exists|id| #![no_triggers] self.m(k, id)) ==> (glb == k))
            &&& self.gap(glb, k)
        }


        
        // constructor from an actual implementation
        pub(in crate) closed spec fn from(x: StrictlyOrderedMap<K, ID>) -> Self {
            SOMapModel(x)
        }

        pub(in crate) proof fn from_ensures(x : StrictlyOrderedMap<K, ID>)
            ensures
                forall|k, id| #![auto] (x@.dom().contains(k) && x@[k] == id) == Self::from(x).m(k, id),
                forall|k,j| #![auto] x.gap(KeyIterator::new_spec(k), KeyIterator::new_spec(j)) == Self::from(x).gap(k, j),
                // need to expose for the new proof
                K::zero_spec() == key_zero::<K>(),
                // need to expose for get
                forall|k : K, j : K| #![auto] key_le(k, j) == k.cmp_spec(j).le()
        {
        }

        
    }

    /* DMap Abstraction */
    pub struct DMapModel<#[verifier(maybe_negative)] K: Key + VerusClone, ID>(DelegationMap<K, ID>);

    impl<K: Key + VerusClone, ID : VerusClone> DMapModel<K, ID> {

        /**************************************
            primitives of the interface
        **************************************/

        // lows: 0______x_______y____
        // m:    0000000xxxxxxxxyyyyy

        pub closed spec fn m(&self, k : K, id : ID) -> bool {
            // TODO: m is total, is this necessary?
            &&& self.0.m@.dom().contains(k)
            &&& self.0.m@[k] == id
        }


        pub closed spec fn lows(&self) -> SOMapModel<K, ID> {
            SOMapModel(self.0.lows)
        }

        pub proof fn map_properties(&self)
            ensures 
                forall|k, id_1, id_2| #![no_triggers] self.m(k, id_1) && self.m(k, id_2) ==> id_1 == id_2,
        {}





        /**************************************
            transitions built on interface
        **************************************/



        #[verifier::inline_only]
        pub open spec fn new(&self, id_zero: ID) -> bool {
            // all keys in m, value set to id_zero
            &&& forall|k, id| #![no_triggers] self.m(k, id) == (id == id_zero)
            // only key in lows is k_zero with id_zero
            &&& forall|k, id| #![no_triggers] self.lows().m(k, id) == (k == key_zero::<K>() && id == id_zero)
            // gap is true for every pair of keys
            &&& forall|k, j| #![no_triggers] self.lows().gap(k,j)
        }

        #[verifier::inline_only]
        pub open spec fn get(&self, k : K, id : ID) -> bool
        {
            &&& exists|glb : K| #![no_triggers] self.get_internal(k, id, glb)
        }

        #[verifier::inline_only]
        pub open spec fn get_internal(&self, k: K, id : ID, glb : K) -> bool {
            // glb is the greatest lower bound for k in the map
            &&& self.lows().g_l_b(k, glb)
            // id is equal to the glb's id
            &&& self.lows().m(glb, id)
        }



        #[verifier::inline_only]
        pub open spec fn set(&self, new: Self, lo: K, hi: K, dst: ID, hi_id : ID, hi_glb : K, lows_1: SOMapModel<K, ID>, lows_2: SOMapModel<K, ID>) -> bool {
            &&& !key_le(hi, lo)
            &&& self.get_internal(hi, hi_id, hi_glb)
            // m update
            &&& forall |k : K| #![no_triggers] (key_le(lo, k) && !key_le(hi, k)) ==> (forall|id : ID| new.m(k, id) == (id == dst))
            &&& forall |k : K| #![no_triggers] !(key_le(lo, k) && !key_le(hi, k)) ==> (forall|id : ID| (new.m(k, id) == self.m(k, id)))
            // lows update
            &&& self.lows().set(lows_1, hi, hi_id)
            &&& lows_1.erase(lows_2, lo, hi)
            &&& lows_2.set(new.lows(), lo, dst)

        }

        // handles the case where hi is None (i.e. set everything above low)
        #[verifier::inline_only]
        pub open spec fn set_unbounded(&self, new: Self, lo: K, dst: ID, lows_2: SOMapModel<K, ID>) -> bool {
            // m update (everything about lo is dst)
            &&& forall |k : K| #![no_triggers] key_le(lo, k) ==> (forall|id : ID| new.m(k, id) == (id == dst))
            &&& forall |k : K| #![no_triggers] !key_le(lo, k) ==> (forall|id : ID| (new.m(k, id) == self.m(k, id)))
            // lows update
            &&& self.lows().erase_unbounded(lows_2, lo)
            &&& lows_2.set(new.lows(), lo, dst)
        }

        pub(in crate) closed spec fn from(inner_map: DelegationMap<K, ID>) -> Self {
            DMapModel(inner_map)
        }

        pub(in crate) proof fn from_ensures(dm : DelegationMap<K, ID>)
            ensures
                // part of interface
                forall|k, id| #![auto] (dm.m@.dom().contains(k) && dm.m@[k] == id) == Self::from(dm).m(k, id),
                // TODO: Already captured by SOMapModel::from_ensures...
                forall|k, id| #![auto] (dm.lows@.dom().contains(k) && dm.lows@[k] == id) == Self::from(dm).lows().m(k, id),
                forall|k,j| dm.lows.gap(KeyIterator::new_spec(k), KeyIterator::new_spec(j)) == #[trigger] Self::from(dm).lows().gap(k, j),
                // need to expose for the new proof
                K::zero_spec() == key_zero::<K>(),
                // need to expose for get
                forall|k : K, j : K| #![auto] key_le(k, j) == k.cmp_spec(j).le()
                // TODO: what else to expose?
        {
        }
    }

}

proof fn no_match_means_doesnt_contain<K, V>(map: Map<K, V>, k: K)
    requires
        forall|v: V| !map.contains_pair(k, v),
    ensures
        !map.contains_key(k),
{
    if map.contains_key(k) {
        let v = map[k];
        assert(map.contains_pair(k, v));
    }
}

proof fn has_all_keys_means_full<K, V>(map: Map<K, V>)
    requires
        forall|k: K| map.contains_key(k),
    ensures
        map.dom().is_full(),
{
    assert(map.dom() =~= Set::full());
}

#[verifier::epr_check]
mod EPRProof {
    use crate::Key;
    use crate::VerusClone;
    use crate::EPRModel::*;
    use crate::KeyIterator;

    spec fn m_has_key<K: Key + VerusClone, ID: VerusClone>(dm: DMapModel<K, ID>, k : K) -> bool {
       exists|id| #![no_triggers] dm.m(k, id) 
    }

    pub closed spec fn dmap_invariant<K: Key + VerusClone, ID: VerusClone>(dm: DMapModel<K, ID>) -> bool {
        // lows contains zero_spec
        &&& exists|id : ID| #![no_triggers] dm.lows().m(key_zero(), id)
        // TODO: avoid forall exists?
        // domain of view is full
        &&& forall|k| #![no_triggers] m_has_key(dm, k)
        // lows contains i, gap i j, i < k < j => m(k) = lows(i)
        // alternate representation:
        // if in lows, the value agrees in m
        &&& forall|k , id| #![no_triggers] dm.lows().m(k, id) ==> dm.m(k, id)
        // if i and j have a gap, and i has id_1 in lows, j has id_2 in m, then j must have id_2 in lows
        // i.e. if there is a gap, the value in lows is the same as the value in m
        &&& forall|i, j, id_1, id_2|
                #![no_triggers]
                key_le(i, j)
            &&  dm.lows().m(i, id_1)
            &&  dm.m(j, id_2)
            &&  dm.lows().gap(i, j)
            &&  id_1 != id_2
            ==> dm.lows().m(j, id_2)

        /*
        &&& forall|k, i, j|
                      dm.lows().m()@.contains_key(i)
                   && dm.lows().m().gap(KeyIterator::new_spec(i), j)
                   && #[trigger] KeyIterator::between(KeyIterator::new_spec(i), KeyIterator::new_spec(k), j)
                   ==> forall|id| #![all_triggers] dm.m(k, id) == DMapModel::<K, ID>::has_pair(dm.lows().m(), i, id)
        
        // porting ivy-delmap-simplified
        &&& dm.lows().m().valid()
        // this fails as map is an orderedmap exclusive
        // TODO: Do we add it to the Strictly ordered interface?
        &&& dm.lows().m().map(K::zero_spec()).is_Some()
        */
    }

    // this is to be invoked in the executable version's proof
    
    pub proof fn get_postcondition<K: Key + VerusClone, ID: VerusClone>(dm : DMapModel<K, ID>, k : K, id : ID)
        requires
            dmap_invariant(dm),
            dm.get(k, id),
        ensures
            dm.m(k, id),
    {
        key_le_properties::<K>();
        dm.lows().gap_properties();
        dm.lows().map_properties();
        dm.map_properties();
        // TODO: MBQI should resolve needing existential witness? 
        // assert(m_has_key(dm, k));
    }

    pub proof fn new_preserves_inv<K: Key + VerusClone, ID: VerusClone>(dm: DMapModel<K, ID>, id_zero : ID)
        requires
            dm.new(id_zero),
        ensures 
            dmap_invariant(dm),
    {
        // TODO: MBQI should resolve needing existential witness? 
        // assert(dm.lows().m(key_zero(), id_zero));
        // assert forall|k| m_has_key(dm, k) by {
        //     assert(dm.m(k, id_zero));
        // };
    }

    pub proof fn set_postcondition<K: Key + VerusClone, ID: VerusClone>(dm: DMapModel<K, ID>, dm_: DMapModel<K, ID>, lo: K, hi: K, dst: ID, hi_id : ID, hi_glb : K, lows_1: SOMapModel<K, ID>, lows_2: SOMapModel<K, ID>) 
        requires
            dmap_invariant(dm),
            dm.set(dm_, lo, hi, dst, hi_id, hi_glb, lows_1, lows_2),
        ensures
            forall |k : K| #![no_triggers] (key_le(lo, k) && !key_le(hi, k)) ==> dm_.m(k, dst),
            forall |k : K| #![no_triggers] !(key_le(lo, k) && !key_le(hi, k)) ==> (forall|id : ID| (dm_.m(k, id) == dm.m(k, id))),
            dmap_invariant(dm_),
    {
        key_le_properties::<K>();
        dm.lows().gap_properties();
        dm.lows().map_properties();
        dm.map_properties();
        dm_.lows().gap_properties();
        dm_.lows().map_properties();
        dm_.map_properties();
        lows_1.map_properties();
        lows_1.gap_properties();
        lows_2.map_properties();
        lows_2.gap_properties();
        // assert forall|k| #![all_triggers] m_has_key(dm_, k) by {
        //     if key_le(lo, k) && !key_le(hi, k) {
        //         assert(dm_.m(k, dst));
        //     } else {
        //         assert(m_has_key(dm, k));
        //     }
        // }
        // if lo == key_zero::<K>() {
        //     assert(dm_.lows().m(key_zero(), dst));
        // } else {
        //     assert(exists|id : ID| dm_.lows().m(key_zero(), id));
        // } 
        // assert forall|k , id| #![all_triggers] dm_.lows().m(k, id) implies dm_.m(k, id) by {
        //     assert(m_has_key(dm, k));
        // }
        
    }

    pub proof fn set_unbounded_postcondition<K: Key + VerusClone, ID: VerusClone>(dm: DMapModel<K, ID>, dm_: DMapModel<K, ID>, lo: K, dst: ID, lows_2: SOMapModel<K, ID>) 
        requires
            dmap_invariant(dm),
            dm.set_unbounded(dm_, lo, dst, lows_2),
        ensures
            forall |k : K| #![no_triggers] (key_le(lo, k)) ==> dm_.m(k, dst),
            forall |k : K| #![no_triggers] !(key_le(lo, k)) ==> (forall|id : ID| (dm_.m(k, id) == dm.m(k, id))),
            dmap_invariant(dm_),
    {
        key_le_properties::<K>();
        dm.lows().gap_properties();
        dm.lows().map_properties();
        dm.map_properties();
        dm_.lows().gap_properties();
        dm_.lows().map_properties();
        dm_.map_properties();
        lows_2.map_properties();
        lows_2.gap_properties();
        // assert forall|k| #![all_triggers] m_has_key(dm_, k) by {
        //     if key_le(lo, k) {
        //         assert(dm_.m(k, dst));
        //     } else {
        //         assert(m_has_key(dm, k));
        //     }
        // }
        // 
        // if lo == key_zero::<K>() {
        //     assert(dm_.lows().m(key_zero(), dst));
        // } else {
        //     assert(exists|id : ID| dm_.lows().m(key_zero(), id));
        // }

        // assert forall|k , id| #![all_triggers] dm_.lows().m(k, id) implies dm_.m(k, id) by {
        //     if k == lo {
        //         assert(key_le(lo, k));
        //     } else {
        //         assert(m_has_key(dm, k));
        //     }
        // }
    }
}

impl<K: Key + VerusClone, ID: VerusClone> DelegationMap<K, ID> {
    pub closed spec fn view(self) -> Map<K,ID> {
        self.m@
    }

    pub closed spec fn valid(self) -> bool {
        &&& self.lows.valid()
        &&& self@.dom().is_full()
        &&& self.lows@.contains_key(K::zero_spec()) 
        &&& EPRProof::dmap_invariant(EPRModel::DMapModel::<K, ID>::from(self))
    }

    pub fn new(k_zero: K, id_zero: ID) -> (s: Self)
        requires 
            k_zero == K::zero_spec(),
        ensures
            s.valid(),
            s@[k_zero] == id_zero,
    {
        let mut lows = StrictlyOrderedMap::new();
        lows.set(k_zero, id_zero);
        let m = Ghost(Map::total(|k| id_zero));
        let s = DelegationMap { lows, m };
        proof {
            let model = EPRModel::DMapModel::<K, ID>::from(s);
            EPRModel::DMapModel::<K, ID>::from_ensures(s);
            K::zero_properties();
            K::cmp_properties();
            EPRProof::new_preserves_inv(model, id_zero);
        }
        s
    }


    // Returns the greatest_lower_bound as evidence for the proof of correctness for set
    fn get_internal(&self, k: &K) -> (res: (ID, Ghost<KeyIterator<K>>))
        requires
            self.valid(),
        ensures ({
            let (id, glb) = res;
            let model = EPRModel::DMapModel::<K, ID>::from(*self);
            glb@.k.is_Some() && model.get_internal(*k, id, *glb@.get_spec())
        }),
    {
        let ki = KeyIterator::new(k.clone());
        let glb = self.lows.greatest_lower_bound(&ki);
        let id = self.lows.get(glb.get()).unwrap().clone();
        proof {
            let model = EPRModel::DMapModel::<K, ID>::from(*self);
            EPRModel::DMapModel::<K, ID>::from_ensures(*self);
            
            K::zero_properties();
            K::cmp_properties();
            EPRModel::key_le_properties::<K>();
            assert(glb.k.is_Some());
            let glb = *glb.get_spec();
            let k = *k;
            assert(model.lows().m(glb, id));
            if glb != k {
                let hi = choose|hi| #![auto] self.lows.gap(KeyIterator::new_spec(glb), hi) && KeyIterator::between(KeyIterator::new_spec(glb), ki, hi);
                if self.lows@.contains_key(k) {
                    self.lows.gap_means_empty(KeyIterator::new_spec(glb), hi, ki);
                }
            }
        }
        (id, Ghost(glb))
    }

    pub fn get(&self, k: &K) -> (id: ID) 
        requires
            self.valid(),
        ensures 
            id == self@[*k],
    {
        let (id, glb_ret) = self.get_internal(k);
        proof {
            let model = EPRModel::DMapModel::<K, ID>::from(*self);
            EPRModel::DMapModel::<K, ID>::from_ensures(*self);
            K::zero_properties();
            K::cmp_properties();
            EPRProof::get_postcondition(model, *k, id);
        }
        id
    }

        
    // Maps keys from [lo, hi) to dst
    pub fn set(&mut self, lo: KeyIterator<K>, hi: KeyIterator<K>, dst: ID)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            forall |ki:KeyIterator<K>| #[trigger] KeyIterator::between(lo, ki, hi) ==> self@[*ki.get()] == dst,
            forall |ki:KeyIterator<K>| !ki.is_end_spec() && !(#[trigger] KeyIterator::between(lo, ki, hi)) ==> self@[*ki.get()] == old(self)@[*ki.get()],
    {
        if lo.lt(&hi) {
            let ghost mut hi_glb : K; 
            let ghost mut hi_id : ID; 
            if !hi.is_end() {
                // Get the current value of hi
                let (id, glb_ret) = self.get_internal(hi.get());
                proof { hi_glb = *glb_ret@.get(); }
                proof { hi_id = id; }
                // Set it explicitly
                self.lows.set(hi.get().clone(), id);
            }
            let ghost mut lows_post_hi_set; proof { lows_post_hi_set = self.lows; }
            self.lows.erase(&lo, &hi);
            let ghost mut lows_post_erase; proof { lows_post_erase = self.lows; }
            self.lows.set(lo.get().clone(), dst);
            self.m = Ghost(self.m@.union_prefer_right(
                        Map::new(|k| KeyIterator::between(lo, KeyIterator::new_spec(k), hi),
                                 |k| dst)));
            proof {
                has_all_keys_means_full(self.m@);
                assert(self.m@.dom().is_full());
            }
            proof {
                let model = EPRModel::DMapModel::<K, ID>::from(*old(self));
                EPRModel::DMapModel::<K, ID>::from_ensures(*old(self));
                let lows_1 = EPRModel::SOMapModel::<K, ID>::from(lows_post_hi_set);
                EPRModel::SOMapModel::<K, ID>::from_ensures(lows_post_hi_set);
                let lows_2 = EPRModel::SOMapModel::<K, ID>::from(lows_post_erase);
                EPRModel::SOMapModel::<K, ID>::from_ensures(lows_post_erase);
                let new_model = EPRModel::DMapModel::<K, ID>::from(*self);
                EPRModel::DMapModel::<K, ID>::from_ensures(*self);
                K::zero_properties();
                K::cmp_properties();
                let lo = *lo.get();
                if hi.is_end_spec() {
                    assert forall|k,id| #![auto] (model.lows().m(k, id) && !(EPRModel::key_le(lo, k))) implies lows_2.m(k, id) by {
                        assert(lows_post_erase@.contains_key(k));
                    }
                    assert(model.lows().erase_unbounded(lows_2, lo));
                    assert(model.set_unbounded(new_model, lo, dst, lows_2));
                    EPRProof::set_unbounded_postcondition(model, new_model, lo, dst, lows_2);
                } else {
                    let hi = *hi.get();

                    assert forall|k,id| (lows_1.m(k, id) && !(EPRModel::key_le(lo, k) && !EPRModel::key_le(hi, k))) implies lows_2.m(k, id) by {
                        assert(lows_post_erase@.contains_key(k));
                    }
                    
                    assert forall|x,y| (lows_1.gap(x,y) || (lows_1.gap(x,lo) && lows_1.gap(hi,y) && (EPRModel::key_le(y, hi) || !lows_1.contains(hi)))) implies lows_2.gap(x,y) by {
                        if lows_1.gap(x,y) {
                            assert(lows_post_erase.gap(KeyIterator::new_spec(x), KeyIterator::new_spec(y)));
                        } else {
                            if !lows_1.contains(hi) {
                                assert(forall|id| !lows_1.m(hi, id));
                                assert forall|id : ID| !lows_post_erase@.contains_pair(hi, id) by {
                                    assert(!lows_1.m(hi, id));
                                };
                                no_match_means_doesnt_contain(lows_post_erase@, hi);
                                assert(!lows_post_erase@.contains_key(*KeyIterator::new_spec(hi).get()));
                            }
                            assert(lows_post_erase.gap(KeyIterator::new_spec(x), KeyIterator::new_spec(y)));
                        }
                    }
                    assert(model.set(new_model, lo, hi, dst, hi_id, hi_glb, lows_1, lows_2));
                    EPRProof::set_postcondition(model, new_model, lo, hi, dst, hi_id, hi_glb, lows_1, lows_2);
                }
            }
        }
        assert forall |ki:KeyIterator<K>| KeyIterator::between(lo, ki, hi) implies #[trigger] self@[*ki.get()] == dst by {
            K::cmp_properties();
        };
    }
}

// ====================================================================================================================

struct KeyInt {
    i: Option<usize>,
}

impl KeyInt {
    fn new(u: usize) -> Self {
        KeyInt { i: Some(u) }
    }

    fn get(&self) -> usize 
        requires self != Self::zero_spec(),
    {
        self.i.unwrap()
    }

//    fn to_str(&self) -> String {
//        match self.i {
//            None => "Zero".to_string(),
//            Some(i) => format!("{}", i),
//        }
//    }
}

impl Key for KeyInt {
    closed spec fn zero_spec() -> Self {
        KeyInt { i: None }
    }

    fn zero() -> (z: Self )
    {
        KeyInt { i: None }
    }
    
    closed spec fn cmp_spec(self, other: Self) -> Ordering {
        match (self.i, other.i) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(i), Some(j)) => {
                if i < j {
                    Ordering::Less
                } else if i == j {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
    }

    fn cmp(&self, other: &Self) -> Ordering {
        match (self.i, other.i) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(i), Some(j)) => {
                if i < j {
                    Ordering::Less
                } else if i == j {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
    }

    proof fn zero_properties() { }

    proof fn cmp_properties() { }
}

impl VerusClone for KeyInt {
    fn clone(&self) -> (o: Self) {
        KeyInt { i: match self.i {
            Some(x) => Some(x),
            None => None,
        } }
    }
}

}   // end verus!

// ====================================================================================================================

fn main() {
//     // println!("Hello, world!");
//     //    let mut v = StrictlyOrderedVec::new();
//     //    v.insert(KeyInt { i: Some(2) });
//     //    v.insert(KeyInt { i: Some(1) });
//     //    v.insert(KeyInt { i: Some(5) });
//     //    v.set(2, KeyInt { i: Some(4) });
//     //    assert_eq!(v.index(0).i.unwrap(), 1);
//     //    let mut i = 0;
//     //    while i < v.len() {
//     //        println!("v[{}] = {}", i, v.index(i).i.unwrap());
//     //        i = i + 1;
//     //    }
// 
//     let mut m = DelegationMap::new(KeyInt::zero(), KeyInt::zero());
//     m.set(
//         KeyIterator::new(KeyInt::new(2)),
//         KeyIterator::new(KeyInt::new(4)),
//         KeyInt::new(42),
//     );
//     println!("0 = {}", m.id_map.keys.v[0].to_str());
//     println!("1 = {}", m.id_map.keys.v[1].to_str());
//     println!("2 = {}", m.id_map.keys.v[2].to_str());
//     m.set(
//         KeyIterator::new(KeyInt::new(6)),
//         KeyIterator::new(KeyInt::new(10)),
//         KeyInt::new(330),
//     );
// 
//     println!("3 = {}", m.get(KeyInt::new(3)).to_str());
// 
//     println!(
//         "1 = {}\n3 = {}\n5 = {}",
//         m.get(KeyInt::new(1)).to_str(),
//         m.get(KeyInt::new(3)).to_str(),
//         m.get(KeyInt::new(5)).to_str()
//     );
// 
//     println!(
//         "1 = {}, 3 = {}, 5 = {}, 8 = {}, 15 = {}",
//         m.get(KeyInt::new(1)).to_str(),
//         m.get(KeyInt::new(3)).to_str(),
//         m.get(KeyInt::new(5)).to_str(),
//         m.get(KeyInt::new(8)).to_str(),
//         m.get(KeyInt::new(15)).to_str()
//     );
}
