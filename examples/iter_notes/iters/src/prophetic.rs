use std::iter;

use vstd::prelude::*;

verus!{

pub trait Iterator {
    type Item;

    /// Seq that will be returned
    #[verifier::prophetic]
    spec fn seq(&self) -> Seq<Self::Item>;

    /// Does this complete with a `None` after the above sequence?
    /// (As opposed to hanging indefinitely on a `next()` call)
    #[verifier::prophetic]
    spec fn completes(&self) -> bool;

    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.completes() == old(self).completes(),
            ({
                if old(self).seq().len() > 0 {
                    self.seq() == old(self).seq().drop_first()
                        && ret == Some(old(self).seq()[0])
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            });
}

pub trait DoubleEndedIterator : Iterator {
    fn next_back(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.completes() == old(self).completes(),
            ({
                if old(self).seq().len() > 0 {
                    self.seq() == old(self).seq().drop_last()
                        && ret == Some(old(self).seq().last())
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            });

}

/* vec iterator */

pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
    j: usize,
}

impl<'a, T> VecIterator<'a, T> {
    #[verifier::type_invariant]
    closed spec fn vec_iterator_type_inv(self) -> bool {
        self.i <= self.j <= self.v.len()
    }
}

pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures iter.seq() == v@.map(|i, v| &v)
{
    VecIterator { v: v, i: 0, j: v.len() }
}

impl<'a, T> Iterator for VecIterator<'a, T> {
    type Item = &'a T;

    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.v@.subrange(self.i as int, self.j as int).map(|i, v| &v)
    }

    closed spec fn completes(&self) -> bool {
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.i < self.j {
            let i = self.i;
            self.i = self.i + 1;
            return Some(&self.v[i]);
        } else {
            return None;
        }
    }
}

impl<'a, T> DoubleEndedIterator for VecIterator<'a, T> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.i < self.j {
            self.j = self.j - 1;
            return Some(&self.v[self.j]);
        } else {
            return None;
        }
    }
}

/* proph util (this should be implementable) */

pub trait Predicate<T> {
    #[verifier::prophetic]
    spec fn pred(&self, i: int, t: T) -> bool;
}

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::accept_recursive_types(Pred)]
pub tracked struct ProphSeq<T, Pred> { t: T, pred: Pred }

impl<T, Pred> ProphSeq<T, Pred>
    where Pred: Predicate<T>
{
    pub uninterp spec fn pred(&self) -> Pred;
    pub uninterp spec fn proph_elem(&self, i: int) -> Option<T>;
    pub uninterp spec fn has_resolved(&self, i: int) -> bool;

    pub axiom fn new(pred: Pred) -> (tracked s: Self)
        ensures
            s.pred() == pred,
            forall |i| !s.has_resolved(i);


    pub axiom fn proph_elem_meets_pred(tracked &self)
        ensures forall |i: int| (match #[trigger] self.proph_elem(i) {
            Some(p) => self.pred().pred(i, p),
            None => true,
        });

    pub axiom fn resolve(tracked &mut self, i: int, t: T)
        requires
            !old(self).has_resolved(i),
            old(self).pred().pred(i, t),
        ensures
            self.pred() == old(self).pred(),
            forall |j| self.proph_elem(j) == old(self).proph_elem(j),
            forall |j| i != j ==> self.has_resolved(j) == old(self).has_resolved(j),
            self.proph_elem(i) == Some(t);
}

/* map iterator */

ghost struct MapIteratorPred<Iter, F> {
    iter: Iter,
    f: F,
}

impl<Item, Iter, F> Predicate<Item> for MapIteratorPred<Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    #[verifier::prophetic]
    closed spec fn pred(&self, i: int, t: Item) -> bool {
        call_ensures(self.f, (self.iter.seq()[i],), t)
    }
}

pub struct MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    f: F,
    iter: Iter,

    prophs: Tracked<ProphSeq<Item, MapIteratorPred<Iter, F>>>,
    idx: Ghost<int>,
}

impl<Item, Iter, F> MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    closed spec fn map_iterator_type_inv(self) -> bool {
        0 <= self.idx@ <= self.prophs@.pred().iter.seq().len()
          && self.iter.seq() =~= self.prophs@.pred().iter.seq().skip(self.idx@)
          && self.prophs@.pred().f == self.f
          && (forall |i| 0 <= i < self.iter.seq().len() ==> call_requires(self.f, (self.iter.seq()[i], )))
          && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> !self.prophs@.has_resolved(i))
    }

    fn new(iter: Iter, f: F) -> (s: Self)
        requires
            forall |i| 0 <= i < iter.seq().len() ==>
                call_requires(f, (iter.seq()[i], ))
        ensures
            s.seq().len() <= iter.seq().len(),
            forall |i| 0 <= i < s.seq().len() ==>
                call_ensures(f, (iter.seq()[i],), s.seq()[i]),
            s.completes() ==> iter.completes() && s.seq().len() == iter.seq().len(),
    {
        let s = Self {
            f: f,
            iter: iter,
            prophs: Tracked(ProphSeq::new(MapIteratorPred {
                iter: iter,
                f: f,
            })),
            idx: Ghost(0),
        };
        
        assert(s.map_iterator_type_inv());
        proof {
            s.prophs.borrow().proph_elem_meets_pred();
            // PAPER CUT: can't call lemma with prophetic arg
            broadcast use unwrap_up_to_first_none_len_le; //(s.seq_of_options());
            broadcast use unwrap_up_to_first_none_len_le_values;
        }
        s
    }

    #[verifier::prophetic]
    spec fn seq_of_options(&self) -> Seq<Option<Item>> {
        Seq::new(self.iter.seq().len(), |i| {
            self.prophs@.proph_elem(self.idx@ + i)
        })
    }
}

spec fn unwrap_up_to_first_none<T>(seq: Seq<Option<T>>) -> Seq<T>
    decreases seq.len()
{
    if seq.len() == 0 {
        seq![]
    } else if seq[0].is_some() {
        seq![seq[0].unwrap()] + unwrap_up_to_first_none(seq.drop_first())
    } else {
        seq![]
    }
}

broadcast proof fn unwrap_up_to_first_none_len_le<T>(seq: Seq<Option<T>>)
    ensures #[trigger] unwrap_up_to_first_none(seq).len() <= seq.len(),
        (forall |i| 0 <= i < seq.len() ==> seq[i].is_some()) ==>
            unwrap_up_to_first_none(seq).len() == seq.len(),
    decreases seq.len()
{
    if seq.len() != 0 && seq[0].is_some() {
        unwrap_up_to_first_none_len_le(seq.drop_first());
    }
}

broadcast proof fn unwrap_up_to_first_none_len_le_values<T>(seq: Seq<Option<T>>, i: int)
    requires 0 <= i < unwrap_up_to_first_none(seq).len()
    ensures
        i < seq.len(),
        seq[i].is_some(),
        #[trigger] unwrap_up_to_first_none(seq)[i] == seq[i].unwrap(),
    decreases seq.len()
{
    if i > 0 {
        unwrap_up_to_first_none_len_le_values(seq.drop_first(), i-1);
    }
}

impl<Item, Iter, F> Iterator for MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    type Item = Item;

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        unwrap_up_to_first_none(self.seq_of_options())
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
          && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> self.prophs@.proph_elem(i).is_some())
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.map_iterator_type_inv());

        match self.iter.next() {
            None => {
                assert(self.map_iterator_type_inv());
                return None;
            }
            Some(elem) => {
                let output = (self.f)(elem);
                proof {
                    self.prophs.borrow_mut().resolve(self.idx@, output);
                    self.idx@ = self.idx@ + 1;
                }

                assert(self.seq_of_options() == old(self).seq_of_options().drop_first());
                assert(self.map_iterator_type_inv());
                return Some(output);
            }
        }
    }
}

// take

struct TakeIterator<Iter> {
    iter: Iter,
    count_remaining: usize,
}

impl<Iter: Iterator> TakeIterator<Iter> {
    fn new(iter: Iter, count: usize) -> (s: Self)
        ensures
            s.seq() == (if iter.seq().len() < count { iter.seq() } else { iter.seq().take(count as int) }),
            s.completes() <==> iter.completes() || iter.seq().len() >= count,
    {
        TakeIterator {
            iter: iter,
            count_remaining: count,
        }
    }
}

impl<Iter: Iterator> Iterator for TakeIterator<Iter> {
    type Item = Iter::Item;

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        if self.iter.seq().len() < self.count_remaining { self.iter.seq() } else { self.iter.seq().take(self.count_remaining as int) }
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes() || self.iter.seq().len() >= self.count_remaining
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        if self.count_remaining == 0 {
            None
        } else {
            self.count_remaining = self.count_remaining - 1;
            self.iter.next()
        }
    }
}

// skip

struct SkipIterator<Iter> {
    iter: Iter,
}

impl<Iter: Iterator> SkipIterator<Iter> {
    fn new(iter: Iter, count: usize) -> (s: Self)
        ensures
            s.seq() == (if iter.seq().len() < count { seq![] } else { iter.seq().skip(count as int) }),
            s.completes() <==> iter.completes(),
            iter.seq().len() < count ==> iter.completes(),
    {
        let mut i = 0;
        let mut iter0 = iter;
        while i < count
            invariant
                i <= count,
                iter0.seq() == (if iter.seq().len() < i { seq![] } else { iter.seq().skip(i as int) }),
                iter0.completes() <==> iter.completes(),
                iter.seq().len() < i ==> iter.completes(),
            decreases count - i,
        {
            iter0.next();
            i += 1;
        }
        
        SkipIterator {
            iter: iter0,
        }
    }
}

impl<Iter: Iterator> Iterator for SkipIterator<Iter> {
    type Item = Iter::Item;

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.iter.seq()
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        self.iter.next()
    }
}

// reverse iterator

struct ReverseIterator<Iter> {
    iter: Iter,
}

impl<Iter: Iterator + DoubleEndedIterator> ReverseIterator<Iter> {
    fn new(iter: Iter) -> (s: Self)
        ensures
            s.seq() == iter.seq().reverse(),
            s.completes() <==> iter.completes(),
    {
        ReverseIterator {
            iter: iter,
        }
    }
}

impl<Iter: Iterator + DoubleEndedIterator> Iterator for ReverseIterator<Iter> {
    type Item = Iter::Item;

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.iter.seq().reverse()
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        self.iter.next_back()
    }
}

impl<Iter: Iterator + DoubleEndedIterator> DoubleEndedIterator for ReverseIterator<Iter> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        self.iter.next()
    }
}

// collect

#[verifier::exec_allows_no_decreases_clause]
fn collect_to_vec<Iter: Iterator>(iter: Iter) -> (s: Vec<Iter::Item>)
    ensures s@ == iter.seq(),
        iter.completes(),
{
    let mut iter0 = iter;
    let mut v = vec![];
    loop
        invariant
            v@ + iter0.seq() =~= iter.seq(),
            iter.completes() == iter0.completes(),
    {
        match iter0.next() {
            Some(elem) => {
                v.push(elem);
            }
            None => {
                return v;
            }
        }
    }
}

// examples

fn test() {
    let f = |i: &u8| -> (out: u8)
        requires i < 255,
        ensures out == i + 1,
        {
            *i + 1
        };
    let g = |i: u8| -> (out: u8)
        requires i >= 3
        ensures out == i - 3,
        {
            i - 3
        };

    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];

    let iter = vec_iter(&v);
    let iter = ReverseIterator::new(iter); // 6 5 4 3 2 1
    let iter = MapIterator::new(iter, f);  // 7 6 5 4 3 2
    let iter = TakeIterator::new(iter, 5); // 7 6 5 4 3
    let iter = MapIterator::new(iter, g);  // 4 3 2 1 0
    let iter = SkipIterator::new(iter, 1); // 3 2 1 0
    let iter = TakeIterator::new(iter, 3); // 3 2 1
    let w = collect_to_vec(iter);

    assert(w@ === seq![3, 2, 1]);
}

#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
fn test_loop() {
    let f = |i: &u8| -> (out: u8)
        requires i < 255,
        ensures out == i + 1,
        {
            *i + 1
        };
    let g = |i: u8| -> (out: u8)
        requires i >= 3
        ensures out == i - 3,
        {
            i - 3
        };

    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];

    let iter = vec_iter(&v);
    let iter = ReverseIterator::new(iter); // 6 5 4 3 2 1
    let iter = MapIterator::new(iter, f);  // 7 6 5 4 3 2
    let iter = TakeIterator::new(iter, 5); // 7 6 5 4 3
    let iter = MapIterator::new(iter, g);  // 4 3 2 1 0
    let iter = SkipIterator::new(iter, 1); // 3 2 1 0
    let iter = TakeIterator::new(iter, 3); // 3 2 1

    // for elem in iter {
    //    assert(1 <= elem <= 3);
    // }

    let mut iter = iter;
    let ghost iter_snapshot = iter;
    let ghost mut idx = 0;
    loop
        invariant
            0 <= idx <= iter_snapshot.seq().len(),
            iter.seq() =~= iter_snapshot.seq().skip(idx)
    {
        match iter.next() {
            None => {
                break;
            }
            Some(elem) => {
                /* body */
                assert(1 <= elem <= 3);
            }
        }

        proof { idx = idx + 1; }
    }
}

fn all_true<'a, I: Iterator<Item=&'a bool>>(iter: &mut I) -> (r: bool)
    requires
        old(iter).completes(),
    ensures
        r == forall |i| 0 <= i < old(iter).seq().len() ==> *#[trigger]old(iter).seq()[i]
{
    // TODO
    assume(false);
    true
}

fn all_true_caller(v: &Vec<bool>)
    requires
        v@.len() == 10,
{
    let mut iter: VecIterator<bool> = vec_iter(v);
    let ghost iter_snapshot = iter;
    assert(iter.seq() == v@.map(|i, v| &v));
    let b = all_true(&mut iter);
    proof {
        if b {
            // Note: We have to mention the iter_snapshot-based trigger to get the "real"
            //       assertion on the following line to go through
            assert(forall |i| 0 <= i < v@.len() ==> v@[i] == *iter_snapshot.seq()[i]);
            assert(forall |i| 0 <= i < v@.len() ==> v@[i]);
        }
    }
}
}

