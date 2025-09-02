use vstd::prelude::*;

verus!{

pub trait Iterator {
    type Item;

    #[verifier::prophetic]
    spec fn seq(&self) -> Seq<Self::Item>;

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

/* vec iterator */

pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
}

impl<'a, T> VecIterator<'a, T> {
    #[verifier::type_invariant]
    closed spec fn vec_iterator_type_inv(self) -> bool {
        self.i <= self.v.len()
    }
}

pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures iter.seq() == v@.map(|i, v| &v)
{
    VecIterator { v: v, i: 0 }
}

impl<'a, T> Iterator for VecIterator<'a, T> {
    type Item = &'a T;

    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.v@.skip(self.i as int).map(|i, v| &v)
    }

    closed spec fn completes(&self) -> bool {
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.i < self.v.len() {
            let i = self.i;
            self.i = self.i + 1;
            return Some(&self.v[i]);
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

// Take3 iterator
pub struct Take3<T> {
    pub inner: T,
    pub count: usize,
    // pub ghost_count: Ghost<int>,
    // pub start_pos: Ghost<int>,
}

impl<T: Iterator> Take3<T> {
    fn new(iter: T) -> (r: Take3<T>)
        requires
            true, //iter.inv(),
        ensures
            //r.inv(),
            r.inner == iter,
            r.count == 0,
            //r.events().len() == 0,
    {
        Take3 { inner: iter, count: 0 } //, ghost_count: Ghost(0), start_pos: Ghost(iter.events().len() as int) }
    }

    // spec fn spec_new(iter: T) -> Take3<T> {
    //     Take3 { inner: iter, count: 0, ghost_count: Ghost(0), start_pos: Ghost(iter.events().len() as int) }
    // }
}

impl<T: Iterator> Iterator for Take3<T> {
    type Item = T::Item;

    #[verifier::prophetic]
    open spec fn seq(&self) -> Seq<Self::Item> {
        if self.count >= 3 {
            Seq::empty()
        } else {
            self.inner.seq().take(3 - self.count)
        }
    }

    #[verifier::prophetic]
    open spec fn completes(&self) -> bool {
        true //self.count >= 3 || self.inner.completes()
    }

    // open spec fn inv(&self) -> bool {
    //     &&& self.inner.inv()
    //     &&& 0 <= self.start_pos@
    //     &&& self.inner.events().len() == self.start_pos@ + self.count
    //     &&& {
    //         ||| self.count < 3 && self.count == self.ghost_count@
    //         ||| self.count == 3 && self.ghost_count@ >= 3
    //     }
    // }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        if self.count < 3 {
            self.count = self.count + 1;
            let r = self.inner.next();
            assume(false);
            r
        } else {
            assert(self.seq().len() == 0);
            None
        }
    }
}

// Skip3 iterator
pub struct Skip3<T> {
    pub inner: T,
    pub has_started: bool,
}

impl<T: Iterator> Skip3<T> {
    fn new(iter: T) -> (r: Skip3<T>)
        // requires
        //     iter.inv(),
        ensures
            //r.inv(),
            !r.has_started,
            r.inner == iter,
            //r.events().len() == 0,
    {
        Skip3 { inner: iter, has_started: false }
    }

    spec fn spec_new(iter: T) -> Skip3<T> {
        Skip3 { inner: iter, has_started: false }
    }
}

impl<T: Iterator> Iterator for Skip3<T> {
    type Item = T::Item;

    #[verifier::prophetic]
    open spec fn seq(&self) -> Seq<Self::Item> {
        // if self.has_started && self.inner.seq().len() >= 3 {
        //     self.inner.seq().skip(3)
        // } else {
        //     Seq::empty()
        // }
        if !self.has_started && self.inner.seq().len() >= 3 {
            self.inner.seq().skip(3)
        } else if !self.has_started {
            Seq::empty()
        } else {
            self.inner.seq()
        }
    }
    
    #[verifier::prophetic]
    open spec fn completes(&self) -> bool {
        self.inner.completes()
    }

    // open spec fn inv(&self) -> bool {
    //     &&& self.inner.inv()
    //     &&& 0 <= self.start_pos@
    //     &&& !self.has_started ==> self.start_pos@ == self.inner.events().len()
    //     &&& self.has_started ==> self.start_pos@ + 3 <= self.inner.events().len()
    //     // We only perform Next operations
    //     &&& forall |i| self.start_pos@ <= i < self.inner.events().len() ==> (#[trigger] self.inner.events()[i].op) is Next
    // }


    fn next(&mut self) -> (r: Option<Self::Item>) {
        if !self.has_started {
            let _ = self.inner.next();
            let _ = self.inner.next();
            let _ = self.inner.next();
            self.has_started = true;
        }
        self.inner.next()
    }
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
          && forall |i| 0 <= i < self.iter.seq().len() ==> call_requires(self.f, (#[trigger]self.iter.seq()[i], ))
          && forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> !self.prophs@.has_resolved(i)
    }

    fn new(iter: Iter, f: F) -> (s: Self)
        requires
            forall |i| 0 <= i < iter.seq().len() ==>
                call_requires(f, (#[trigger]iter.seq()[i], ))
        ensures
            s.seq().len() == iter.seq().len(),
            s.completes() ==> iter.completes(),
            s.completes() ==>
                forall |i| 0 <= i < s.seq().len() ==>
                    call_ensures(f, (iter.seq()[i],), #[trigger]s.seq()[i])
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
        }
        s
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
        Seq::new(self.iter.seq().len(), |i| {
            self.prophs@.proph_elem(self.idx@ + i).unwrap()
        })
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
                None
            }
            Some(elem) => {
                let output = (self.f)(elem);
                proof {
                    self.prophs.borrow_mut().resolve(self.idx@, output);
                    self.idx@ = self.idx@ + 1;
                }

                assert(self.map_iterator_type_inv());
                Some(output)
            }
        }
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

    let v: Vec<u8> = vec![1, 2, 3];

    let iter0 = vec_iter(&v);
    let iter1 = MapIterator::new(iter0, f);

    let w = collect_to_vec(iter1);

    assert(w.len() == 3);
    assert(w[0] == 2);
    assert(w[1] == 3);
    assert(w[2] == 4);
}



fn test_take3_seq(v: &Vec<u8>)
    requires
        v@.len() == 10,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
        v@[7] == 70,
        v@[8] == 80,
        v@[9] == 90,
{
    let mut iter = Take3::new(vec_iter(v));
    let r = iter.next();
    assert(r == Some(&0u8));
    let r = iter.next();
    assert(r == Some(&10u8));
    let r = iter.next();
    assert(r == Some(&20u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_take3_take3_seq(v: &Vec<u8>)
    requires
        v@.len() == 10,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
        v@[7] == 70,
        v@[8] == 80,
        v@[9] == 90,
{
    let mut iter = Take3::new(Take3::new(vec_iter(v)));
    let r = iter.next();
    assert(r == Some(&0u8));
    let r = iter.next();
    assert(r == Some(&10u8));
    let r = iter.next();
    assert(r == Some(&20u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_skip3_seq(v: &Vec<u8>)
    requires
        v@.len() == 7,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
{
    let mut iter = Skip3::new(vec_iter(v));
    let r = iter.next();
    assert(r == Some(&30u8));
    let r = iter.next();
    assert(r == Some(&40u8));
    let r = iter.next();
    assert(r == Some(&50u8));
    let r = iter.next();
    assert(r == Some(&60u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_skip3_skip3_seq(v: &Vec<u8>)
    requires
        v@.len() == 10,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
        v@[7] == 70,
        v@[8] == 80,
        v@[9] == 90,
{
    let mut iter = Skip3::new(Skip3::new(vec_iter(v)));
    let r = iter.next();
    assert(r == Some(&60u8));
    let r = iter.next();
    assert(r == Some(&70u8));
    let r = iter.next();
    assert(r == Some(&80u8));
    let r = iter.next();
    assert(r == Some(&90u8));
    let r = iter.next();
    assert(r.is_none());
}

// TODO: Should be able to prove termination
#[verifier::exec_allows_no_decreases_clause]
fn test_skip3_skip3_loop_iso_true(v: &Vec<u8>)
    requires
        v@.len() >= 6,
{
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = Skip3::new(Skip3::new(vec_iter(v)));
    let ghost i0 = iter;
    //let ghost mut count = iter.seq().len();
    loop
        invariant
            s + iter.seq().map_values(|e: &u8| *e) =~= v@.skip(6),
        ensures
            s =~= v@.skip(6),
        //decreases count //iter.seq().len(), //v@.len() - 6 - iter.events().len(),
    {
        if let Some(r) = iter.next() {
            proof {
                s = s.push(*r);
                //count = (count - 1) as nat;
            }
        } else {
            break;
        }
    }
    assert(s == v@.skip(6));
}



}  // verus!