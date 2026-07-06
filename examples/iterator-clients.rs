use vstd::prelude::*;
use vstd::std_specs::iter::zip_iterators;
use vstd::std_specs::iter::IteratorSpec;

verus! {

////////////////////////////////////////////////////////////
//
//    Creusot Examples
//
////////////////////////////////////////////////////////////

// From: https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/examples/iterators/03_std_iterators.rs#L28
fn all_zero(v: &mut Vec<usize>) 
    ensures
        final(v).len() == old(v).len(),
        forall |i| 0 <= i < final(v).len() ==> final(v)[i] == 0,
{
    for x in it: v.iter_mut()
        invariant
            after_borrow(v)@.len() == it.seq().len(),
            forall |i: int| #![auto] 0 <= i < it.seq().len() ==> *final(it.seq()[i]) == after_borrow(v)@[i],
            forall |i: int| #![auto] 0 <= i < it.index() ==> *final(it.seq()[i]) == 0,
    {
        *x = 0;
    }
}

// Their table (and function name) misnames this skip_take, but the discussion text says take_skip
// and the code computes take(n).skip(n)
// https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/examples/iterators/03_std_iterators.rs#L35
fn take_skip<I: Iterator>(v: Vec<u32>, n: usize)
    requires
        n <= v.len(),
{
    // Creusot:
    //   assert!(iter.take(n).skip(n).next().is_none())
    // Verus:
    let out = v.into_iter().take(n).skip(n).next();
    assert(out is None);
}

// TODO: Their counter client uses a closure that captures a mutable reference, which Verus does not
// yet support
// https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/examples/iterators/03_std_iterators.rs#L41
/*
    pub fn counter(v: Vec<u32>) {
        let mut cnt: usize = 0;

        let x: Vec<u32> = v
            .iter()
            .map_inv(|x, _prod| {
                proof_assert!(cnt@ == _prod.len());
                cnt += 1;
                *x
            })
            .collect();

        proof_assert! { x@.len() == v@.len() };
        proof_assert! { x@.ext_eq(v@) };
        proof_assert! { cnt@ == x@.len() };
    }
*/

// I think the corresponds to their eval of `concat_vec`:
// https://github.com/creusot-rs/creusot/blob/bef58f6aa7493ac8c8012164a8eeab462c346d1a/examples/iterators/08_collect_extend.rs#L20
fn extend<T, I: Iterator<Item = T> + IteratorSpec<Item = T>>(vec: &mut Vec<T>, iter: I) 
    requires
        iter.obeys_prophetic_iter_laws(),
        iter.decrease() is Some,
        iter.will_return_none(),
        iter.initial_value_relation(&iter),
    ensures
        final(vec)@ == old(vec)@ + iter.remaining(),
        iter.will_return_none(),
{
    let ghost old_vec = vec;
    for x in it: iter 
        invariant
            it.iter.obeys_prophetic_iter_laws(),
            vec@ =~= old_vec@ + it.history(),
    {
        vec.push(x);
    }
}

// The Creusot repo doesn't have anything named `decuple_range`.  I think this matches the text
// description, however: 
// "The example decuple_range maps a Range, multiplying elements by 10, collecting the results 
// into a vector and verifying functional correctness
fn decuple_range() {
    let f = |x: u32| -> (y: u32) requires x < 10, ensures y == x * 10 { x * 10 };
    let v: Vec<u32> = (0..10).map(f).collect();
    assert(v@ == seq![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
}

// See knights_tour.rs and hillel.rs for the corresponding ports


////////////////////////////////////////////////////////////
//
//    Prusti Examples
//
////////////////////////////////////////////////////////////

// I did not find any mention of iterators in the main Prusti repo:
//   https://github.com/viperproject/prusti-dev
// Nor did any of the branches seem to have iterator-related names

// Best guess is that `counter` is just a Range that starts at 0

fn counter()
{
    let mut v = vec![];
    for i in iter: 0..4
        invariant
            v.len() == iter.index(),
            forall |i| 0 <= i < iter.index() ==> v[i] == i,
    {
        v.push(i);
    }
    assert(v@ == seq![0, 1, 2, 3]);
}


// Best guess is that `double` is just a map of: |x| 2*x
fn double() {
    let f = |x: u32| -> (y: u32) requires x < 10, ensures y == x * 2 { x * 2 };
    let v: Vec<u32> = (0..3).map(f).collect();
    assert(v@ == seq![0, 2, 4]);
}


fn filter_test() {
    let p = |x: &u32| -> (b: bool)
        ensures b == (*x % 2 == 0)
    { *x % 2 == 0 };

    let v: Vec<u32> = vec![1, 2, 3, 4];
    let mut w: Vec<u32> = Vec::new();

    for x in it: v.into_iter().filter(p)
        invariant
            w.len() == it.index(),
            forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
    {
        w.push(x);
    }
    assert(w.len() <= 4);
    assert(forall |i| 0 <= i < w.len() ==> w[i] % 2 == 0);
    assert(forall |i| #![auto] 0 <= i < w.len() ==> v@.contains(w[i]));
}

// Unclear what the map test is meant to evaluate, so here's a simple example
fn map() {
    let f = |x: &u32| -> (y: u32) requires *x < 10, ensures y == x * 3 { *x * 3 };
    let v = vec![1u32, 2, 3, 4];
    let mut w = Vec::new();
    for x in iter: v.iter().map(f)
        invariant
            w.len() == iter.index(),
            forall |i| 0 <= i < w.len() ==> w[i] == iter.seq()[i],
    {
        w.push(x);
    }
    assert(w@ == seq![3u32, 6, 9, 12]);
}

// Unclear what the original client did
fn option_into_iter() {
    broadcast use vstd::std_specs::option::axiom_spec_into_iter;
    let o = Some(5u32);
    let v: Vec<u32> = o.into_iter().collect();
    assert(v@ == seq![5]);
}

// Unclear what the original client did
fn vec_into_iter() {
    let v: Vec<u32> = vec![1, 2, 3, 4];
    let w: Vec<u32> = v.into_iter().collect();
    assert(v@ == w@);
    let x: Vec<u32> = w.into_iter().rev().collect();
    assert(x@ == seq![4u32, 3, 2, 1]);

    let y: Vec<u32> = vec![1, 2, 3, 4];
    let z: Vec<u32> = y.into_iter().rev().rev().collect();
    assert(z@ == y@);
}


// Unclear what the original client did
fn zip() {
    let w = vec![1u32, 2, 3];
    let x = vec![2u32, 4, 6];
    let y = vec![1u32, 2];
    let z = vec![2u32, 4, 6, 8, 10];

    let wx: Vec<(&u32, &u32)> = zip_iterators(w.iter(), x.iter()).collect();
    assert(wx@.unref() == seq![(1u32,2u32), (2, 4), (3, 6)]);

    let xy: Vec<(&u32, &u32)> = zip_iterators(x.iter(), y.iter()).collect();
    assert(xy@.unref() == seq![(2u32,1u32), (4, 2)]);

    let yz: Vec<(&u32, &u32)> = zip_iterators(y.iter(), z.iter()).collect();
    assert(yz@.unref() == seq![(1u32,2u32), (2, 4)]);
}

}

fn main() {}
