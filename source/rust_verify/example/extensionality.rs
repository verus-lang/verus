#![allow(unused_imports)]

use builtin::*;
mod pervasive;
use crate::pervasive::{*, map::*, seq::*, set::*, seq_lib::*, set_lib::*};

// Sequence extensionality

#[proof]
fn test_seqs(s1: Seq<u64>, s2: Seq<u64>) {
    requires([
        s1.len() == 3,
        s1.index(0) == 0,
        s1.index(1) == 4,
        s1.index(2) == 8,
        s2.len() == 3,
        s2.index(0) == 0,
        s2.index(1) == 4,
        s2.index(2) == 8,
    ]);

    assert_seqs_equal!(s1, s2);

    assert(equal(s1, s2));
}

#[proof]
fn pop_and_push(s: Seq<u64>) {
    requires([
        s.len() >= 1,
    ]);

    let t = s.subrange(0, s.len() as int - 1).push(s.index(s.len() as int - 1));

    assert_seqs_equal!(s, t);

    assert(equal(s, t));
}

#[proof]
fn subrange_concat(s: Seq<u64>, i: int) {
    requires([
        0 <= i && i <= s.len(),
    ]);

    let t1 = s.subrange(0, i);
    let t2 = s.subrange(i, s.len());
    let t = t1.add(t2);

    assert_seqs_equal!(s, t);

    assert(equal(s, t));
}

#[spec]
fn are_equal(s: Seq<u64>, t: Seq<u64>, i: int) -> bool {
    s.index(i) == t.index(i)
}

#[proof]
fn assert_seqs_equal_with_proof(s: Seq<u64>, t: Seq<u64>) {
    requires([
        s.len() == t.len(),
        forall(|i| 0 <= i && i < s.len() as int >>= are_equal(s, t, i))
    ]);

    assert_seqs_equal!(s, t, i => {
        assert(are_equal(s, t, i)); // trigger
    });

    assert(equal(s, t));
}

// Map extensionality

#[proof]
fn test_map(m: Map<int, int>) {
    requires([
        m.contains_pair(5, 17)
    ]);

    let q = m.remove(5).insert(5, 17);

    assert_maps_equal!(m, q);

    assert(equal(m, q));
}

#[spec]
fn maps_are_equal_on(m: Map<int, int>, q: Map<int, int>, i: int) -> bool {
    m.dom().contains(i) && q.dom().contains(i) &&
    m.index(i) == q.index(i)
}

#[proof]
fn assert_maps_equal_with_proof(m: Map<int, int>, q: Map<int, int>) {
    requires(
        forall(|i| maps_are_equal_on(m, q, i))
    );

    assert_maps_equal!(m, q, i => {
        assert(maps_are_equal_on(m, q, i)); // trigger
    });

    assert(equal(m, q));
}

#[proof]
fn assert_maps_equal_with_proof2() {
    let m = Map::<u64, u64>::total(|t| t & 184);
    let q = Map::<u64, u64>::new(|t| t ^ t == 0, |t| 184 & t);

    assert_maps_equal!(m, q, t => {
        // show that the `q` map is total:
        assert_bit_vector(t ^ t == 0); 

        // show that the values are equal:
        assert_bit_vector(t & 184 == 184 & t);
    });

    assert(equal(m, q));
}

// Set extensionality

#[proof]
fn test_set(s: Set<int>, t: Set<int>) {
    assert_sets_equal!(
        s.union(t),
        t.union(s),
    );

    assert(equal(
        s.union(t),
        t.union(s),
    ));
}

#[proof]
fn assert_sets_equal_with_proof() {
    let s = Set::<u64>::new(|i: u64| i ^ 25 < 100);
    let t = Set::<u64>::new(|i: u64| 25 ^ i < 100);

    assert_sets_equal!(s, t, i => {
        assert_bit_vector(i ^ 25 == 25 ^ i);
    });

    assert(equal(s, t));
}

fn main() {
}
