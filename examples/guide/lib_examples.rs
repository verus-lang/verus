#![allow(unused_imports)]
use vstd::{map::*, prelude::*, seq::*, set::*};

verus! {

// ANCHOR: macro
proof fn test_seq1() {
    let s: Seq<int> = seq![0, 10, 20, 30, 40];
    assert(s.len() == 5);
    assert(s[2] == 20);
    assert(s[3] == 30);
}

proof fn test_set1() {
    let s: Set<int> = set![0, 10, 20, 30, 40];
    assert(s.finite());
    assert(s.contains(20));
    assert(s.contains(30));
    assert(!s.contains(60));
}

proof fn test_map1() {
    let m: Map<int, int> = map![0 => 0, 10 => 100, 20 => 200, 30 => 300, 40 => 400];
    assert(m.dom().contains(20));
    assert(m.dom().contains(30));
    assert(!m.dom().contains(60));
    assert(m[20] == 200);
    assert(m[30] == 300);
}

// ANCHOR_END: macro
#[verusfmt::skip]
mod m0 {
use vstd::{seq::*, prelude::*};

// ANCHOR: new0
proof fn test_seq2() {
    let s: Seq<int> = Seq::new(5, |i: int| 10 * i);
    assert(s.len() == 5);
    assert(s[2] == 20);
    assert(s[3] == 30);
}
// ANCHOR_END: new0
}

// ANCHOR: new
proof fn test_seq2() {
    let s: Seq<int> = Seq::new(5, |i: int| 10 * i);
    assert(s.len() == 5);
    assert(s[2] == 20);
    assert(s[3] == 30);
}

proof fn test_set2() {
    let s: Set<int> = Set::new(|i: int| 0 <= i <= 40 && i % 10 == 0);
    assert(s.contains(20));
    assert(s.contains(30));
    assert(!s.contains(60));

    let s_infinite: Set<int> = Set::new(|i: int| i % 10 == 0);
    assert(s_infinite.contains(20));
    assert(s_infinite.contains(30));
    assert(!s_infinite.contains(35));
}

proof fn test_map2() {
    let m: Map<int, int> = Map::new(|i: int| 0 <= i <= 40 && i % 10 == 0, |i: int| 10 * i);
    assert(m[20] == 200);
    assert(m[30] == 300);

    let m_infinite: Map<int, int> = Map::new(|i: int| i % 10 == 0, |i: int| 10 * i);
    assert(m_infinite[20] == 200);
    assert(m_infinite[30] == 300);
    assert(m_infinite[90] == 900);
}
// ANCHOR_END: new

/*
// ANCHOR: test_eq_fail
proof fn test_eq_fail() {
    let s1: Seq<int> = seq![0, 10, 20, 30, 40];
    let s2: Seq<int> = seq![0, 10] + seq![20] + seq![30, 40];
    let s3: Seq<int> = Seq::new(5, |i: int| 10 * i);
    assert(s1 === s2); // FAILS, even though it's true
    assert(s1 === s3); // FAILS, even though it's true
}
// ANCHOR_END: test_eq_fail
*/

// ANCHOR: test_eq
proof fn test_eq() {
    let s1: Seq<int> = seq![0, 10, 20, 30, 40];
    let s2: Seq<int> = seq![0, 10] + seq![20] + seq![30, 40];
    let s3: Seq<int> = Seq::new(5, |i: int| 10 * i);
    assert(s1 =~= s2);
    assert(s1 =~= s3);
    assert(s1 === s2);  // succeeds
    assert(s1 === s3);  // succeeds
}
// ANCHOR_END: test_eq

/*
// ANCHOR: lemma_len_intersect_fail
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {

    } else {
        let a = s1.choose();

        lemma_len_intersect(s1.remove(a), s2);
    }
}
// ANCHOR_END: lemma_len_intersect_fail

// ANCHOR: lemma_len_intersect_sketch
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        // s1 is the empty set.
        // Therefore, s1.intersect(s2) is also empty.
        // So both s1.len() and s1.intersect(s2).len() are 0,
        // and 0 <= 0.
    } else {
        // s1 is not empty, so it has at least one element.
        // Let a be an element from s1.
        // Let s1' be the set s1 with the element a removed (i.e. s1' == s1 - {a}).
        // Removing an element decreases the cardinality by 1, so s1'.len() == s1.len() - 1.
        // By induction, s1'.intersect(s2).len() <= s1'.len(), so:
        //   (s1 - {a}).intersect(s2).len() <= s1'.len()
        //   (s1.intersect(s2) - {a}).len() <= s1'.len()
        //   (s1.intersect(s2) - {a}).len() <= s1.len() - 1
        // case a in s1.intersect(s2):
        //   (s1.intersect(s2) - {a}).len() == s1.intersect(s2).len() - 1
        // case a not in s1.intersect(s2):
        //   (s1.intersect(s2) - {a}).len() == s1.intersect(s2).len()
        // In either case:
        //   s1.intersect(s2).len() <= (s1.intersect(s2) - {a}).len() + 1
        // Putting all the inequalities together:
        //   s1.intersect(s2).len() <= (s1.intersect(s2) - {a}).len() + 1 <= (s1.len() - 1) + 1
        // So:
        //   s1.intersect(s2).len() <= (s1.len() - 1) + 1
        //   s1.intersect(s2).len() <= s1.len()
    }
}
// ANCHOR_END: lemma_len_intersect_sketch

// ANCHOR: lemma_len_intersect
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        lemma_len_intersect(s1.remove(a), s2);
    }
}
// ANCHOR_END: lemma_len_intersect
*/

// ANCHOR: lemma_len_intersect_commented
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2).len() == 0) by {
            assert(s1.intersect(s2) =~= s1);
        }
    } else {
        let a = s1.choose();
        lemma_len_intersect(s1.remove(a), s2);
        // by induction: s1.remove(a).intersect(s2).len() <= s1.remove(a).len()
        assert(s1.intersect(s2).remove(a).len() <= s1.remove(a).len()) by {
            assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        }
        // simplifying ".remove(a).len()" yields s1.intersect(s2).len() <= s1.len())

    }
}
// ANCHOR_END: lemma_len_intersect_commented

// ANCHOR: test_vec1
fn test_vec1() {
    let mut v: Vec<u32> = Vec::new();
    v.push(0);
    v.push(10);
    v.push(20);
    v.push(30);
    v.push(40);
    assert(v.len() == 5);
    assert(v[2] == 20);
    assert(v[3] == 30);
    v.set(2, 21);
    assert(v[2] == 21);
    assert(v[3] == 30);
}
// ANCHOR_END: test_vec1

// ANCHOR: test_vec2
spec fn has_five_sorted_numbers(s: Seq<u32>) -> bool {
    s.len() == 5 && s[0] <= s[1] <= s[2] <= s[3] <= s[4]
}

fn test_vec2() {
    let mut v: Vec<u32> = Vec::new();
    v.push(0);
    v.push(10);
    v.push(20);
    v.push(30);
    v.push(40);
    v.set(2, 21);
    assert(v@ =~= seq![0, 10, 21, 30, 40]);
    assert(v@ =~= seq![0, 10] + seq![21] + seq![30, 40]);
    assert(v@[2] == 21);
    assert(v@[3] == 30);
    assert(v@.subrange(2, 4) =~= seq![21, 30]);
    assert(has_five_sorted_numbers(v@));
}
// ANCHOR_END: test_vec2

// ANCHOR: ret_spec_fn
spec fn adder(x: int) -> spec_fn(int) -> int {
    |y: int| x + y
}

proof fn test_adder() {
    let f = adder(10);
    assert(f(20) == 30);
    assert(f(60) == 70);
}
// ANCHOR_END: ret_spec_fn

fn main() {
}

} // verus!
