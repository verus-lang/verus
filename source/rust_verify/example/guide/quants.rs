#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*};

verus! {

// ANCHOR: quants_finite
spec fn is_even(i: int) -> bool {
    i % 2 == 0
}

proof fn test_seq_5_is_evens(s: Seq<int>)
    requires
        s.len() == 5,
        is_even(s[0]),
        is_even(s[1]),
        is_even(s[3]),
        is_even(s[3]),
        is_even(s[4]),
{
    assert(is_even(s[3]));
}
// ANCHOR_END: quants_finite

spec fn is_odd(i: int) -> bool {
    i % 2 == 1
}

// ANCHOR: quants_recursion
spec fn all_evens(s: Seq<int>) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        is_even(s.last()) && all_evens(s.drop_last())
    }
}

proof fn test_seq_recursive(s: Seq<int>)
    requires
        s.len() == 5,
        all_evens(s),
{
    assert(is_even(s[3])) by {
        reveal_with_fuel(all_evens, 2);
    }
}
// ANCHOR_END: quants_recursion

// ANCHOR: quants_use_forall
proof fn test_use_forall(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] is_even(s[i]),
{
    assert(is_even(s[3]));
}
// ANCHOR_END: quants_use_forall

/*
// ANCHOR: trigger_fails
spec fn is_even(i: int) -> bool {
    i % 2 == 0
}

proof fn test_use_forall_fail(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] is_even(s[i]),
{
    assert(s[3] % 2 == 0); // FAILS: doesn't trigger is_even(s[i])
}
// ANCHOR_END: trigger_fails
*/

// ANCHOR: test_use_forall_succeeds1
proof fn test_use_forall_succeeds1(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] is_even(s[i]),
{
    assert(is_even(s[3]));  // triggers is_even(s[3])
    assert(s[3] % 2 == 0);  // succeeds, because previous line already instantiated the forall
}
// ANCHOR_END: test_use_forall_succeeds1

// ANCHOR: test_use_forall_succeeds2
proof fn test_use_forall_succeeds2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> is_even(#[trigger] s[i]),
{
    assert(s[3] % 2 == 0);  // succeeds by triggering s[3]
}
// ANCHOR_END: test_use_forall_succeeds2

/*
// ANCHOR: test_use_forall_succeeds3
proof fn test_use_forall_succeeds3(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> is_even(s[i]), // Verus chooses s[i] as the trigger and prints a note
{
    assert(s[3] % 2 == 0); // succeeds by triggering s[3]
}
// ANCHOR_END: test_use_forall_succeeds3
*/

// ANCHOR: test_use_forall_succeeds4
proof fn test_use_forall_succeeds4(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int|
            #![auto]
            0 <= i < s.len() ==> is_even(s[i]),  // Verus chooses s[i] as the trigger
{
    assert(s[3] % 2 == 0);  // succeeds by triggering s[3]
}
// ANCHOR_END: test_use_forall_succeeds4

/*
// ANCHOR: test_use_forall_bad1
proof fn test_use_forall_bad1(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| (#[trigger](0 <= i)) && i < s.len() ==> is_even(s[i]),
{
    assert(s[3] % 2 == 0);
}
// ANCHOR_END: test_use_forall_bad1
*/

/*
// ANCHOR: test_use_forall_bad2
spec fn nonnegative(i: int) -> bool {
    0 <= i
}

proof fn test_use_forall_bad2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| #[trigger] nonnegative(i) && i < s.len() ==> is_even(s[i]),
{
    assert(is_even(s[3])); // FAILS: doesn't trigger nonnegative(i)
}
// ANCHOR_END: test_use_forall_bad2
*/

// ANCHOR: test_distinct1
spec fn is_distinct(x: int, y: int) -> bool {
    x != y
}

proof fn test_distinct1(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] is_distinct(s[i], s[j]),
{
    assert(is_distinct(s[2], s[4]));
}
// ANCHOR_END: test_distinct1

// ANCHOR: test_distinct2
proof fn test_distinct2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j],
{
    assert(s[4] != s[2]);
}
// ANCHOR_END: test_distinct2

// ANCHOR: test_distinct3
proof fn test_distinct3(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==> s[i] != s[j],
{
    assert(s[4] != s[2]);
}
// ANCHOR_END: test_distinct3

/*
// ANCHOR: test_distinct_fail1
proof fn test_distinct_fail1(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int|
            0 <= i < j < s.len() ==> s[i] != #[trigger] s[j], // error: trigger fails to mention i
{
    assert(s[4] != s[2]);
}
// ANCHOR_END: test_distinct_fail1
*/

/*
// ANCHOR: test_distinct_fail2
proof fn test_distinct_fail2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| #![trigger s[i], s[j], is_even(i)]
            0 <= i < j < s.len() ==> s[i] != s[j],
{
    assert(s[4] != s[2]); // FAILS, because nothing matches is_even(i)
}
// ANCHOR_END: test_distinct_fail2
*/

// ANCHOR: test_distinct4
proof fn test_distinct4(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int|
            #![trigger s[i], s[j]]
            #![trigger is_even(i), is_even(j)]
            0 <= i < j < s.len() ==> s[i] != s[j],
{
    assert(s[4] != s[2]);
}
// ANCHOR_END: test_distinct4

// ANCHOR: test_multitriggers
proof fn test_multitriggers(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        5 <= a.len(),
        a.len() == b.len(),
        a.len() == c.len(),
        forall|i: int, j: int|
            #![trigger a[i], b[j]]
            #![trigger a[i], c[j]]
            0 <= i < j < a.len() ==> a[i] != b[j] && a[i] != c[j],
{
    assert(a[2] != c[4]);  // succeeds, matches a[i], c[j]
}
// ANCHOR_END: test_multitriggers

// ANCHOR: seq_update_different
proof fn seq_update_different<A>(s: Seq<A>, i: int, j: int, a: A) {
    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, a)[i] == s[i]);
}
// ANCHOR_END: seq_update_different

// ANCHOR: test_sorted_good
proof fn test_sorted_good(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j],
{
    assert(s[2] <= s[4]);
}
// ANCHOR_END: test_sorted_good

/*
// ANCHOR: test_sorted_bad1
proof fn test_sorted_bad(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int|
            0 <= i < s.len() - 1 ==> s[i] <= s[i + 1],
{
    assert(s[2] <= s[4]);
}
// ANCHOR_END: test_sorted_bad1
*/

// ANCHOR: test_exists_succeeds
proof fn test_exists_succeeds() {
    assert(is_even(4));
    assert(!is_even(5));
    assert(is_even(6));
    assert(exists|i: int| #[trigger] is_even(i));  // succeeds with witness i = 4 or i = 6
}
// ANCHOR_END: test_exists_succeeds

/*
// ANCHOR: test_exists_fails
proof fn test_exists_fails() {
    assert(exists|i: int| #[trigger] is_even(i)); // FAILS, no match for trigger
}
// ANCHOR_END: test_exists_fails
*/

// ANCHOR: test_choose_succeeds
spec fn f(i: int) -> bool;

proof fn test_choose_succeeds()
    requires
        exists|i: int| f(i),
{
    let i_witness = choose|i: int| f(i);
    assert(f(i_witness));
}
// ANCHOR_END: test_choose_succeeds

/*
// ANCHOR: test_choose_fails
proof fn test_choose_fails() {
    let i_witness = choose|i: int| f(i);
    assert(i_witness < 0 || i_witness >= 0); // i_witness is some integer
    assert(f(i_witness)); // FAILS because we don't know exists|i: int| f(i)
}
// ANCHOR_END: test_choose_fails
*/

// ANCHOR: test_choose_same
proof fn test_choose_same() {
    let x = choose|i: int| f(i);
    let y = choose|i: int| f(i);
    assert(x == y);
}
// ANCHOR_END: test_choose_same

// ANCHOR: test_choose_succeeds2
spec fn less_than(x: int, y: int) -> bool {
    x < y
}

proof fn test_choose_succeeds2() {
    assert(less_than(3, 7));  // promote i = 3, i = 7 as a witness
    let (x, y) = choose|i: int, j: int| less_than(i, j);
    assert(x < y);
}
// ANCHOR_END: test_choose_succeeds2

#[verusfmt::skip]
mod M {
#[allow(unused_imports)]

use builtin::*;

// ANCHOR: just_works
spec fn is_distinct(x: int, y: int) -> bool {
    x != y
}

spec fn dummy(i: int) -> bool;

proof fn prove_forall()
    ensures
        forall|i: int, j: int|
            #![trigger dummy(i), dummy(j)]
            is_distinct(i, j) ==> is_distinct(j, i),
{
    // proving the forall just works; the trigger is irrelevant
}

proof fn use_exists(x: int)
    requires
        exists|i: int| #![trigger dummy(i)] x == i + 1 && is_distinct(i, 5),
{
    // using the exists just works; the trigger is irrelevant
    assert(x != 6);
}
// ANCHOR_END: just_works
}

// ANCHOR: hoist
proof fn hoisted_forall(i: int, j: int)
    ensures
        is_distinct(i, j) ==> is_distinct(j, i),
{
}

proof fn hosted_exists(x: int, i: int)
    requires
        x == i + 1 && is_distinct(i, 5),
{
    assert(x != 6);
}
// ANCHOR_END: hoist

#[verifier::external_body]
proof fn lemma_even_f(i: int)
    requires
        is_even(i),
    ensures
        f(i),
{
}

/*
// ANCHOR: test_even_f_fail1
proof fn test_even_f()
    ensures
        forall|i: int| is_even(i) ==> f(i), // FAILS because we don't call the lemma
{
}
// ANCHOR_END: test_even_f_fail1
*/

/*
// ANCHOR: test_even_f_fail2
proof fn test_even_f()
    ensures
        forall|i: int| is_even(i) ==> f(i),
{
    lemma_even_f(i); // ERROR: i is not in scope here
}
// ANCHOR_END: test_even_f_fail2
*/

// ANCHOR: test_even_f
proof fn test_even_f()
    ensures
        forall|i: int| is_even(i) ==> f(i),
{
    assert forall|i: int| is_even(i) implies f(i) by {
        // First, i is in scope here
        // Second, we assume is_even(i) here
        lemma_even_f(i);
        // Finally, we have to prove f(i) here
    }
}
// ANCHOR_END: test_even_f

spec fn g(i: int, j: int) -> bool;

#[verifier::external_body]
proof fn lemma_g_proves_f(i: int, j: int)
    requires
        g(i, j),
    ensures
        f(i),
{
}

/*
// ANCHOR: test_g_proves_f_fails
proof fn test_g_proves_f(i: int)
    requires
        exists|j: int| g(i, j),
    ensures
        f(i),
{
    lemma_g_proves_f(i, j); // ERROR: j is not in scope here
}
// ANCHOR_END: test_g_proves_f_fails
*/

// ANCHOR: test_g_proves_f
proof fn test_g_proves_f(i: int)
    requires
        exists|j: int| g(i, j),
    ensures
        f(i),
{
    lemma_g_proves_f(i, choose|j: int| g(i, j));
}
// ANCHOR_END: test_g_proves_f

// ANCHOR: binary_search
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}

fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(0);
    v.push(10);
    v.push(20);
    v.push(30);
    v.push(40);
    assert(v[3] == 30);  // needed to trigger exists|i: int| ... k == v[i]
    let r = binary_search(&v, 30);
    assert(r == 3);
}
// ANCHOR_END: binary_search

} // verus!
