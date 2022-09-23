#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use pervasive::seq::*;

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

// ANCHOR: quants_recursion
spec fn all_evens(s: Seq<int>) -> bool
    decreases s.len()
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
    assert(is_even(s[3])); // triggers is_even(s[3])
    assert(s[3] % 2 == 0); // succeeds, because previous line already instantiated the forall
}
// ANCHOR_END: test_use_forall_succeeds1

// ANCHOR: test_use_forall_succeeds2
proof fn test_use_forall_succeeds2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> is_even(#[trigger] s[i]),
{
    assert(s[3] % 2 == 0); // succeeds by triggering s[3]
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
        forall|i: int| #![auto] 0 <= i < s.len() ==> is_even(s[i]), // Verus chooses s[i] as the trigger
{
    assert(s[3] % 2 == 0); // succeeds by triggering s[3]
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
        forall|i: int, j: int|
            0 <= i < j < s.len() ==> #[trigger] is_distinct(s[i], s[j]),
{
    assert(is_distinct(s[4], s[2]));
}
// ANCHOR_END: test_distinct1

// ANCHOR: test_distinct2
proof fn test_distinct2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int|
            0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j],
{
    assert(s[4] != s[2]);
}
// ANCHOR_END: test_distinct2

// ANCHOR: test_distinct3
proof fn test_distinct3(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| #![trigger s[i], s[j]]
            0 <= i < j < s.len() ==> s[i] != s[j],
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
            0 <= i < j < a.len() ==> a[i] != b[j] && a[i] != c[j]
{
    assert(a[2] != c[4]); // succeeds, matches a[i], c[j]
}
// ANCHOR_END: test_multitriggers

// ANCHOR: seq_update_different
proof fn seq_update_different<A>(s: Seq<A>, i: int, j: int, a: A) {
    assert(forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, a)[i] === s[i]
    );
}
// ANCHOR_END: seq_update_different

// ANCHOR: test_sorted_good
proof fn test_sorted_good(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int|
            0 <= i <= j < s.len() ==> s[i] <= s[j],
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

fn main() {
}

} // verus!
