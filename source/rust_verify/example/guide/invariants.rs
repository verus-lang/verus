#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: fib_spec
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib((n - 2) as nat) + fib((n - 1) as nat)
    }
}
// ANCHOR_END: fib_spec

// ANCHOR: fib_is_mono
proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
    decreases j - i,
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        assert(fib(j) == fib((j - 2) as nat) + fib((j - 1) as nat));
    } else {
        lemma_fib_is_monotonic(i, (j - 1) as nat);
        lemma_fib_is_monotonic(i, (j - 2) as nat);
    }
}
// ANCHOR_END: fib_is_mono

/*
// ANCHOR: fib_impl_no_proof
fn fib_impl(n: u64) -> (result: u64)
    requires
        fib(n as nat) <= 0xffff_ffff_ffff_ffff
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
    {
        i = i + 1;
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
// ANCHOR_END: fib_impl_no_proof
*/

/*
// ANCHOR: fib_mono_no_proof
proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
{
}
// ANCHOR_END: fib_mono_no_proof
*/

/*
// ANCHOR: fib_mono_skeleton
proof fn lemma_fib_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        assume(false);
    } else {
        assume(false);
    }

}
// ANCHOR_END: fib_mono_skeleton
*/

// ANCHOR: fib_final
fn fib_impl(n: u64) -> (result: u64)
    requires
        fib(n as nat) <= 0xffff_ffff_ffff_ffff
    ensures
        result == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            fib(n as nat) <= 0xffff_ffff_ffff_ffff,
            cur == fib(i as nat),
            prev == fib((i - 1) as nat),
    {
        i = i + 1;
        proof {
            lemma_fib_is_monotonic(i as nat, n as nat);
        }
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}
// ANCHOR_END: fib_final


// ANCHOR: bank_spec
spec fn always_non_negative(s: Seq<i64>) -> bool
{
    forall|i: int| 0 <= i <= s.len() ==> sum(#[trigger] s.take(i)) >= 0    
}

spec fn sum(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.drop_last()) + s.last()
    }
}
// ANCHOR_END: bank_spec

/*
// ANCHOR: bank_no_proof
fn non_negative(operations: &[i64]) -> (r: bool)
    ensures
        r == always_non_negative(operations@),
{
    let mut s = 0i128;
    for i in 0usize..operations.len()
    {
        s = s + operations[i] as i128;
        if s < 0 {
            return false;
        }
    }
    true
}
// ANCHOR_END: bank_no_proof
*/

// ANCHOR: bank_final
fn non_negative(operations: &[i64]) -> (r: bool)
    ensures
        r == always_non_negative(operations@),
{
    let mut s = 0i128;
    for i in 0usize..operations.len()
        invariant
            s == sum(operations@.take(i as int)),
            forall|j: int| 0 <= j <= i ==> sum(#[trigger] operations@.take(j)) >= 0,
            i64::MIN <= s <= i64::MAX * i,
    {
        assert(operations@.take(i as int) =~= operations@.take(
            (i + 1) as int,
        ).drop_last());
        s = s + operations[i] as i128;
        if s < 0 {
            return false;
        }
    }
    true
}
// ANCHOR_END: bank_final


fn main() {
}

} // verus!

