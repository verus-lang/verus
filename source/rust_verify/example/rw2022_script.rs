fn main() {}

// ## 11 -- 10-program.rs

#[allow(unused_imports)]
use {builtin::*, builtin_macros::*, prelude::*, seq::*, vstd::*};

verus! {

// ## A -- A-program.rs
fn max(a: u64, b: u64) -> (ret: u64)
    ensures
        ret == a || ret == b,
        ret >= a && ret >= b,
{
    if a >= b {
        a
    } else {
        b
    }
}

fn max_test2() {
    let x = 3;
    let y = 4;
    let ret = max(x, y);
    assert(ret == 4);
}

// ## B -- B-program.rs
fn main_1() {
    let x = 3;
    let y = 4;
    assert(x != y);
}

// ## B -- B-program.rs.smt sat
// ## C -- C-prime.rs
spec fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

spec fn is_prime(candidate: nat) -> bool {
    &&& 1 < candidate
    &&& forall|factor: nat| 1 < factor && factor < candidate ==> !divides(factor, candidate)
}

fn test_prime(candidate: u64) -> (result: bool)
    requires
        1 < candidate,
    ensures
        result == is_prime(candidate as nat),
{
    let mut factor: u64 = 2;
    while factor < candidate
        invariant
            1 < factor <= candidate,
            forall|smallerfactor: nat|
                1 < smallerfactor < factor ==> !divides(smallerfactor, candidate as nat),
    {
        if candidate % factor == 0 {
            assert(divides(factor as nat, candidate as nat));
            assert(!is_prime(candidate as nat));
            return false;
        }
        factor = factor + 1;
    }
    true
}

fn assertions() {
    assert(divides(3, 6));
    assert(divides(12, 24));
    assert(is_prime(2));
    assert(is_prime(3));
    assert(!divides(4, 5));
    assert(is_prime(5));
}

// ## D -- D-fibo.rs
spec fn fibo(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibo((n - 2) as nat) + fibo((n - 1) as nat)
    }
}

proof fn lemma_fibo_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i,
{
    // ----
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        reveal_with_fuel(fibo, 2);
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
        lemma_fibo_is_monotonic(i, (j - 2) as nat);
    }
}

// ## D/2 -- D-fibo.rs
spec fn fibo_fits_u64(n: nat) -> bool {
    fibo(n) <= 0xffff_ffff_ffff_ffff
}

exec fn fibo_impl(n: u64) -> (result: u64)
    requires
        fibo_fits_u64(n as nat),
    ensures
        result == fibo(n as nat),
{
    // ----
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    let mut i: u64 = 1;
    while i < n
        invariant
            0 < i <= n,
            fibo_fits_u64(n as nat),
            fibo_fits_u64(i as nat),
            cur == fibo(i as nat),
            prev == fibo((i - 1) as nat),
    {
        i = i + 1;
        proof {
            lemma_fibo_is_monotonic(i as nat, n as nat);
        }
        let new_cur = cur + prev;
        prev = cur;
        cur = new_cur;
    }
    cur
}

// ## E -- E-reverse.rs -- spec variables
/* See vectors.rs
fn reverse(v: &mut Vec<u64>) {
    ensures([
        v.len() == old(v).len(),
        forall(|i: int| 0 <= i && i < old(v).len()
               >>= v.index(i) == old(v).index(old(v).len() - i - 1)),
    ]);

    let length = v.len();
    #[verifier::spec] let v1 = *v;
    let mut n: usize = 0;
    while n < length / 2 {
        invariant([
            length == v.len(),
            forall(|i: int| n <= i && i + n < length >>= v.index(i) == v1.index(i)),
            forall(|i: int| 0 <= i && i < n >>= v.index(i) == v1.index(length - i - 1)),
            forall(|i: int| 0 <= i && i < n >>= v1.index(i) == v.index(length - i - 1)),
        ]);

        let x = *v.index(n);
        let y = *v.index(length - 1 - n);
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}
*/

// F -- F-linear-proof
// cell::RefCell::Cell<X>
// G -- G-bitvector.rs
fn mod8_bw(x: u32) -> (ret: u32)
    ensures
        ret == x % 8,
{
    assert(x & 7 == x % 8) by (bit_vector);
    x & 7
}

} // verus!
