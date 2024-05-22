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
    //-   if a >= b { b } else { a }
    /*+*/
    if a >= b {
        a
    } else {
        b
    }
}

// ;; Function-Def crate::max
// (push)
//  (declare-const ret~10@ Int)
//  (declare-const a~2@ Int)
//  (declare-const b~4@ Int)
//  (assert fuel_defaults)
//  (assert (uInv 64 a~2@))
//  (assert (uInv 64 b~4@))
//  ;; postcondition not satisfied
//  (declare-const %%location_label%%0 Bool)
//  ;; postcondition not satisfied
//  (declare-const %%location_label%%1 Bool)
//  (declare-const %%query%% Bool)
//  (assert
//   (=>
//    %%query%%
//    (not (=>
//      (= ret~10@ (ite
//        (>= a~2@ b~4@)
//        a~2@
//        b~4@
//      ))
//      (and
//       (=>
//        %%location_label%%0
//        (or
//         (= ret~10@ a~2@)
//         (= ret~10@ b~4@)
//       ))
//       (=>
//        %%location_label%%1
//        (and
//         (>= ret~10@ a~2@)
//         (>= ret~10@ b~4@)
//  )))))))
//  (assert %%query%%)
//  (set-option :rlimit 30000000)
//  (check-sat)
//  (set-option :rlimit 0)
// (pop)
// ## B -- B-fibo.rs
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

spec fn fibo_fits_u64(n: nat) -> bool {
    fibo(n) <= 0xffff_ffff_ffff_ffff
}

exec fn fibo_impl(n: u64) -> (result: u64)
    requires
        fibo_fits_u64(n as nat),
    ensures
        result == fibo(n as nat),
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

// ## C -- C-linearity.rs
//-  exec fn f(v: Vec<u64>) -> (Vec<u64>, Vec<u64>) {
//-      let v1 = v;
//-      let v2 = v;
//-      (v1, v2)
//-  }
/*+*/

exec fn f(v: Vec<u64>) {
    /*+*/
    let v1: Ghost<Vec<u64>> = Ghost(v);
    /*+*/
    let v2: Ghost<Vec<u64>> = Ghost(v);
    /*+*/
    assert(v1@.len() == v2@.len());
    /*+*/
}

exec fn g(v1: &mut Vec<u64>, v2: &mut Vec<u64>)
    requires
        old(v1)@.len() == 2,
        old(v2)@.len() == 3,
    ensures
        v1@.len() == v2@.len(),
{
    v1.push(42);
    v1.push(43);
    v2.push(52);
}

// exec fn g_(v1: Vec<u64>, v2: Vec<u64>) -> (out: (Vec<u64>, Vec<u64>))
//     requires
//         v1@.len() == 2,
//         v2@.len() == 3,
//     ensures
//         out.0@.len() == out.1@.len()
// {
//     let v1a = v1.push(42);
//     let v1b = v1.push(43);
//     let v2a.push(52);
//     (v1b, v2a)
// }
// ## E -- E-reverse.rs -- spec variables
/* See vectors.rs
fn reverse(v: &mut Vec<u64>) {
    ensures([
        v.len() == old(v).len(),
        forall(|i: int| 0 <= i && i < old(v).len()
               >>= v.index(i) == old(v).index(old(v).len() - i - 1)),
    ]);

    let length = v.len();
    #[spec] let v1 = *v;
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
