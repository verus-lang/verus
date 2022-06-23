fn main() {}

// ## 11 -- 10-program.rs

mod pervasive;
#[allow(unused_imports)] use { builtin_macros::*, builtin::*, pervasive::*, option::*, seq::*, vec::*, };

// ## A -- A-program.rs

fn max(a: u64, b: u64) -> u64 {
    ensures(|ret: u64| [
        ret == a || ret == b,
        ret >= a && ret >= b,
    ]);

    if a >= b { a } else { b }
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

#[spec]
fn divides(factor: nat, candidate: nat) -> bool {
    candidate % factor == 0
}

#[spec]
fn is_prime(candidate: nat) -> bool {
       1 < candidate
    && forall(|factor: nat| 1 < factor && factor < candidate
              >>= !divides(factor, candidate))
}

fn test_prime(candidate: u64) -> bool {
    requires(1 < candidate);
    ensures(|result: bool| result == is_prime(candidate));
    
    let mut factor: u64 = 2;
    while (factor < candidate) {
        invariant([
            1 < factor, factor <= candidate,
            forall(|smallerfactor:nat|
                   1 < smallerfactor && smallerfactor < factor
                   >>= !divides(smallerfactor, candidate))
        ]);
        if candidate % factor == 0 {
            assert(divides(factor, candidate));
            assert(!is_prime(candidate));
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

#[spec]
fn fibo(n: nat) -> nat {
  decreases(n);
  if n == 0 { 0 } else if n == 1 { 1 }
  else { fibo(n - 2) + fibo(n - 1) }
}

#[proof]
fn lemma_fibo_is_monotonic(i:nat, j:nat) {
  requires(i<=j);
  ensures(fibo(i) <= fibo(j));
  decreases(j-i);

  // ----

  if i<2 && j<2 { } else if i==j { }
  else if i==j-1 {
    reveal_with_fuel(fibo, 2);
    lemma_fibo_is_monotonic(i, j-1);
  } else {
    lemma_fibo_is_monotonic(i, j-1);
    lemma_fibo_is_monotonic(i, j-2);
  }
}

// ## D/2 -- D-fibo.rs

#[spec]
fn fibo_fits_u64(n: nat) -> bool { fibo(n) <= 0xffff_ffff_ffff_ffff }

#[exec]
fn fibo_impl(n: u64) -> u64 {
  requires(fibo_fits_u64(n));
  ensures(|result: u64| result == fibo(n));

  // ----

  if n == 0 { return 0; }
  let mut prev: u64 = 0; let mut cur: u64 = 1;
  let mut i: u64 = 1;
  while i < n {
    invariant([
      i > 0, i <= n,
      fibo_fits_u64(n as nat), fibo_fits_u64(i as nat),
      cur == fibo(i), prev == fibo(i as nat - 1),
    ]);
    i = i + 1;
    lemma_fibo_is_monotonic(i, n);
    let new_cur = cur + prev;
    prev = cur; cur = new_cur;
  }
  cur
}

// ## E -- E-reverse.rs -- spec variables

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

// F -- F-linear-proof

// cell::RefCell::Cell<X>

// G -- G-bitvector.rs

fn mod8_bw(x: u32) -> u32 {
  ensures(|ret: u32| ret == x % 8);

  assert_bit_vector(x & 7 == x % 8);
  x & 7
}
