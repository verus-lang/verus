#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::option::Option;
#[allow(unused_imports)]
use pervasive::*;
use seq::Seq;

fn main() {}
/*
#[spec]
fn shifter(x: u64, amt: usize) -> u64 {
    decreases(amt);
    if amt == 0 { x }
    else { shifter(x << 1, amt - 1) }
}

const one32: u32 = 1;
const two32: u32 = 2;
const one64: u64 = 1;
const two64: u64 = 2;
fn compute_bv(x:u64) {
    assert_by_compute(!(-1) == 0); // true
    assert_by_compute(!(-2) == 1); // true
    assert_by_compute(!one32 == 0xFFFF_FFFE); // true
    assert_by_compute(!two32 == 0xFFFF_FFFD); // true
    assert_by_compute(!one64 == 0xFFFF_FFFF_FFFF_FFFE); // true
    assert_by_compute(!two64 == 0xFFFF_FFFF_FFFF_FFFD); // true
    assert_by_compute(-1 << 3 == -8); // true
    assert_by_compute(x ^ x == 0);  // true
    assert_by_compute(x & x == x);  // true
    assert_by_compute(shifter(1, 10) == 1024); // true
}

fn compute_arith(x:u64) {
    assert_by_compute((7 + 7 * 2 > 20) && (22 - 5 <= 10*10)); // true
    assert_by_compute(x * 0 == 0);  // 0 == 0
    // TODO: This currently produces: uClip(64, x) == x,
    // due to the same issue mentioned below
    assert_by_compute(x * 1 == x);
}

fn compute_ite() {
    assert_by_compute(9 == if 7 > 3 { 9 } else { 5 });  // 9 == 9
    // TODO: The example below fails the expr_to_pure_exp check,
    // due to the overflow checks that are inserted.
    // They are inserted because the mode checker treats constants as Exec,
    // which leads to the arith being marked as Exec, and the mode checker
    // confirms that an Exec expression can be passed as a Spec arg,
    // but it doesn't "upgrade" the expression to Spec.
    // This should be addressed when we move to the new syntax.
    //assert_by_compute(9 == if (7 + 7 * 2 > 20) { 7 + 2 } else { 22 - 5 + 10*10 });
}

fn compute_let() {
    assert_by_compute({#[spec]let x = true; x});    // true
    assert_by_compute({#[spec]let x = 7; x > 4});   // true
}

fn compute_datatype() {
    assert_by_compute(  // true
        match Option::Some(true) {
            Option::Some(b) => b,
            _ => 10 > 20,
        });
}

#[spec]
fn sum(x: nat) -> nat {
    decreases(x);
    if x == 0 { 0 }
    else { 1 + sum(x - 1) }
}

fn compute_call() {
    // assert(sum(10) == 10);  // fails without more fuel
    assert_by_compute(sum(10) == 10);  // true
}

#[spec]
fn fib(x: nat) -> nat {
    decreases(x);
    if x == 0 { 0 }
    else if x == 1 { 1 }
    else { fib(x - 1) + fib(x - 2) }
}

fn compute_fib() {
    assert_by_compute(fib(10) == 55);   // true
    //assert_by_compute(fib(100) == 354224848179261915075);   // TODO: times out
}

// VeriTitan example
/*
#[spec]
fn pow(base: nat, exp: nat) -> nat {
    decreases(exp);
    if exp == 0 { 1 }
    else { base * pow(base, exp - 1) }
}

const Q: nat = 12289;
const L: nat = 11;
const G: nat = 7;

fn compute_verititan() {
    assert_by_compute(pow(G, pow(2, L) / 2) % Q == Q - 1);  // TODO: stack overflow
}
*/

// VeriBetrKV example:
// https://github.com/vmware-labs/verified-betrfs/blob/ee4b18d553933440bb5ecda037c6a1c411a49a5f/lib/Crypto/CRC32Lut.i.dfy
/*
function pow_mod_crc(n: nat) : seq<bool>
  requires n >= 33
  {
    reverse(mod_F2_X(zeroes(n-33) + [true], bits_of_int(0x1_1EDC_6F41, 33)))
  }

assert (forall n | 1 <= n <= 256 :: bits_of_int(lut[n-1] as int, 64) == pow_mod_crc(2*64*n) + pow_mod_crc(64*n))
    by(computation);
*/


/*
 * Examples traversing recursive data structures
 */
#[derive(Structural,PartialEq,Eq)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

#[spec]
fn len<T>(l: List<T>) -> nat {
    decreases(l);
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
    }
}

#[spec]
fn append<T>(l: List<T>, x: T) -> List<T> {
    decreases(l);
    match l {
        List::Nil => List::Cons(x, box List::Nil),
        List::Cons(hd, tl) => 
            List::Cons(hd, box append(*tl, x)),
    }
}

#[spec]
fn reverse<T>(l: List<T>) -> List<T> {
    decreases(l);
    match l {
        List::Nil => List::Nil,
        List::Cons(hd, tl) => append(reverse(*tl), hd),
    }
}

#[spec]
fn ex1() -> List<nat> {
    List::Cons(1, box List::Cons(2, box List::Cons(3, box List::Cons(4, box List::Cons(5, box List::Nil)))))
}

#[spec]
fn ex1_rev() -> List<nat> {
    List::Cons(5, box List::Cons(4, box List::Cons(3, box List::Cons(2, box List::Cons(1, box List::Nil)))))
}

fn compute_list() {
    assert_by_compute(len(ex1()) == 5);
    assert_by_compute(equal(reverse(ex1()), ex1_rev()));
}
*/

/*
 * Computing on sequences
 */

#[spec] const empty: Seq<u32> = Seq::empty();

fn compute_seq() {
//    assert_by_compute(empty.len() == 0);
//    assert_by_compute(empty.push(4).len() == 1);
//    assert_by_compute(empty.push(4).last() == 4);
//    assert_by_compute(seq![1, 2, 3].len() == 3);
//    assert_by_compute(seq![1, 2, 3].index(1) == 2);
//    assert_by_compute(seq![1, 2, 3].index(2) == 3);
//    assert_by_compute(seq![1, 2, 3].update(1, 5).index(1) == 5);
//    assert_by_compute(seq![1, 2, 3].update(1, 5).index(2) == 3);
//    assert_by_compute(seq![1, 2, 3].add(seq![4, 5]).len() == 5);
    assert_by_compute(seq![1, 2, 3].ext_equal(seq![1].add(seq![2, 3])));
}
