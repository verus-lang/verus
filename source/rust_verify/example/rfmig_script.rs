// #![allow(unused_imports, unused_macros, non_camel_case_types)] #![feature(fmt_internals)]
use vstd::prelude::*;

fn main() {}

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
pub struct Account {
    pub balance: u64,
}

pub fn transfer(orig: &mut Account, dest: &mut Account, amount: u64)
    requires
        old(orig).balance >= amount,
        old(dest).balance + amount < u64::MAX,
    ensures
        dest.balance == old(dest).balance + amount,
        orig.balance == old(orig).balance - amount,
{
    /*+*/
    let accounts_pre: Ghost<(Account, Account)> = Ghost((*orig, *dest));
    orig.balance = orig.balance - amount;
    dest.balance = dest.balance + amount;
    /*+*/
    assert(orig.balance + dest.balance == accounts_pre@.0.balance + accounts_pre@.1.balance);
}

//- fn cmain(account: Account)
//-     requires account.balance >= 100
//- {
//-     let mut account = account;
//-     transfer(&mut account, &mut account, 100);
//- }
// ## C2(e) -- C2-linearity.rs
use vstd::prelude::*;

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

// ## D -- D-recommends.rs
spec fn divide(x: nat, y: nat) -> nat
    recommends
        y != 0,
{
    x / y
}

// E -- E-solvers.rs
proof fn div_is_smaller(x: nat, y: nat)/*+*/

    by (nonlinear_arith)
    requires
        y != 0,
    ensures
        divide(x, y) <= x,
{
}

fn mod8_bw(x: u32) -> (ret: u32)
    ensures
        ret == x % 8,
{
    assert(x & 7 == x % 8) by (bit_vector);
    x & 7
}

// F0 -- F-linear-ghost
struct State1 {
    s: nat,
}

struct State2 {
    s: nat,
}

#[verifier::external_body]
proof fn exchange(tracked s1: State1) -> (tracked s2: State2)
    ensures
        s1.s == s2.s,
{
    todo!()
}

#[verifier::external_body]
proof fn exercise1(tracked s1: &State1) -> (result: bool) {
    todo!()
}

#[verifier::external_body]
proof fn exercise2(tracked s1: &State1) -> (result: bool) {
    todo!()
}

proof fn p(tracked s1: State1) {
    //+ let tracked s2 = exchange(s1);
    exercise1(&s1);
    //+ exercise(&s2);
}

// F1 -- F-linear-proof
mod F1 {
    use vstd::{prelude::*, simple_pptr::*};

    #[verifier::external_body]
    fn send_pointer(ptr: PPtr<u64>) {
        todo!()
    }

    #[verifier::external_body]
    proof fn transfer_permission(tracked perm: PointsTo<u64>) {
        todo!()
    }

    fn increment(counter: PPtr<u64>, Tracked(perm): Tracked<&mut PointsTo<u64>>)
        requires
            counter == old(perm).pptr(),
            old(perm).is_init() && old(perm).value() < 100,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.opt_value() == MemContents::Init((old(perm).value() + 1) as u64),
    {
        // pub fn borrow<'a>(&self, perm: &'a Tracked<PointsTo<V>>) -> (v: &'a V)
        let cur_i: u64 = *counter.borrow(Tracked(&*perm));
        // pub fn replace(&self, perm: &mut Tracked<PointsTo<V>>, in_v: V) -> (out_v: V)
        counter.replace(Tracked(perm), cur_i + 1);
    }

    fn start_thread(counter: PPtr<u64>, Tracked(perm): Tracked<PointsTo<u64>>)
        requires
            counter == perm.pptr(),
            perm.opt_value() === MemContents::Uninit,
    {
        send_pointer(counter);
        let tracked mut perm: PointsTo<u64> = perm;
        // pub fn put(&self, perm: &mut Tracked<PointsTo<V>>, v: V)
        counter.put(Tracked(&mut perm), 5);
        assert(perm.opt_value() === MemContents::Init(5));
        //+ proof { transfer_permission(perm) };
        increment(counter, Tracked(&mut perm));
        assert(perm.opt_value() === MemContents::Init(6));
    }

}

// F1

} // verus!
