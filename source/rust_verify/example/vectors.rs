#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, vec::*, seq::*, modes::*};

verus! {

fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i:int| i1 <= i <= i2 && k == v[i],
            forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        let d: Ghost<int> = ghost(i2 - i1);

        let ix = i1 + (i2 - i1) / 2;
        if *v.index(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }

        assert(i2 - i1 < d@);
    }
    i1
}

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let v1: Ghost<Seq<u64>> = ghost(v@);
    let mut n: usize = 0;
    while n < length / 2
        invariant
            length == v.len(),
            forall|i: int| 0 <= i < n ==> v[i] == v1@[length - i - 1],
            forall|i: int| 0 <= i < n ==> v1@[i] == v[length - i - 1],
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i] == v1@[i],
    {
        let x = *v.index(n);
        let y = *v.index(length - 1 - n);
        v.set(n, y);
        v.set(length - 1 - n, x);

        n = n + 1;
    }
}

fn pusher() -> Vec<u64> {
    let mut v = Vec::new();
    v.push(0);
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    let goal: Ghost<Seq<u64>> = ghost(Seq::new(5, |i: int| i as u64));
    assert(v@.ext_equal(goal@));
    assert(v[2] == 2);

    v.pop();
    v.push(4);
    assert(v@.ext_equal(goal@));

    v
}

spec fn uninterp_fn(x: u64) -> bool;

fn pop_test(t: Vec<u64>)
    requires
        t.len() > 0,
        forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i]),
{
    let mut t = t;
    let x = t.pop();

    assert(uninterp_fn(x));
    assert(forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i]));
}

fn pust_test(t: Vec<u64>, y: u64)
    requires
        forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i]),
        uninterp_fn(y),
{
    let mut t = t;
    t.push(y);

    assert(
        forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i])
    );
}

#[verifier(external)]
fn main() {
    let mut v = Vec{vec: vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]};
    println!("{}", binary_search(&v, 70));
    println!();
    reverse(&mut v);
    for x in v.vec {
        println!("{}", x);
    }

    println!("Pushed 5 values:");
    for x in pusher().vec {
        println!("{}", x);
    }
}

} // verus!
