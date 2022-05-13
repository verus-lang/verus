#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, vec::*, seq::*};

fn binary_search(v: &Vec<u64>, k: u64) -> usize {
    requires([
        forall(|i:int, j:int| 0 <= i && i <= j && j < v.len() >>= v.index(i) <= v.index(j)),
        exists(|i:int| 0 <= i && i < v.len() && k == v.index(i)),
    ]);
    ensures(|r: usize| r < v.len() && k == v.index(r));

    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2 {
        invariant([
            i2 < v.len(),
            exists(|i:int| i1 <= i && i <= i2 && k == v.index(i)),
            forall(|i:int, j:int| 0 <= i && i <= j && j < v.len() >>= v.index(i) <= v.index(j)),
        ]);
        #[spec] let d = i2 - i1;

        let ix = i1 + (i2 - i1) / 2;
        if *v.index(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }

        assert(i2 - i1 < d);
    }
    i1
}

fn reverse(v: &mut Vec<u64>) {
    ensures([
        v.len() == old(v).len(),
        forall(|i: int| 0 <= i && i < old(v).len() >>= v.index(i) == old(v).index(old(v).len() - i - 1)),
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

fn pusher() -> Vec<u64> {
    let mut v = Vec::new();
    v.push(0);
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    #[spec] let goal = Seq::new(5, |i:int| i as u64);
    assert(v.view().ext_equal(goal));
    assert(v.index(2) == 2);

    v.pop();
    v.push(4);
    assert(v.view().ext_equal(goal));

    v
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
