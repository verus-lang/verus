#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, vec::*};

fn binary_search(v: &Vec<u64>, k: u64) -> usize {
    requires([
        forall(|i:int, j:int| 0 <= i && i <= j && j < v.view().len() >>= v.idx(i) <= v.idx(j)),
        exists(|i:int| 0 <= i && i < v.view().len() && k == v.idx(i)),
    ]);
    ensures(|r: usize| r < v.view().len() && k == v.idx(r));

    let length = v.len();
    let mut i1: usize = 0;
    let mut i2: usize = length - 1;
    while i1 != i2 {
        invariant([
            length == v.view().len(),
            i2 < length,
            exists(|i:int| i1 <= i && i <= i2 && k == v.idx(i)),
            forall(|i:int, j:int| 0 <= i && i <= j && j < length >>= v.idx(i) <= v.idx(j)),
        ]);
        #[spec] let d = i2 - i1;

        let ix = i1 + (i2 - i1) / 2;
        if *v.get(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }

        assert(i2 - i1 < d);
    }
    i1
}

fn reverse(v1: Vec<u64>) -> Vec<u64> {
    ensures(|r: Vec<u64>| [
        r.view().len() == v1.view().len(),
        forall(|i: int| 0 <= i && i < v1.view().len() >>= r.idx(i) == v1.idx(v1.view().len() - i - 1)),
    ]);

    let length = v1.len();
    let mut v2 = v1;
    let mut n: usize = 0;
    while n < length / 2 {
        invariant([
            length == v2.view().len(),
            forall(|i: int| n <= i && i + n < length >>= v2.idx(i) == v1.idx(i)),
            forall(|i: int| 0 <= i && i < n >>= v2.idx(i) == v1.idx(length - i - 1)),
            forall(|i: int| 0 <= i && i < n >>= v1.idx(i) == v2.idx(length - i - 1)),
        ]);

        let x = *v2.get(n);
        let y = *v2.get(length - 1 - n);
        v2 = v2.set(n, y);
        v2 = v2.set(length - 1 - n, x);

        n = n + 1;
    }
    v2
}

#[verifier(external)]
fn main() {
    let v = Vec{vec: vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]};
    println!("{}", binary_search(&v, 70));
    println!();
    for x in reverse(v).vec {
        println!("{}", x);
    }
}
