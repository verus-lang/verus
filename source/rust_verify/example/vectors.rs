#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, vec::*};

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

fn reverse(v1: Vec<u64>) -> Vec<u64> {
    ensures(|r: Vec<u64>| [
        r.len() == v1.len(),
        forall(|i: int| 0 <= i && i < v1.len() >>= r.index(i) == v1.index(v1.len() - i - 1)),
    ]);

    let length = v1.len();
    let mut v2 = v1;
    let mut n: usize = 0;
    while n < length / 2 {
        invariant([
            length == v2.len(),
            forall(|i: int| n <= i && i + n < length >>= v2.index(i) == v1.index(i)),
            forall(|i: int| 0 <= i && i < n >>= v2.index(i) == v1.index(length - i - 1)),
            forall(|i: int| 0 <= i && i < n >>= v1.index(i) == v2.index(length - i - 1)),
        ]);

        let x = *v2.index(n);
        let y = *v2.index(length - 1 - n);
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
