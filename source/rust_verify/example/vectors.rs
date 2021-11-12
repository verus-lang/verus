// extern crate builtin;
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, vec::*};

fn binary_search(v: &Vec<u64>, k: u64) -> usize {
    requires([
        forall(|i:int, j:int| imply(0 <= i && i <= j && j < len(v), index(v, i) <= index(v, j))),
        exists(|i:int| 0 <= i && i < len(v) && k == index(v, i)),
    ]);
    ensures(|r: usize| r < len(v) && k == index(v, r));

    let length = length(&v);
    let mut i1: usize = 0;
    let mut i2: usize = length - 1;
    while i1 != i2 {
        invariant([
            length == len(v),
            i2 < length,
            exists(|i:int| i1 <= i && i <= i2 && k == index(v, i)),
            forall(|i:int, j:int| imply(0 <= i && i <= j && j < length, index(v, i) <= index(v, j))),
        ]);
        #[spec] let d = i2 - i1;

        let ix = i1 + (i2 - i1) / 2;
        if *get(v, ix) < k {
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
        len(&r) == len(&v1),
        forall(|i: int| imply(0 <= i && i < len(&v1), index(&r, i) == index(&v1, len(&v1) - i - 1))),
    ]);

    let length = length(&v1);
    let mut v2 = v1;
    let mut n: usize = 0;
    while n < length / 2 {
        invariant([
            length == len(&v2),
            forall(|i: int| imply(n <= i && i + n < length, index(&v2, i) == index(&v1, i))),
            forall(|i: int| imply(0 <= i && i < n, index(&v2, i) == index(&v1, length - i - 1))),
            forall(|i: int| imply(0 <= i && i < n, index(&v1, i) == index(&v2, length - i - 1))),
        ]);

        let x = *get(&v2, n);
        let y = *get(&v2, length - 1 - n);
        v2 = set(v2, n, y);
        v2 = set(v2, length - 1 - n, x);

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
