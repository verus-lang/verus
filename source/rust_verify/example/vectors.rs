extern crate builtin;
use builtin::*;
mod pervasive;
mod pervasive_vec;
#[allow(unused_imports)]
use pervasive::*;
use pervasive_vec::*;

fn binary_search(v: &Vec<u64>, length: usize, k: u64) -> usize {
    requires([
        len(v) == length,
        forall(|i:int, j:int| imply(0 <= i && i <= j && j < length, index(v, i) <= index(v, j))),
        exists(|i:int| 0 <= i && i < length && index(v, i) == k),
    ]);
    ensures(|r: usize| r < length && index(v, r) == k);

    let mut i1: usize = 0;
    let mut i2: usize = length - 1;
    while i1 != i2 {
        invariant([
            len(v) == length,
            i2 < length,
            exists(|i:int| i1 as int <= i && i <= i2 && index(v, i) == k),
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

fn reverse(v1: Vec<u64>, length: usize) -> Vec<u64> {
    requires([
        len(&v1) == length,
    ]);
    ensures(|r: Vec<u64>| [
        len(&r) == length,
        forall(|i: int| imply(0 <= i && i < length, index(&r, i) == index(&v1, length as int - 1 - i))),
    ]);

    let mut v2 = v1;
    let mut n: usize = 0;
    while n < length / 2 {
        invariant([
            len(&v2) == length,
            forall(|i: int| imply(i >= n && i < length as int - n, index(&v2, i) == index(&v1, i))),
            forall(|i: int| imply(0 <= i && i < n, index(&v2, i) == index(&v1, length as int - 1 - i))),
            forall(|i: int| imply(0 <= i && i < n, index(&v1, i) == index(&v2, length as int - 1 - i))),
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
    let length = 10; // TODO: let length = v.vec.len();
    println!("{}", binary_search(&v, length, 70));
    println!();
    for x in reverse(v, length).vec {
        println!("{}", x);
    }
}
