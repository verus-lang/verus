extern crate builtin;
use builtin::*;
mod pervasive;
mod pervasive_vec;
#[allow(unused_imports)]
use pervasive::*;
use pervasive_vec::*;

fn binary_search(v: &Vec<u64>, length: usize, k: u64) -> usize {
    requires([
        length == len(v),
        forall(|i:int, j:int| imply(0 <= i && i <= j && j < length, index(v, i) <= index(v, j))),
        exists(|i:int| 0 <= i && i < length && k == index(v, i)),
    ]);
    ensures(|r: usize| r < length && k == index(v, r));

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

fn reverse(v1: Vec<u64>, length: usize) -> Vec<u64> {
    requires([
        length == len(&v1),
    ]);
    ensures(|r: Vec<u64>| [
        length == len(&r),
        forall(|i: int| imply(0 <= i && i < length, index(&r, i) == index(&v1, length - i - 1))),
    ]);

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
    let length = 10; // TODO: let length = v.vec.len();
    println!("{}", binary_search(&v, length, 70));
    println!();
    for x in reverse(v, length).vec {
        println!("{}", x);
    }
}
