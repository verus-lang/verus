#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{modes::*, prelude::*, seq::*, *};

verus! {

enum List<A> {
    Nil,
    Cons(A, Box<List<A>>),
}

spec fn len<A>(list: &List<A>) -> nat
    decreases list,
{
    match list {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(tl),
    }
}

fn get_len<A>(list: &List<A>) -> (r: u64)
    requires
        len(list) <= 0xffffffffffffffff,
    ensures
        r == len(list),
{
    let mut n: u64 = 0;
    let mut done = false;
    let mut iter = list;
    while !done
        invariant
            len(list) <= 0xffffffffffffffff,
            n + len(iter) == len(list),
            done ==> len(iter) == 0,
    {
        match iter {
            List::Nil => {
                done = true;
            },
            List::Cons(_, tl) => {
                iter = tl;
                proof {
                    reveal_with_fuel(len, 2);
                }
                n = n + 1;
            },
        }
    }
    n
}

fn mk_range(start: u32, length: u32) -> (r: List<u32>)
    requires
        start + length <= 0xffff_ffff,
    ensures
        len::<u32>(&r) == length,
    decreases length,
{
    if length == 0 {
        List::Nil
    } else {
        List::Cons(start, Box::new(mk_range(start + 1, length - 1)))
    }
}

fn main() {
    let x = List::Cons(100u64, Box::new(List::Nil));
    let i = match x {
        List::Nil => 1,
        List::Cons(n, _) if n < 10 => n + 2,
        List::Cons(n, _) if n < 100 => n + 3,
        List::Cons(n, _) if n < 200 => n + 4,
        List::Cons(n, _) => n + 5,
    };
    assert(i == 104);
    let mut j: u64 = 0;
    match x {
        List::Nil => {
            j = 1;
        },
        List::Cons(n, _) => {
            j = n;
        },
    }
    assert(j == 100);
    let k: u32 = match List::Cons(100u64, Box::new(List::Nil)) {
        List::Nil => {
            j = 11;
            6
        },
        List::Cons(n, _) => {
            j = n + 1;
            7
        },
    };
    assert(j == 101);
    assert(k == 7);
}

} // verus!
