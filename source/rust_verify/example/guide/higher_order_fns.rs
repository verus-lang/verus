// rust_verify/tests/example.rs expect-failures

#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use vstd::*;
use vstd::modes::*;
use vstd::map::*;
use vstd::seq::*;
use vstd::prelude::*;

verus!{

mod X {
use super::*;

// ANCHOR: example1
fn double(x: u8) -> (res: u8)
    requires 0 <= x < 128,
    ensures res == 2 * x,
{
    2 * x
}

fn higher_order_fn(f: impl Fn(u8) -> u8) -> (res: u8)
{
    f(50)
}

fn test() {
    higher_order_fn(double);
}
// ANCHOR_END: example1

}

mod Y {
use super::*;

// ANCHOR: example2
fn double(x: u8) -> (res: u8)
    requires 0 <= x < 128,
    ensures res == 2 * x,
{
    2 * x
}

fn higher_order_fn(f: impl Fn(u8) -> u8) -> (res: u8)
    requires call_requires(f, (50,))
{
    f(50)
}

fn test() {
    higher_order_fn(double);
}
// ANCHOR_END: example2

}

mod Z {
use super::*;

// ANCHOR: example3
fn double(x: u8) -> (res: u8)
    requires 0 <= x < 128,
    ensures res == 2 * x,
{
    2 * x
}

fn higher_order_fn(f: impl Fn(u8) -> u8) -> (res: u8)
    requires
        call_requires(f, (50,)),
        forall |x, y| call_ensures(f, x, y) ==> y % 2 == 0,
    ensures
        res % 2 == 0
{
    let ret = f(50);
    return ret;
}

fn test() {
    higher_order_fn(double);
}
// ANCHOR_END: example3

}


// ANCHOR: vec_map
// ANCHOR: vec_map_signature
fn vec_map<T, U>(v: &Vec<T>, f: impl Fn(T) -> U) -> (result: Vec<U>)
    where T: Copy
// ANCHOR_END: vec_map_signature
// ANCHOR: vec_map_requires
    requires
        forall |i| 0 <= i < v.len() ==> call_requires(f, (v[i],)),
// ANCHOR_END: vec_map_requires
// ANCHOR: vec_map_ensures
    ensures
        result.len() == v.len(),
        forall |i| 0 <= i < v.len() ==> call_ensures(f, (v[i],), #[trigger] result[i])
// ANCHOR_END: vec_map_ensures
{
    let mut result = Vec::new();
    let mut j = 0;
    while j < v.len()
        invariant 
            forall |i| 0 <= i < v.len() ==> call_requires(f, (v[i],)),
            0 <= j <= v.len(),
            j == result.len(),
            forall |i| 0 <= i < j ==> call_ensures(f, (v[i],), #[trigger] result[i]),
    {
        result.push(f(v[j]));
        j += 1;
    }
    result
}
// ANCHOR_END: vec_map

// ANCHOR: vec_map_example
fn double(x: u8) -> (res: u8)
    requires 0 <= x < 128,
    ensures res == 2 * x,
{
    2 * x
}

fn test_vec_map() {
    let mut v = Vec::new();
    v.push(0);
    v.push(10);
    v.push(20);

    let w = vec_map(&v, double);
    assert(w[2] == 40);
}
// ANCHOR_END: vec_map_example


fn main() { }

}
