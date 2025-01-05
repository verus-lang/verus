use std::option::Option::{None, Some};

use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {

fn is_some_test() {
    let a: Option<i32> = None;
    let b = Some(2);
    runtime_assert(!a.is_some());
    runtime_assert(b.is_some());
}

fn is_none_test() {
    let a: Option<i32> = None;
    let b = Some(2);
    runtime_assert(a.is_none());
    runtime_assert(!b.is_none());
}

fn as_ref_test() {
    let a = Option::Some(2);
    if let Some(ref_val) = a.as_ref() {
        runtime_assert(*ref_val == 2);
    } else {
        runtime_assert(false);
    }
}

fn unwrap_test() {
    let a = Option::Some(2);
    let b = Option::Some(4);
    runtime_assert(a.unwrap() == 2);
    runtime_assert(a.unwrap() != b.unwrap());
}

fn unwrap_or_test() {
    let a = Option::Some(2);
    let b = Option::None;
    runtime_assert(a.unwrap_or(3) == 2);
    runtime_assert(b.unwrap_or(3) == 3);
}

fn ok_or_test() {
    let a: Option<i32> = Option::Some(2);
    let b: Option<i32> = Option::None;
    let ra: Result<i32, bool> = a.ok_or(false);
    let rb: Result<i32, bool> = b.ok_or(false);
    assert(ra.is_ok());
    assert(ra.unwrap() == 2);
    assert(rb.is_err());
    assert(rb.unwrap_err() == false);
}

} // verus!
