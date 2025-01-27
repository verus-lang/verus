use std::rc::Rc;

use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

verus! {

fn try_unwrap_test() {
    let r1 = Rc::new(5);
    let r2 = r1.clone();
    let result1 = Rc::try_unwrap(r1);
    assert(result1 is Err ==> result1.unwrap_err() == 5);
    match result1 {
        Err(r3) => { runtime_assert(*r3 == 5); },
        Ok(five) => { assert(five == 5); }, // won't happen
    };
    let result2 = Rc::try_unwrap(r2);
    assert(result2 is Ok ==> result2.unwrap() == 5);
    match result2 {
        Err(r4) => { assert(r4 == 5); }, // won't happen
        Ok(five) => { runtime_assert(five == 5); },
    }

}

fn into_inner_test() {
    let r1 = Rc::new(5);
    let r2 = r1.clone();
    let result1 = Rc::into_inner(r1);
    match result1 {
        Some(five) => {
            assert(five == 5); // won't happen
        },
        None => {
            let result2 = Rc::into_inner(r2);
            match result2 {
                Some(five) => { runtime_assert(five == 5) },
                None => {},
            }
        },
    }
}

} // verus!
