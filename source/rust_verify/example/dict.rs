#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, dict::*, map::*, string::*, option::*};

verus! {
#[derive(Eq, PartialEq, Structural, Hash)]
pub struct ObjectKey { a: u64 }

#[verifier(external)]
unsafe impl pervasive::hash::HashEq for ObjectKey {}

fn main() {
    let mut d = Dict::new();
    d.insert(ObjectKey { a: 3 }, 3);
    assert(d@.dom().contains(ObjectKey { a: 3 }));
    d.insert(ObjectKey { a: 4 }, 4);
    let a3 = d.insert(ObjectKey { a: 3 }, 5);
    assert(a3 === Option::Some(3));
}
}
