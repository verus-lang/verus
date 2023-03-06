// rust_verify/tests/example.rs

use builtin_macros::*;
use builtin::*;
#[cfg(not(vstd_todo))]
mod pervasive;
#[cfg(not(vstd_todo))]
use pervasive::*;
#[cfg(vstd_todo)]
use vstd::*;

verus! {

struct Thing {
}

impl std::cmp::PartialEq<Thing> for Thing {
    fn eq(&self, _: &Thing) -> bool { todo!() }
}

impl std::cmp::Eq for Thing { }

#[derive(PartialEq, Eq)]
struct Car {
    thing: Thing,
    four_doors: bool,
}

fn one() {
    let c1 = Car { thing: Thing {}, four_doors: true };
    let c2 = Car { thing: Thing {}, four_doors: true };
    assert(c1 == c2);
    let t1 = Thing {};
    let t2 = Thing {};
    assert(t1 == t2);
}

fn main() { }

}
