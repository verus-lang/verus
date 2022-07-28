#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
mod pervasive;
use crate::pervasive::{*, cell::*};
use crate::pervasive::modes::*;
use crate::pervasive::option::*;

verus!{

// ANCHOR: example
fn main() {
    // Construct a new pcell and obtain the permission for it.
    let (pcell, mut perm) = PCell::<u64>::empty();

    // Initially, cell is unitialized, and the `perm` token
    // represents that as the value `None`.
    assert(perm@.value === Option::None);

    // We can write a value to the pcell (thus initializing it).
    // This only requires an `&` reference to the PCell, but it does
    // mutate the `perm` token.
    pcell.put(&mut perm, 5); 

    // Having written the value, this is reflected in the token:
    assert(perm@.value === Option::Some(5));

    // We can take the value back out:
    let x = pcell.take(&mut perm); 

    // Which leaves it uninitialized again:
    assert(x == 5);
    assert(perm@.value === Option::None);
}
// ANCHOR_END: example

}

/*
// After erasure, this looks more like:

// ANCHOR: erased
fn main() {
  let pcell = PCell::<u64>::empty();
  pcell.put(5);
  let x = pcell.take();
}
// ANCHOR_END: erased
*/
