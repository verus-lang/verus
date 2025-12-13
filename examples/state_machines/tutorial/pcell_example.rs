// rust_verify/tests/example.rs
#![allow(unused_imports)]

use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::{cell::*, pervasive::*};

verus! {

// ANCHOR: example
fn main() {
    // Construct a new pcell and obtain the permission for it.
    let (pcell, Tracked(mut perm)) = PCell::<u64>::empty();

    // Initially, cell is unitialized, and the `perm` token
    // represents that as the value `MemContents::Uninit`.
    // The meaning of the permission token is given by its _view_, here `perm@`.
    //
    // The expression `pcell_opt![ pcell.id() => MemContents::Uninit ]` can be read as roughly,
    // "the cell with value pcell.id() is uninitialized".
    assert(perm@ === pcell_points![ pcell.id() => MemContents::Uninit ]);

    // The above could also be written by accessing the fields of the
    // `PointsToData` struct:
    assert(perm.id() === pcell.id());
    assert(perm.mem_contents() === MemContents::Uninit);

    // We can write a value to the pcell (thus initializing it).
    // This only requires an `&` reference to the PCell, but it does
    // mutate the `perm` token.
    pcell.put(Tracked(&mut perm), 5);

    // Having written the value, this is reflected in the token:
    assert(perm@ === pcell_points![ pcell.id() => MemContents::Init(5) ]);

    // We can take the value back out:
    let x = pcell.take(Tracked(&mut perm));

    // Which leaves it uninitialized again:
    assert(x == 5);
    assert(perm@ === pcell_points![ pcell.id() => MemContents::Uninit ]);
}
// ANCHOR_END: example

} // verus!
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
