#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::simple_pptr::MemContents;

verus! {

struct X {
    pub i: u64,
}

fn main() {
    let x = X { i: 5 };
    let (pcell, Tracked(mut token)) = PCell::empty();
    pcell.put(Tracked(&mut token), x);
    assert(token.mem_contents() == MemContents::Init(X { i: 5 }));
}

fn pcell_example() {
}

} // verus!
