use vstd::calc_macro::*;
use vstd::prelude::*;

verus! {

fn main() {
}

proof fn calc_example_simple() {
    // ANCHOR: simple
    let a: int = 2;
    calc! {
        (<=)
        a; {}
        a + 3; {}
        5;
    }
    // ANCHOR_END: simple
}

#[verusfmt::skip]
proof fn calc_example_transitive_relations() {
    // ANCHOR: transitive
    let x: int = 2;
    let y: int = 5;
    calc! {
        (<=)
        x; (==) {}
        5 - 3; (<) {}
        5int; {}  // Notice that no intermediate relation
                  // is specified here, so `calc!` will
                  // consider the top-level relation
                  // `R`; here `<=`.
        y;
    }
    // ANCHOR_END: transitive
}

} // verus!
