use vstd::prelude::*;

verus! {

fn main() {
}

// ANCHOR: min
fn option_min(x: Option<u8>, y: Option<u8>) -> (r : Option<u8>)
ensures
    x matches Some(x) ==> r matches Some(r) && r <= x,
    y matches Some(y) ==> r matches Some(r) && r <= y,
    r == x || r == y
{
    match (x, y) {
        (Some(x), Some(y)) => Some(if x <= y { x } else { y }),
        (x@Some(_), _) => x,
        (_, y@Some(_)) => y,
        (None, None) => None,
    }
}
// ANCHOR_END: min
} // verus!
