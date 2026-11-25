use vstd::prelude::*;

use gat_lib::*;

verus! {

pub struct Tagged;

impl Container for Tagged {
    type Item<A> = Wrap<(A, u8)>;

    fn make<A>(&self, a: A) -> (r: Wrap<(A, u8)>)
        ensures r.0.1 == 7,
    {
        Wrap((a, 7))
    }
}

proof fn item_size<C: Container>(x: C::Item<bool>)
    ensures x.size() > 0,
{
    x.size_pos();
}

fn main() {
    let w = make_u8(&Tagged);
    assert(w.size() == 1);
    let v = Tagged.make(true);
    assert(v.0.1 == 7);
}

} // verus!
