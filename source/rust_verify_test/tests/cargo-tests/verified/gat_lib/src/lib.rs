use vstd::prelude::*;

verus! {

pub trait Size {
    spec fn size(&self) -> nat;

    proof fn size_pos(&self)
        ensures self.size() > 0;
}

pub trait Container {
    type Item<A>: Size;

    fn make<A>(&self, a: A) -> (r: Self::Item<A>)
        ensures r.size() == 1;
}

pub struct Wrap<A>(pub A);

impl<A> Size for Wrap<A> {
    open spec fn size(&self) -> nat { 1 }

    proof fn size_pos(&self) {}
}

pub fn make_u8<C: Container>(c: &C) -> (r: C::Item<u8>)
    ensures r.size() == 1,
{
    c.make(3u8)
}

} // verus!
