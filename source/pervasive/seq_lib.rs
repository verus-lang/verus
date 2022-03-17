#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

impl<A> Seq<A> {
    #[spec] #[verifier(publish)]
    pub fn map<B, F: Fn(int, A) -> B>(self, f: F) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self.index(i)))
    }

    // TODO is_sorted -- summer_school e22
}
