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

    // TODO is_sorted -- extract from summer_school e22
    #[spec] #[verifier(publish)]
    pub fn contains(self, needle: A) -> bool {
        exists(|i: nat| i<self.len() && equal(self.index(i), needle))
    }

    #[spec] #[verifier(publish)]
    pub fn drop_last(self) -> Seq<A> {
        recommends(self.len() >= 1);
        self.subrange(0, self.len() as int - 1)
    } 
}
