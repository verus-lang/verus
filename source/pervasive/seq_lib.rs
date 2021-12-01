#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

impl<A> Seq<A> {
    #[spec]
    pub fn map<F: Fn(int, A) -> A>(self, f: F) -> Seq<A> {
        seq_new(self.len(), |i: int| f(i, self.index(i)))
    }
}
