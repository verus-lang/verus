#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;

#[is_variant]
pub enum Option<A> {
    None,
    Some(A)
}

// TODO this currently doesn't work without `external`,
// because of some temporary Verus trait limitations,
// but we need to implement Copy.
#[verifier(external)]
impl<A: Clone> Clone for Option<A> {
    fn clone(&self) -> Self {
        match self {
            Option::None => Option::None,
            Option::Some(a) => Option::Some(a.clone()),
        }
    }
}

impl<A: Copy> Copy for Option<A> { }

impl<A> Option<A> {
    #[spec]
    #[verifier(publish)]
    pub fn or(self, optb: Option<A>) -> Option<A> {
        match self {
            Option::None => optb,
            Option::Some(s) => self,
        }
    }

    #[exec]
    pub fn unwrap(&self) -> &A {
        requires(self.is_Some());
        ensures(|a: &A| equal(*a, self.get_Some_0()));

        match self {
            Option::Some(a) => a,
            Option::None => unreached(),
        }
    }
}
