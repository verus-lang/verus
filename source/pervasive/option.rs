#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;

verus! {

#[deprecated(note="Use std::option::Option instead")]
#[is_variant]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
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
    pub open spec fn or(self, optb: Option<A>) -> Option<A> {
        match self {
            Option::None => optb,
            Option::Some(s) => self,
        }
    }

    #[inline(always)]
    pub const fn is_some(&self) -> (res: bool)
        ensures res <==> self.is_Some(),
    {
        match self {
            Option::Some(_) => true,
            Option::None => false,
        }
    }

    #[inline(always)]
    pub const fn is_none(&self) -> (res: bool)
        ensures res <==> self.is_None(),
    {
        match self {
            Option::Some(_) => false,
            Option::None => true,
        }
    }

    pub fn as_ref(&self) -> (a: Option<&A>)
        ensures
          a.is_Some() <==> self.is_Some(),
          a.is_Some() ==> self.get_Some_0() == a.get_Some_0(),
    {
        match self {
            Option::Some(x) => Option::Some(x),
            Option::None => Option::None,
        }
    }

    // A more-readable synonym for get_Some_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap(self) -> A
    recommends self.is_Some()
    {
        self.get_Some_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap))]
    pub fn unwrap(self) -> (a: A)
        requires
            self.is_Some(),
        ensures
            a == self.get_Some_0(),
    {
        match self {
            Option::Some(a) => a,
            Option::None => unreached(),
        }
    }

    pub proof fn tracked_unwrap(tracked self) -> (tracked a: A)
        requires
            self.is_Some(),
        ensures
            a == self.get_Some_0(),
    {
        match self {
            Option::Some(a) => a,
            Option::None => proof_from_false(),
        }
    }
}

} // verus!

/// A poor-person's `?` operator, until Verus switches to the "real" Rust `Option`.
#[macro_export]
#[allow(unused_macros)]
macro_rules! try_option {
    ($x:expr) => {{
        let x = $x;
        match x {
            $crate::option::Option::None => {
                return $crate::option::Option::None;
            }
            $crate::option::Option::Some(x) => x,
        }
    }};
}
