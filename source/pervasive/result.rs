#![deprecated(note="Use std::result instead")]

#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

#[is_variant]
pub enum Result<T, E> {
    Ok(T),
    Err(E)
}

pub use crate::result::Result::Ok;
pub use crate::result::Result::Err;

impl<T, E> Result<T, E> {
    #[inline(always)]
    pub const fn is_ok(&self) -> (res: bool)
        ensures res <==> self.is_Ok(),
    {
        match self {
            Result::Ok(_) => true,
            Result::Err(_) => false,
        }
    }

    #[inline(always)]
    pub const fn is_err(&self) -> (res: bool)
        ensures res <==> self.is_Err(),
    {
        match self {
            Result::Ok(_) => false,
            Result::Err(_) => true,
        }
    }

    pub fn as_ref(&self) -> (r: Result<&T, &E>)
        ensures
          r.is_Ok() <==> self.is_Ok(),
          r.is_Ok() ==> self.get_Ok_0() == r.get_Ok_0(),
          r.is_Err() <==> self.is_Err(),
          r.is_Err() ==> self.get_Err_0() == r.get_Err_0(),
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::Err(e) => Result::Err(e),
        }
    }

    // A more-readable synonym for get_Ok_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap(self) -> T
    recommends self.is_Ok()
    {
        self.get_Ok_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap))]
    pub fn unwrap(self) -> (t: T)
        requires
            self.is_Ok(),
        ensures
            t == self.get_Ok_0(),
    {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => unreached(),
        }
    }

    // A more-readable synonym for get_Err_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap_err(self) -> E
    recommends self.is_Err()
    {
        self.get_Err_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap_err))]
    pub fn unwrap_err(self) -> (e: E)
        requires
            self.is_Err(),
        ensures
            e == self.get_Err_0(),
    {
        match self {
            Result::Ok(_) => unreached(),
            Result::Err(e) => e,
        }
    }
}

} // verus!
