#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {
    /// Indicates that the type's hash implementation matches the type's Eq, PartialEq
    /// implementations and respects structural equality
    #[verifier(external)]
    pub unsafe trait HashEq {}

    #[verifier(external)]
    unsafe impl HashEq for super::string::String {}
}
