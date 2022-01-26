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
