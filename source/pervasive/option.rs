#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;

pub enum Option<A> {
    None,
    Some(A)
}
