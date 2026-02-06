use super::super::prelude::*;
use super::algebra::ResourceAlgebra;

verus! {

pub enum ExclusiveRA<T> {
    Exclusive(T),
    Invalid,
}

impl<T> ResourceAlgebra for ExclusiveRA<T> {
    open spec fn valid(self) -> bool {
        match self {
            ExclusiveRA::Invalid => false,
            _ => true,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        ExclusiveRA::Invalid
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

} // verus!
