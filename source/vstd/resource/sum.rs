use super::super::prelude::*;
use super::algebra::ResourceAlgebra;

verus! {

pub enum SumRA<RA1: ResourceAlgebra, RA2: ResourceAlgebra> {
    Left(RA1),
    Right(RA2),
    Invalid,
}

// Rust does not support variadic generics, so we define the sum pairwise
impl<RA1: ResourceAlgebra, RA2: ResourceAlgebra> ResourceAlgebra for SumRA<RA1, RA2> {
    open spec fn valid(self) -> bool {
        match self {
            SumRA::Left(l) => l.valid(),
            SumRA::Right(r) => r.valid(),
            SumRA::Invalid => false,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (SumRA::Left(la), SumRA::Left(lb)) => SumRA::Left(RA1::op(la, lb)),
            (SumRA::Right(ra), SumRA::Right(rb)) => SumRA::Right(RA2::op(ra, rb)),
            _ => SumRA::Invalid,
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (SumRA::Left(a), SumRA::Left(b), SumRA::Left(c)) => RA1::associative(a, b, c),
            (SumRA::Right(a), SumRA::Right(b), SumRA::Right(c)) => RA2::associative(a, b, c),
            (_, _, _) => {},
        }
    }

    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (SumRA::Left(a), SumRA::Left(b)) => RA1::commutative(a, b),
            (SumRA::Right(a), SumRA::Right(b)) => RA2::commutative(a, b),
            (_, _) => {},
        }
    }

    proof fn valid_op(a: Self, b: Self) {
        match (a, b) {
            (SumRA::Left(a), SumRA::Left(b)) => RA1::valid_op(a, b),
            (SumRA::Right(a), SumRA::Right(b)) => RA2::valid_op(a, b),
            (_, _) => {},
        }
    }
}

} // verus!
