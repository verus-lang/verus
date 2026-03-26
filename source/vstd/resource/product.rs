use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;

verus! {

pub struct ProductRA<RA1: ResourceAlgebra, RA2: ResourceAlgebra> {
    pub left: RA1,
    pub right: RA2,
}

// Rust does not support variadic generics, so we define the product pairwise
impl<RA1: ResourceAlgebra, RA2: ResourceAlgebra> ResourceAlgebra for ProductRA<RA1, RA2> {
    open spec fn valid(self) -> bool {
        self.left.valid() && self.right.valid()
    }

    open spec fn op(a: Self, b: Self) -> Self {
        ProductRA { left: RA1::op(a.left, b.left), right: RA2::op(a.right, b.right) }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        RA1::associative(a.left, b.left, c.left);
        RA2::associative(a.right, b.right, c.right);
    }

    proof fn commutative(a: Self, b: Self) {
        RA1::commutative(a.left, b.left);
        RA2::commutative(a.right, b.right);
    }

    proof fn valid_op(a: Self, b: Self) {
        RA1::valid_op(a.left, b.left);
        RA2::valid_op(a.right, b.right);
    }
}

impl<P1: PCM, P2: PCM> PCM for ProductRA<P1, P2> {
    open spec fn unit() -> Self {
        ProductRA { left: P1::unit(), right: P2::unit() }
    }

    proof fn op_unit(self) {
        P1::op_unit(self.left);
        P2::op_unit(self.right);
    }

    proof fn unit_valid() {
        P1::unit_valid();
        P2::unit_valid();
    }
}

} // verus!
