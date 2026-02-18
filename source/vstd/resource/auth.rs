use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::exclusive::ExclusiveRA;
#[cfg(verus_keep_ghost)]
use super::option::lemma_incl_opt_rev;
use super::pcm::PCM;
#[cfg(verus_keep_ghost)]
use super::relations::incl;
#[cfg(verus_keep_ghost)]
use super::relations::lemma_incl_transitive;

verus! {

pub struct AuthRA<RA: ResourceAlgebra> {
    pub auth: Option<ExclusiveRA<RA>>,
    pub frac: RA,
}

proof fn lemma_incl_valid<RA: ResourceAlgebra>(a: RA, b: RA)
    requires
        incl(a, b),
        b.valid(),
    ensures
        a.valid(),
{
    let c = choose|c| RA::op(a, c) == b;
    RA::valid_op(a, c);
}

impl<RA: ResourceAlgebra> ResourceAlgebra for AuthRA<RA> {
    open spec fn valid(self) -> bool {
        match self.auth {
            None => self.frac.valid(),
            Some(ExclusiveRA::Exclusive(a)) => a.valid() && incl(self.frac, a),
            Some(ExclusiveRA::Invalid) => false,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        let auth = Option::<ExclusiveRA::<RA>>::op(a.auth, b.auth);
        let frac = RA::op(a.frac, b.frac);
        AuthRA { auth, frac }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        Option::<ExclusiveRA::<RA>>::associative(a.auth, b.auth, c.auth);
        RA::associative(a.frac, b.frac, c.frac);
    }

    proof fn commutative(a: Self, b: Self) {
        Option::<ExclusiveRA::<RA>>::commutative(a.auth, b.auth);
        RA::commutative(a.frac, b.frac);
    }

    proof fn valid_op(a: Self, b: Self) {
        let op = Self::op(a, b);
        match op.auth {
            None => {
                RA::valid_op(a.frac, b.frac);
            },
            Some(auth) => {
                lemma_incl_valid(op.frac, auth->Exclusive_0);

                RA::valid_op(a.frac, b.frac);
                Option::<ExclusiveRA::<RA>>::valid_op(a.auth, b.auth);
                if a.auth is Some {
                    lemma_incl_opt_rev(a.auth->Some_0, auth);
                    if a.auth->Some_0 == auth {
                        lemma_incl_transitive(a.frac, op.frac, a.auth->Some_0->Exclusive_0);
                    }
                }
            },
        }
    }
}

impl<P: PCM> PCM for AuthRA<P> {
    open spec fn unit() -> Self {
        AuthRA { auth: None, frac: P::unit() }
    }

    proof fn op_unit(self) {
        Option::<ExclusiveRA::<P>>::op_unit(self.auth);
        P::op_unit(self.frac);
    }

    proof fn unit_valid() {
        Option::<ExclusiveRA::<P>>::unit_valid();
        P::unit_valid();
    }
}

} // verus!
