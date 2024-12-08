use vir::ast::{Typ, VirErr};
use super::State;

struct UnifierVar {
    i: u64
}

enum Possibility {
    Unknown,
    UnknownIntegerType,
    Type(vir::ast::Typ),
    Contradiction,
}

pub struct Unifier {
}

impl Unifier {
    pub fn new() -> Self {
        Unifier { }
    }

    //pub fn expect_equivalent(&mut self, u1: &UnifierVar, u2: &UnifierVar) -> Result<(), VirErr> {
        /*
        let a = self.uf_get_rep(u1);
        let b = self.uf_get_rep(u2);
        if a != b {
            let merged_state = merge_states(self.states[a], self.states[b])?;
            self.uf_merge(a, b)
        }
        */
        //todo!();
    //}
}

impl State<'_, '_> {
    pub fn new_unknown_typ(&mut self) -> Typ {
        todo!();
    }

    pub fn new_unknown_integer_typ(&mut self) -> Typ {
        todo!();
    }

    pub fn expect_integer(&mut self, _u2: &Typ) -> Result<(), VirErr> {
        todo!();
    }

    pub fn expect(&mut self, _t1: &Typ, _t2: &Typ) -> Result<(), VirErr> {
        todo!();
    }
}
