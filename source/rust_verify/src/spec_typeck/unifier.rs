use vir::ast::VirErr;

struct UnifierVar {
    i: u64
}

enum State {
    Unknown,
    AnyIntegerType,
    Type(vir::ast::Typ),
}

pub struct Unifier {
}

impl Unifier {
    pub fn new_unif_variable(&mut self) -> UnifierVar {
        todo!();
    }

    pub fn new_unif_variable_integer(&mut self) -> UnifierVar {
        todo!();
    }

    pub fn expect_equivalent(&mut self, u1: &UnifierVar, u2: &UnifierVar) -> Result<(), VirErr> {
        let a = self.uf_get_rep(u1);
        let b = self.uf_get_rep(u2);
        if a != b {
            let merged_state = merge_states(self.states[a], self.states[b])?;
            self.uf_merge(a, b)
        }
    }

    pub fn expect_integer(&mut self, u1: &UnifierVar, u2: &vir::ast::Typ) -> Result<(), VirErr> {
    }

    pub fn expect_type(&mut self, u1: &UnifierVar, u2: &vir::ast::Typ) -> Result<(), VirErr> {
    }
}
