/*
Statement-oriented syntax tree

Whereas ast supports statements inside expressions,
sst expressions cannot contain statments.
*/

use crate::ast::{BinaryOp, Typ, UnaryOp};
use crate::def::Spanned;
use air::ast::{Constant, Ident};
use std::rc::Rc;

pub type Exp = Rc<Spanned<ExpX>>;
pub type Exps = Rc<Vec<Exp>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Constant),
    Var(Ident),
    Call(Ident, Exps),
    Field(Exp, Ident),
    Unary(UnaryOp, Exp),
    Binary(BinaryOp, Exp, Exp),
}

pub type Stm = Rc<Spanned<StmX>>;
pub type Stms = Rc<Vec<Stm>>;
#[derive(Debug)]
pub enum StmX {
    Assume(Exp),
    Assert(Exp),
    Decl { ident: Ident, typ: Typ, mutable: bool },
    Assign(Exp, Exp),
    Fuel(Ident, u32),
    Block(Stms),
}
