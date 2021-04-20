/*
Statement-oriented syntax tree

Whereas ast supports statements inside expressions,
sst expressions cannot contain statments.
*/

use crate::ast::{BinaryOp, Typ, UnaryOp};
use crate::def::Spanned;
use air::ast::{Const, Ident};
use std::rc::Rc;

pub type Exp = Rc<Spanned<ExpX>>;
pub type Exps = Rc<Box<[Exp]>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Const),
    Var(Ident),
    Call(Ident, Exps),
    Unary(UnaryOp, Exp),
    Binary(BinaryOp, Exp, Exp),
}

pub type Stm = Rc<Spanned<StmX>>;
pub type Stms = Rc<Box<[Stm]>>;
#[derive(Debug)]
pub enum StmX {
    Assume(Exp),
    Assert(Exp),
    Decl { ident: Ident, typ: Typ, mutable: bool },
    Assign(Exp, Exp),
    Fuel(Ident, u32),
    Block(Stms),
}
