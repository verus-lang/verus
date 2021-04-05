/*
Statement-oriented syntax tree

Whereas ast supports statements inside expressions,
sst expressions cannot contain statments.
*/

use crate::ast::{BinaryOp, UnaryOp};
use crate::def::Spanned;
use air::ast::{Const, Ident};
use std::rc::Rc;

pub type Exp = Rc<Spanned<ExpX>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Const),
    Var(Ident),
    Unary(UnaryOp, Exp),
    Binary(BinaryOp, Exp, Exp),
}

pub type Stm = Rc<Spanned<StmX>>;
pub type Stms = Rc<Box<[Stm]>>;
#[derive(Debug)]
pub enum StmX {
    Assume(Exp),
    Assert(Exp),
    Block(Stms),
}
