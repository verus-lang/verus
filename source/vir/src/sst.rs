/*
Statement-oriented syntax tree

Whereas ast supports statements inside expressions,
sst expressions cannot contain statments.
*/

use crate::ast::{BinaryOp, TernaryOp, Typ, UnaryOp};
use crate::def::Spanned;
use air::ast::{Binders, Constant, Ident, Quant};
use std::rc::Rc;

pub type Trig = Exps;
pub type Trigs = Rc<Vec<Trig>>;

pub type Bnd = Rc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    #[allow(dead_code)]
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
}

pub type Exp = Rc<Spanned<ExpX>>;
pub type Exps = Rc<Vec<Exp>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Constant),
    Var(Ident),
    Old(Ident, Ident), // used only during sst_to_air to generate AIR Old
    Call(Ident, Exps), // call to spec function
    Field {
        lhs: Exp,
        datatype_name: Ident,
        field_name: Ident,
    },
    Unary(UnaryOp, Exp),
    Binary(BinaryOp, Exp, Exp),
    #[allow(dead_code)]
    Ternary(TernaryOp, Exp, Exp, Exp),
    Bind(Bnd, Exp),
}

#[derive(Debug)]
pub struct Dest {
    pub var: Ident,
    pub mutable: bool,
}

pub type Stm = Rc<Spanned<StmX>>;
pub type Stms = Rc<Vec<Stm>>;
#[derive(Debug)]
pub enum StmX {
    Call(Ident, Exps, Option<Dest>), // call to exec/proof function
    Assume(Exp),
    Assert(Exp),
    Decl { ident: Ident, typ: Typ, mutable: bool },
    Assign(Exp, Exp),
    Fuel(Ident, u32),
    Block(Stms),
}
