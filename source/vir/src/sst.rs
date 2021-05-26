/*
Statement-oriented syntax tree

Whereas ast supports statements inside expressions,
sst expressions cannot contain statments.
*/

use crate::ast::{BinaryOp, Path, Typ, Typs, UnaryOp, UnaryOpr};
use crate::def::Spanned;
use air::ast::{Binders, Ident, Quant};
use std::rc::Rc;

pub type Trig = Exps;
pub type Trigs = Rc<Vec<Trig>>;

pub type Bnd = Rc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
}

#[derive(Clone, Debug)]
pub enum Constant {
    Bool(bool),
    Nat(Rc<String>),
}

pub type Exp = Rc<Spanned<ExpX>>;
pub type Exps = Rc<Vec<Exp>>;
#[derive(Debug)]
pub enum ExpX {
    Const(Constant),
    Var(Ident),
    Old(Ident, Ident),       // used only during sst_to_air to generate AIR Old
    Call(Ident, Typs, Exps), // call to spec function
    Ctor(Path, Ident, Binders<Exp>),
    Field { lhs: Exp, datatype_name: Ident, field_name: Ident },
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
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
    Call(Ident, Typs, Exps, Option<Dest>), // call to exec/proof function
    Assert(Exp),
    Assume(Exp),
    Decl {
        ident: Ident,
        typ: Typ,
        mutable: bool,
        init: bool,
    },
    Assign(Exp, Exp),
    Fuel(Ident, u32),
    If(Exp, Stm, Option<Stm>),
    While {
        cond: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Rc<Vec<(Ident, Typ)>>,
        modified_vars: Rc<Vec<Ident>>,
    },
    Block(Stms),
}
