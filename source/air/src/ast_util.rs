use crate::ast::{Binder, BinderX, Expr, ExprX, Ident, Typ, TypX};
use std::rc::Rc;

pub fn str_ident(x: &str) -> Ident {
    Rc::new(x.to_string())
}

pub fn ident_var(x: &Ident) -> Expr {
    Rc::new(ExprX::Var(x.clone()))
}

pub fn string_var(x: &String) -> Expr {
    Rc::new(ExprX::Var(Rc::new(x.clone())))
}

pub fn str_var(x: &str) -> Expr {
    Rc::new(ExprX::Var(Rc::new(x.to_string())))
}

pub fn ident_apply(x: &Ident, args: &Box<[Expr]>) -> Expr {
    Rc::new(ExprX::Apply(x.clone(), Rc::new(args.clone())))
}

pub fn string_apply(x: &String, args: &Box<[Expr]>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.clone()), Rc::new(args.clone())))
}

pub fn str_apply(x: &str, args: &Box<[Expr]>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.to_string()), Rc::new(args.clone())))
}

pub fn ident_apply_vec(x: &Ident, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(x.clone(), Rc::new(args.clone().into_boxed_slice())))
}

pub fn string_apply_vec(x: &String, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.clone()), Rc::new(args.clone().into_boxed_slice())))
}

pub fn str_apply_vec(x: &str, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.to_string()), Rc::new(args.clone().into_boxed_slice())))
}

pub fn int_typ() -> Typ {
    Rc::new(TypX::Int)
}

pub fn bool_typ() -> Typ {
    Rc::new(TypX::Bool)
}

pub fn ident_typ(x: &Ident) -> Typ {
    Rc::new(TypX::Named(x.clone()))
}

pub fn string_typ(x: &String) -> Typ {
    Rc::new(TypX::Named(Rc::new(x.clone())))
}

pub fn str_typ(x: &str) -> Typ {
    Rc::new(TypX::Named(Rc::new(x.to_string())))
}

pub fn ident_binder<A: Clone>(x: &Ident, a: &A) -> Binder<A> {
    Rc::new(BinderX { name: x.clone(), a: a.clone() })
}
