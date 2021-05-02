use crate::ast::{Binder, BinderX, Constant, Expr, ExprX, Ident, Span, Typ, TypX};
use std::fmt::Debug;
use std::rc::Rc;

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Span").field(&self.as_string).finish()
    }
}

impl Debug for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Nat(n) => write!(f, "{}", n),
        }
    }
}

impl<A: Clone> BinderX<A> {
    pub fn map_a<B: Clone>(&self, f: impl FnOnce(&A) -> B) -> BinderX<B> {
        BinderX { name: self.name.clone(), a: f(&self.a) }
    }
}

impl<A: Clone + Debug> std::fmt::Debug for BinderX<A> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.name.fmt(fmt)?;
        fmt.write_str(" -> ")?;
        self.a.fmt(fmt)?;
        Ok(())
    }
}

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

pub fn ident_apply(x: &Ident, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(x.clone(), Rc::new(args.clone())))
}

pub fn string_apply(x: &String, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.clone()), Rc::new(args.clone())))
}

pub fn str_apply(x: &str, args: &Vec<Expr>) -> Expr {
    Rc::new(ExprX::Apply(Rc::new(x.to_string()), Rc::new(args.clone())))
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
