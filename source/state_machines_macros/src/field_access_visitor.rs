use crate::ast::{Field, LetKind, SpecialOp, TransitionStmt};
use proc_macro2::Span;
use std::collections::{HashMap, HashSet};
use syn::parse::Error;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{Expr, ExprField, ExprPath, Ident, Member};

/// Given a (Rust AST) Expr `e`, visits all the subexpressions of the form
/// `self.foo` where `foo` is a state machine field, and calls the given
/// function `f` on each one.
/// Note `f` takes a `&mut Expr` so it is allowed to modify the subexpression,
/// and it also takes a `&mut Vec<Error>` so it can produce errors.
///
/// The visitor itself may also produce errors. Specifically, it will create
/// an error if it finds a use of `self` for any reason that is NOT an access
/// of a state machine field. For example, `self.associated_method()` is
/// not allowed, nor is using `self` without a "dot" access.

pub fn visit_field_accesses<F>(
    e: &mut Expr,
    f: F,
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) where
    F: FnMut(&mut Vec<Error>, &Field, &mut Expr) -> (),
{
    let mut f = FieldAccessVisitor { errors, user_fn: f, ident_to_field };

    f.visit_expr_mut(e);
}

struct FieldAccessVisitor<'a, F>
where
    F: FnMut(&mut Vec<Error>, &Field, &mut Expr) -> (),
{
    pub errors: &'a mut Vec<Error>,
    pub user_fn: F,
    pub ident_to_field: &'a HashMap<String, Field>,
}

impl<'a, F> VisitMut for FieldAccessVisitor<'a, F>
where
    F: FnMut(&mut Vec<Error>, &Field, &mut Expr) -> (),
{
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let span = node.span();
        match node {
            Expr::Verbatim(_) => {
                panic!(
                    "can't process a Verbatim expression; (and there shouldn't be one in a user-provided expression in the first place)"
                );
            }
            Expr::Path(ExprPath { attrs: _, qself: None, path }) if path.is_ident("self") => {
                self.errors.push(Error::new(span,
                    "in a concurrent state machine, 'self' cannot be used opaquely; it may only be used by accessing its fields"));
            }
            Expr::Field(ExprField {
                base: box Expr::Path(ExprPath { attrs: _, qself: None, path }),
                member,
                attrs: _,
                dot_token: _,
            }) if path.is_ident("self") => match member {
                Member::Named(ident) => {
                    match get_field_by_ident(self.ident_to_field, span, ident) {
                        Err(err) => self.errors.push(err),
                        Ok(field) => {
                            (self.user_fn)(&mut self.errors, field, node);
                        }
                    }
                }
                _ => {
                    self.errors.push(Error::new(span, "expected a named field"));
                }
            },
            _ => syn::visit_mut::visit_expr_mut(self, node),
        }
    }
}

fn get_field_by_ident<'a>(
    ident_to_field: &'a HashMap<String, Field>,
    span: Span,
    ident: &Ident,
) -> syn::parse::Result<&'a Field> {
    match ident_to_field.get(&ident.to_string()) {
        Some(f) => Ok(f),
        None => Err(Error::new(
            span,
            "in a concurrent transition, any field access but be a state field",
        )),
    }
}

/// Applies the visitor `visit_field_accesses` to every Expr in the TransitionStmt.
/// Here, the visitor function `f` takes a fourth argument: a bool that indicates
/// if the given expression is from the initializer of a `#[birds_eye] let` statement
/// (i.e., the bool is false for expressions in any non-birds-eye `let` statement,
/// or in any other non-`let` statement).

pub fn visit_field_accesses_all_exprs<F>(
    ts: &mut TransitionStmt,
    f: &mut F,
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) where
    F: FnMut(&mut Vec<Error>, &Field, &mut Expr, bool) -> (),
{
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                visit_field_accesses_all_exprs(child, f, errors, ident_to_field);
            }
        }
        TransitionStmt::Let(_span, _id, lk, init_e, child) => {
            let is_birds_eye = *lk == LetKind::BirdsEye;
            visit_field_accesses(
                init_e,
                |errors, field, e| f(errors, field, e, is_birds_eye),
                errors,
                ident_to_field,
            );
            visit_field_accesses_all_exprs(child, f, errors, ident_to_field);
        }
        TransitionStmt::If(_span, cond_e, thn, els) => {
            visit_field_accesses(
                cond_e,
                |errors, field, e| f(errors, field, e, false),
                errors,
                ident_to_field,
            );
            visit_field_accesses_all_exprs(thn, f, errors, ident_to_field);
            visit_field_accesses_all_exprs(els, f, errors, ident_to_field);
        }
        TransitionStmt::Require(_, e)
        | TransitionStmt::Assert(_, e)
        | TransitionStmt::Initialize(_, _, e)
        | TransitionStmt::Update(_, _, e)
        | TransitionStmt::PostCondition(_, e)
        | TransitionStmt::Special(_, _, SpecialOp::AddElement(e))
        | TransitionStmt::Special(_, _, SpecialOp::RemoveElement(e))
        | TransitionStmt::Special(_, _, SpecialOp::HaveElement(e))
        | TransitionStmt::Special(_, _, SpecialOp::AddSome(e))
        | TransitionStmt::Special(_, _, SpecialOp::RemoveSome(e))
        | TransitionStmt::Special(_, _, SpecialOp::HaveSome(e))
        | TransitionStmt::Special(_, _, SpecialOp::DepositSome(e))
        | TransitionStmt::Special(_, _, SpecialOp::WithdrawSome(e))
        | TransitionStmt::Special(_, _, SpecialOp::GuardSome(e)) => {
            visit_field_accesses(
                e,
                |errors, field, e| f(errors, field, e, false),
                errors,
                ident_to_field,
            );
        }
    }
}

/// Returns two sets, the first consisting of all fields accessed by `self.foo`
/// in some expression OTHER than a `#[birds_eye] let` statement,
/// and the second consiting of those accesses from a `#[birds_eye] let` statement.
///
/// (Note: Even though `ts` is `&mut`, the argument isn't actually modified.
/// The only reason it is marked `&mut` is because we need to call `visit_field_accesses`,
/// and it doesn't seem worthwhile to implement two different versions for
/// `&mut` vs `&` parameters. But if we really needed to pass a `&TransitionStmt` here,
/// it could be done.)

pub fn find_all_accesses(
    ts: &mut TransitionStmt,
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) -> (HashSet<String>, HashSet<String>) {
    let mut fields_read: HashSet<String> = HashSet::new();
    let mut fields_read_birds_eye: HashSet<String> = HashSet::new();

    visit_field_accesses_all_exprs(
        ts,
        &mut |_errors, field, _e, is_birds_eye| {
            if is_birds_eye {
                fields_read_birds_eye.insert(field.ident.to_string());
            } else {
                fields_read.insert(field.ident.to_string());
            }
        },
        errors,
        ident_to_field,
    );

    (fields_read, fields_read_birds_eye)
}
