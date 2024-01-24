//! This the module with utilities for processing a Rust Expr.
//! Formally, the codegen for the token exchange methods needs to:
//!
//!  1. Look for all `pre.field` subexpressions to determine which fields are read.
//!  2. Perform substitutions of the `pre.field` subexpressions for other expressions
//!     we construct.
//!
//! Unfortunately, attempting to treat a Rust Expr as anything other than a completely
//! opaque expression comes with a variety of technical challenges, which have to do with
//! the fact that this has to run before type-resolution and even before macro-expansion.
//!
//! In order to ensure this transformation is done correctly, we need to:
//!
//!   * Make sure that reserved identifiers like `token_foo` are not shadowed in the expressions
//!   * Disallow macros entirely, which could interfere in a number of ways.
//!     (Note: there seems to be an experimental API for expanding macros inside proc-macros,
//!     which we could look into to possibly remove this restriction!)
//!
//! Both these things are done in ident_visitor.rs.
//!
//! This is all very awkward, and it's also hard to be sure we've really handled every
//! case. The awkwardness here suggests that it would be more principled to do this
//! in VIR, or with VIR support. Unfortunately, this plan has its own problems: namely,
//! the type signatures we generate (namely the input tokens) actually depend on the
//! results of analysis (1).
//!
//! If this becomes a problem, there a few things we could do. We could avoid
//! the need for analysis (1) by requiring the user to be more explicit about which fields
//! are read. Then we could move the trickiest parts of the analysis into VIR, or at least
//! use VIR to help us enforce extra constraints we need to hold. However, I intend
//! to experiment with the current method for now, since generating all the conditions
//! in the macro has a lot of advantages for usability.

use crate::ast::{
    Field, LetKind, MonoidElt, MonoidStmtType, SpecialOp, SplitKind, SubIdx, TransitionStmt,
};
use proc_macro2::Span;
use std::collections::{HashMap, HashSet};
use syn_verus::parse;
use syn_verus::parse::Error;
use syn_verus::spanned::Spanned;
use syn_verus::visit_mut;
use syn_verus::visit_mut::VisitMut;
use syn_verus::{Expr, ExprField, ExprPath, Ident, Member};

/// Given a (Rust AST) Expr `e`, visits the subexpressions of the form
/// `pre.foo` where `foo` is a state machine field, and calls the given
/// function `f` on each one.
/// Note `f` takes a `&mut Expr` so it is allowed to modify the subexpression,
/// and it also takes a `&mut Vec<Error>` so it can produce errors.
///
/// The visitor itself may also produce errors. Specifically, it will create
/// an error if it finds a use of `pre` for any reason that is NOT an access
/// of a state machine field. For example, `pre.associated_method()` is
/// not allowed, nor is using `pre` without a "dot" access.

pub fn visit_field_accesses(
    e: &mut Expr,
    f: impl FnMut(&mut Vec<Error>, &Field, &mut Expr) -> (),
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) {
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
            Expr::Path(ExprPath { attrs: _, qself: None, path }) if path.is_ident("pre") => {
                self.errors.push(Error::new(span,
                    "in a tokenized state machine, `pre` cannot be used opaquely; it may only be used by accessing its fields"));
            }
            Expr::Field(ExprField { base, member, attrs: _, dot_token: _ }) => match &**base {
                Expr::Path(ExprPath { attrs: _, qself: None, path }) if path.is_ident("pre") => {
                    match member {
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
                    }
                }
                _ => visit_mut::visit_expr_mut(self, node),
            },
            _ => visit_mut::visit_expr_mut(self, node),
        }
    }
}

fn get_field_by_ident<'a>(
    ident_to_field: &'a HashMap<String, Field>,
    span: Span,
    ident: &Ident,
) -> parse::Result<&'a Field> {
    match ident_to_field.get(&ident.to_string()) {
        Some(f) => Ok(f),
        None => Err(Error::new(
            span,
            "in a concurrent transition, any field access must be a state field",
        )),
    }
}

/// Applies the visitor `visit_field_accesses` to every Expr in the TransitionStmt.
/// Here, the visitor function `f` takes a fourth argument: a bool that indicates
/// if the given expression is from the initializer of a `birds_eye` let-statement
/// (i.e., the bool is false for expressions in any non-birds-eye `let` statement,
/// or in any other non-`let` statement).
///
/// Corner case: we skip over the 'key' fields in GuardKV, DepositKV, and WithdrawKV,
/// (i.e., for the StorageMap case). The field is actually irrelevant for the codegen
/// of an exchange method, because a token guarded, deposited, or withdrawn is just
/// the value exactly.
/// (This ONLY applies to the StorageMap, not the ordinary Map; i.e., for
/// RemoveKV, AddKV, and HaveKV, we check the 'key' expression like you'd expect.)

pub fn visit_field_accesses_all_exprs(
    ts: &mut TransitionStmt,
    f: &mut impl FnMut(&mut Vec<Error>, &Field, &mut Expr, bool) -> (),
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                visit_field_accesses_all_exprs(child, f, errors, ident_to_field);
            }
        }
        TransitionStmt::Split(_span, split_kind, splits) => {
            match split_kind {
                SplitKind::Let(_pat, _ty, lk, init_e) => {
                    let is_birds_eye = *lk == LetKind::BirdsEye;
                    visit_field_accesses(
                        init_e,
                        |errors, field, e| f(errors, field, e, is_birds_eye),
                        errors,
                        ident_to_field,
                    );
                }
                SplitKind::If(cond_e) => {
                    visit_field_accesses(
                        cond_e,
                        |errors, field, e| f(errors, field, e, false),
                        errors,
                        ident_to_field,
                    );
                }
                SplitKind::Match(match_e, arms) => {
                    visit_field_accesses(
                        match_e,
                        |errors, field, e| f(errors, field, e, false),
                        errors,
                        ident_to_field,
                    );
                    for arm in arms.iter_mut() {
                        match &mut arm.guard {
                            Some((_, guard_e)) => {
                                visit_field_accesses(
                                    &mut **guard_e,
                                    |errors, field, e| f(errors, field, e, false),
                                    errors,
                                    ident_to_field,
                                );
                            }
                            None => {}
                        }
                    }
                }
                SplitKind::Special(_, op, _, _) => {
                    visit_special_op(op, f, errors, ident_to_field);
                }
            }
            for split in splits {
                visit_field_accesses_all_exprs(split, f, errors, ident_to_field);
            }
        }
        TransitionStmt::Require(_, e)
        | TransitionStmt::Assert(_, e, _)
        | TransitionStmt::Initialize(_, _, e)
        | TransitionStmt::Update(_, _, e)
        | TransitionStmt::PostCondition(_, e) => {
            visit_field_accesses(
                e,
                |errors, field, e| f(errors, field, e, false),
                errors,
                ident_to_field,
            );
        }
        TransitionStmt::SubUpdate(_, _, subs, e) => {
            visit_field_accesses(
                e,
                |errors, field, e| f(errors, field, e, false),
                errors,
                ident_to_field,
            );
            for sub in subs {
                match sub {
                    SubIdx::Field(_) => {}
                    SubIdx::Idx(e) => {
                        visit_field_accesses(
                            e,
                            |errors, field, e| f(errors, field, e, false),
                            errors,
                            ident_to_field,
                        );
                    }
                }
            }
        }
    }
}

fn visit_special_op(
    op: &mut SpecialOp,
    f: &mut impl FnMut(&mut Vec<Error>, &Field, &mut Expr, bool) -> (),
    errors: &mut Vec<Error>,
    ident_to_field: &HashMap<String, Field>,
) {
    match op {
        SpecialOp { stmt: _, elt: MonoidElt::OptionSome(Some(e)) }
        | SpecialOp { stmt: _, elt: MonoidElt::General(e) }
        | SpecialOp { stmt: _, elt: MonoidElt::SingletonSet(e) }
        | SpecialOp { stmt: _, elt: MonoidElt::SingletonMultiset(e) } => {
            visit_field_accesses(
                e,
                |errors, field, e| f(errors, field, e, false),
                errors,
                ident_to_field,
            );
        }
        SpecialOp { stmt: _, elt: MonoidElt::True } => {}
        SpecialOp { stmt: _, elt: MonoidElt::OptionSome(None) } => {
            // nothing to do
        }
        SpecialOp { stmt, elt: MonoidElt::SingletonKV(key, val_opt) } => {
            // We skip the processing of the key in some cases because in those cases,
            // this expresson will not appear in the signature of the exchange fn at all.
            let skip_key = match stmt {
                MonoidStmtType::Deposit => true,
                MonoidStmtType::Guard => true,
                MonoidStmtType::Withdraw => true,
                MonoidStmtType::Add(_) => false,
                MonoidStmtType::Remove => false,
                MonoidStmtType::Have => false,
            };
            if !skip_key {
                visit_field_accesses(
                    key,
                    |errors, field, e| f(errors, field, e, false),
                    errors,
                    ident_to_field,
                );
            }
            if let Some(val) = val_opt {
                visit_field_accesses(
                    val,
                    |errors, field, e| f(errors, field, e, false),
                    errors,
                    ident_to_field,
                );
            }
        }
    }
}

/// Returns two sets, the first consisting of all fields accessed by `pre.foo`
/// in some expression OTHER than a `birds_eye` let-statement,
/// and the second consiting of those accesses from a `birds_eye let-statement.
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
                fields_read_birds_eye.insert(field.name.to_string());
            } else {
                fields_read.insert(field.name.to_string());
            }
        },
        errors,
        ident_to_field,
    );

    (fields_read, fields_read_birds_eye)
}
