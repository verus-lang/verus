use crate::ast::{SpecialOp, Transition, TransitionStmt};
use crate::util::combine_errors_or_ok;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Error, Expr, ExprMacro, Ident};

/// Error if any identifiers conflict with reserved IDs used by macro expanion.
///
/// This validation should be applied to:
///  * the entire body of any transition definition
///  * any field name
///
/// Since macros might introduce arbitrary identifiers or otherwise interfere with
/// our checks or transformations, we also disallow macros entirely.
/// (See the more detailed explanation in `field_access_visitor.rs`.)

pub fn validate_idents_transition(trans: &Transition) -> syn::parse::Result<()> {
    let Transition { name, kind: _, params, body } = trans;
    validate_ident(name)?;
    for param in params {
        validate_ident(&param.name)?;
    }
    validate_idents_transition_stmt(body)?;
    Ok(())
}

fn validate_idents_transition_stmt(ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                validate_idents_transition_stmt(t)?;
            }
        }
        TransitionStmt::Let(_, ident, _lk, e, child) => {
            validate_ident(ident)?;
            validate_idents_expr(e)?;
            validate_idents_transition_stmt(child)?;
        }
        TransitionStmt::If(_, cond, thn, els) => {
            validate_idents_expr(cond)?;
            validate_idents_transition_stmt(thn)?;
            validate_idents_transition_stmt(els)?;
        }
        TransitionStmt::Require(_, e) => {
            validate_idents_expr(e)?;
        }
        TransitionStmt::Assert(_, e, _proof) => {
            validate_idents_expr(e)?;
        }
        TransitionStmt::Update(_, f, e) | TransitionStmt::Initialize(_, f, e) => {
            validate_ident(f)?;
            validate_idents_expr(e)?;
        }
        TransitionStmt::Special(_, f, op, _proof) => {
            validate_ident(f)?;
            validate_idents_op(op)?;
        }
        TransitionStmt::PostCondition(_, e) => {
            validate_idents_expr(e)?;
        }
    }
    Ok(())
}

fn validate_idents_op(op: &SpecialOp) -> syn::parse::Result<()> {
    match op {
        SpecialOp::AddSome(e)
        | SpecialOp::RemoveSome(e)
        | SpecialOp::HaveSome(e)
        | SpecialOp::AddElement(e)
        | SpecialOp::RemoveElement(e)
        | SpecialOp::HaveElement(e)
        | SpecialOp::DepositSome(e)
        | SpecialOp::WithdrawSome(e)
        | SpecialOp::GuardSome(e) => {
            validate_idents_expr(e)?;
        }

        SpecialOp::DepositKV(e1, e2)
        | SpecialOp::WithdrawKV(e1, e2)
        | SpecialOp::GuardKV(e1, e2)
        | SpecialOp::AddKV(e1, e2)
        | SpecialOp::RemoveKV(e1, e2)
        | SpecialOp::HaveKV(e1, e2) => {
            validate_idents_expr(e1)?;
            validate_idents_expr(e2)?;
        }
    }
    Ok(())
}

fn validate_idents_expr(e: &Expr) -> syn::parse::Result<()> {
    let mut idv = IdentVisitor::new();
    idv.visit_expr(e);

    combine_errors_or_ok(idv.errors)
}

struct IdentVisitor {
    pub errors: Vec<Error>,
}

impl IdentVisitor {
    pub fn new() -> IdentVisitor {
        IdentVisitor { errors: Vec::new() }
    }
}

impl<'ast> Visit<'ast> for IdentVisitor {
    fn visit_ident(&mut self, node: &'ast Ident) {
        match validate_ident(node) {
            Err(err) => self.errors.push(err),
            Ok(()) => {}
        }
    }

    fn visit_expr_macro(&mut self, node: &'ast ExprMacro) {
        self.errors
            .push(Error::new(node.span(), format!("macro not allowed in transition expression")));
    }
}

/// Validate a single identifier.
pub fn validate_ident(ident: &Ident) -> Result<(), Error> {
    for kw in vec!["post", "instance", "tmp_tuple", "tmp_e"] {
        if ident.to_string() == kw {
            return Err(Error::new(
                ident.span(),
                format!("'{kw:}' is a reserved identifier in state machine definitions"),
            ));
        }
    }

    for prefix in vec!["token_", "original_field_", "update_tmp_"] {
        if ident.to_string().starts_with(prefix) {
            return Err(Error::new(
                ident.span(),
                format!(
                    "identifiers starting with '{prefix:}' are reserved identifiers in state machine definitions"
                ),
            ));
        }
    }

    Ok(())
}
