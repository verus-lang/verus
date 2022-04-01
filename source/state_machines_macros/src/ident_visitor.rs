use crate::ast::{MonoidElt, SpecialOp, Transition, TransitionKind, TransitionStmt};
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
///
/// Also errors if the user incorrectly uses `self` or `pre` (for the sake of a nicer
/// error message).

pub fn validate_idents_transition(trans: &Transition) -> syn::parse::Result<()> {
    let Transition { name, kind, params, body } = trans;
    validate_ident(name)?;
    for param in params {
        validate_ident(&param.name)?;
    }
    validate_idents_transition_stmt(body, *kind)?;
    Ok(())
}

fn validate_idents_transition_stmt(
    ts: &TransitionStmt,
    kind: TransitionKind,
) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                validate_idents_transition_stmt(t, kind)?;
            }
        }
        TransitionStmt::Let(_, ident, _ty, _lk, e, child) => {
            validate_ident(ident)?;
            validate_idents_expr(e, kind)?;
            validate_idents_transition_stmt(child, kind)?;
        }
        TransitionStmt::If(_, cond, thn, els) => {
            validate_idents_expr(cond, kind)?;
            validate_idents_transition_stmt(thn, kind)?;
            validate_idents_transition_stmt(els, kind)?;
        }
        TransitionStmt::Require(_, e) => {
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::Assert(_, e, _proof) => {
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::Update(_, f, e) | TransitionStmt::Initialize(_, f, e) => {
            validate_ident(f)?;
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::Special(_, f, op, _proof) => {
            validate_ident(f)?;
            validate_idents_op(op, kind)?;
        }
        TransitionStmt::PostCondition(_, e) => {
            validate_idents_expr(e, kind)?;
        }
    }
    Ok(())
}

fn validate_idents_op(op: &SpecialOp, kind: TransitionKind) -> syn::parse::Result<()> {
    match &op.elt {
        MonoidElt::OptionSome(e) | MonoidElt::SingletonMultiset(e) | MonoidElt::General(e) => {
            validate_idents_expr(e, kind)?;
        }
        MonoidElt::SingletonKV(e1, e2) => {
            validate_idents_expr(e1, kind)?;
            validate_idents_expr(e2, kind)?;
        }
    }
    Ok(())
}

fn validate_idents_expr(e: &Expr, kind: TransitionKind) -> syn::parse::Result<()> {
    let mut idv = IdentVisitor::new(kind);
    idv.visit_expr(e);

    combine_errors_or_ok(idv.errors)
}

struct IdentVisitor {
    pub errors: Vec<Error>,
    pub kind: TransitionKind,
}

impl IdentVisitor {
    pub fn new(kind: TransitionKind) -> IdentVisitor {
        IdentVisitor { errors: Vec::new(), kind }
    }
}

impl<'ast> Visit<'ast> for IdentVisitor {
    fn visit_ident(&mut self, node: &'ast Ident) {
        if node.to_string() == "post" {
            self.errors.push(Error::new(
                node.span(),
                "cannot refer directly to `post` in a transition definition",
            ));
        } else if node.to_string() == "pre" {
            if self.kind == TransitionKind::Init {
                self.errors.push(Error::new(node.span(),
                    "cannot refer to `pre` in an 'init' routine; there is no previous state to refer to"));
            }
        } else if node.to_string() == "self" {
            self.errors.push(Error::new(node.span(),
                  "identifier `self` is meaningless in transition definition; use `pre` to refer to the previous state (in non-init transitions)"));
        } else {
            match validate_ident(node) {
                Err(err) => self.errors.push(err),
                Ok(()) => {}
            }
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
