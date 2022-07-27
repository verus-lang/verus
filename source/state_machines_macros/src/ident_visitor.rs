use crate::ast::{
    MonoidElt, SpecialOp, SplitKind, SubIdx, Transition, TransitionKind, TransitionStmt,
};
use crate::simplification::UPDATE_TMP_PREFIX;
use crate::util::combine_errors_or_ok;
use syn_verus::parse;
use syn_verus::spanned::Spanned;
use syn_verus::visit::Visit;
use syn_verus::{Error, Expr, ExprMacro, Ident, Macro, Pat, PatIdent, Path, Type};

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

pub fn validate_idents_transition(trans: &Transition) -> parse::Result<()> {
    let Transition { name, kind, params, body } = trans;
    validate_ident(name)?;
    for param in params {
        validate_ident(&param.name)?;
    }
    validate_idents_transition_stmt(body, *kind)?;
    Ok(())
}

fn validate_idents_transition_stmt(ts: &TransitionStmt, kind: TransitionKind) -> parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                validate_idents_transition_stmt(t, kind)?;
            }
        }
        TransitionStmt::Split(_, split_kind, es) => {
            match split_kind {
                SplitKind::Let(pat, _ty, _lk, e) => {
                    validate_idents_pat(pat, kind)?;
                    validate_idents_expr(e, kind)?;
                }
                SplitKind::If(cond) => {
                    validate_idents_expr(cond, kind)?;
                }
                SplitKind::Match(match_e, arms) => {
                    validate_idents_expr(match_e, kind)?;
                    for arm in arms {
                        validate_idents_pat(&arm.pat, kind)?;
                        match &arm.guard {
                            Some((_, box guard_e)) => {
                                validate_idents_expr(guard_e, kind)?;
                            }
                            None => {}
                        }
                    }
                }
                SplitKind::Special(f, op, _proof, pat_opt) => {
                    validate_ident(f)?;
                    validate_idents_op(op, kind)?;
                    match pat_opt {
                        None => {}
                        Some(pat) => {
                            validate_idents_pat(pat, kind)?;
                        }
                    }
                }
            }
            for e in es {
                validate_idents_transition_stmt(e, kind)?;
            }
        }
        TransitionStmt::Require(_, e) => {
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::Assert(_, e, _proof) => {
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::SubUpdate(_, f, subs, e) => {
            validate_ident(f)?;
            for sub in subs {
                match sub {
                    SubIdx::Field(ident) => {
                        validate_ident(ident)?;
                    }
                    SubIdx::Idx(e) => {
                        validate_idents_expr(e, kind)?;
                    }
                }
            }
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::Update(_, f, e) | TransitionStmt::Initialize(_, f, e) => {
            validate_ident(f)?;
            validate_idents_expr(e, kind)?;
        }
        TransitionStmt::PostCondition(_, e) => {
            validate_idents_expr(e, kind)?;
        }
    }
    Ok(())
}

fn validate_idents_op(op: &SpecialOp, kind: TransitionKind) -> parse::Result<()> {
    match &op.elt {
        MonoidElt::OptionSome(None) => {}
        MonoidElt::True => {}
        MonoidElt::OptionSome(Some(e))
        | MonoidElt::SingletonMultiset(e)
        | MonoidElt::SingletonSet(e)
        | MonoidElt::General(e) => {
            validate_idents_expr(e, kind)?;
        }
        MonoidElt::SingletonKV(e1, Some(e2)) => {
            validate_idents_expr(e1, kind)?;
            validate_idents_expr(e2, kind)?;
        }
        MonoidElt::SingletonKV(e1, None) => {
            validate_idents_expr(e1, kind)?;
        }
    }
    Ok(())
}

fn validate_idents_expr(e: &Expr, kind: TransitionKind) -> parse::Result<()> {
    let mut idv = IdentVisitor::new(kind);
    idv.visit_expr(e);

    combine_errors_or_ok(idv.errors)
}

fn validate_idents_pat(pat: &Pat, kind: TransitionKind) -> parse::Result<()> {
    let mut idv = IdentVisitor::new(kind);
    idv.visit_pat(pat);

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

    for prefix in vec!["token_", "original_field_", UPDATE_TMP_PREFIX] {
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

/// Get all identifiers bound by the pattern

pub fn pattern_get_bound_idents(pat: &Pat) -> Vec<Ident> {
    let mut piv = PatIdentVisitor::new();
    piv.visit_pat(pat);
    piv.idents
}

struct PatIdentVisitor {
    pub idents: Vec<Ident>,
}

impl PatIdentVisitor {
    pub fn new() -> PatIdentVisitor {
        PatIdentVisitor { idents: Vec::new() }
    }
}

impl<'ast> Visit<'ast> for PatIdentVisitor {
    fn visit_pat_ident(&mut self, node: &'ast PatIdent) {
        let ident = node.ident.clone();
        if !self.idents.contains(&ident) {
            self.idents.push(ident);
        }
    }
}

/// Error if the type contains a `super::...` path.

pub fn error_on_super_path(ty: &Type) -> parse::Result<()> {
    let mut sv = SuperVisitor { errors: Vec::new() };
    sv.visit_type(ty);
    combine_errors_or_ok(sv.errors)
}

struct SuperVisitor {
    pub errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for SuperVisitor {
    fn visit_macro(&mut self, node: &'ast Macro) {
        self.errors
            .push(Error::new(node.span(), format!("state machine error: macro not allowed here")));
    }

    fn visit_path(&mut self, node: &'ast Path) {
        if node.segments[0].ident.to_string() == "super" {
            self.errors.push(Error::new(
                node.span(),
                format!("state machine error: `super::` path not allowed here"),
            ));
        }
    }
}
