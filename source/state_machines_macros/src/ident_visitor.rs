use crate::ast::{
    MonoidElt, SpecialOp, SplitKind, SubIdx, Transition, TransitionKind, TransitionStmt,
};
use crate::simplification::UPDATE_TMP_PREFIX;
use crate::util::combine_errors_or_ok;
use std::collections::HashSet;
use syn_verus::parse;
use syn_verus::spanned::Spanned;
use syn_verus::visit;
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
///
/// We also check if the user uses a field name as a variable so we can warn them
/// that they need to use `pre.{field name}`. This isn't essential, but it's pretty
/// helpful since otherwise the error message from type-checking is really awkward.

pub fn validate_idents_transition(
    trans: &Transition,
    field_names: HashSet<String>,
) -> parse::Result<()> {
    let Transition { name, kind, params, body } = trans;
    let mut bound_names = HashSet::new();
    validate_ident(name)?;
    for param in params {
        validate_ident(&param.name)?;
        bound_names.insert(param.name.to_string());
    }
    validate_idents_transition_stmt(body, *kind, &bound_names, &field_names)?;
    Ok(())
}

fn validate_idents_transition_stmt(
    ts: &TransitionStmt,
    kind: TransitionKind,
    bound_names: &HashSet<String>,
    field_names: &HashSet<String>,
) -> parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                validate_idents_transition_stmt(t, kind, bound_names, field_names)?;
            }
        }
        TransitionStmt::Split(_, split_kind, es) => {
            let mut bound_names_per_arm = vec![];
            match split_kind {
                SplitKind::Let(pat, _ty, _lk, e) => {
                    validate_idents_expr(e, kind, bound_names, field_names)?;
                    validate_idents_pat(pat, kind)?;

                    let mut bound_names1 = bound_names.clone();
                    for id in pattern_get_bound_idents(pat) {
                        bound_names1.insert(id.to_string());
                    }
                    bound_names_per_arm.push(bound_names1);
                }
                SplitKind::If(cond) => {
                    validate_idents_expr(cond, kind, bound_names, field_names)?;

                    bound_names_per_arm.push(bound_names.clone());
                    bound_names_per_arm.push(bound_names.clone());
                }
                SplitKind::Match(match_e, arms) => {
                    validate_idents_expr(match_e, kind, bound_names, field_names)?;
                    for arm in arms {
                        validate_idents_pat(&arm.pat, kind)?;

                        let mut bound_names1 = bound_names.clone();
                        for id in pattern_get_bound_idents(&arm.pat) {
                            bound_names1.insert(id.to_string());
                        }

                        match &arm.guard {
                            Some((_, guard_e)) => {
                                validate_idents_expr(&**guard_e, kind, &bound_names1, field_names)?;
                            }
                            None => {}
                        }

                        bound_names_per_arm.push(bound_names1);
                    }
                }
                SplitKind::Special(f, op, _proof, pat_opt) => {
                    validate_ident(f)?;
                    validate_idents_op(op, kind, bound_names, field_names)?;
                    match pat_opt {
                        None => {
                            bound_names_per_arm.push(bound_names.clone());
                        }
                        Some(pat) => {
                            validate_idents_pat(pat, kind)?;

                            let mut bound_names1 = bound_names.clone();
                            for id in pattern_get_bound_idents(pat) {
                                bound_names1.insert(id.to_string());
                            }
                            bound_names_per_arm.push(bound_names1);
                        }
                    }
                }
            }
            assert!(bound_names_per_arm.len() == es.len());
            for (e, bound_names) in es.iter().zip(bound_names_per_arm) {
                validate_idents_transition_stmt(e, kind, &bound_names, field_names)?;
            }
        }
        TransitionStmt::Require(_, e) => {
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
        TransitionStmt::Assert(_, e, _proof) => {
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
        TransitionStmt::SubUpdate(_, f, subs, e) => {
            validate_ident(f)?;
            for sub in subs {
                match sub {
                    SubIdx::Field(ident) => {
                        validate_ident(ident)?;
                    }
                    SubIdx::Idx(e) => {
                        validate_idents_expr(e, kind, bound_names, field_names)?;
                    }
                }
            }
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
        TransitionStmt::Update(_, f, e) | TransitionStmt::Initialize(_, f, e) => {
            validate_ident(f)?;
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
        TransitionStmt::PostCondition(_, e) => {
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
    }
    Ok(())
}

fn validate_idents_op(
    op: &SpecialOp,
    kind: TransitionKind,
    bound_names: &HashSet<String>,
    field_names: &HashSet<String>,
) -> parse::Result<()> {
    match &op.elt {
        MonoidElt::OptionSome(None) => {}
        MonoidElt::True => {}
        MonoidElt::OptionSome(Some(e))
        | MonoidElt::SingletonMultiset(e)
        | MonoidElt::SingletonSet(e)
        | MonoidElt::General(e) => {
            validate_idents_expr(e, kind, bound_names, field_names)?;
        }
        MonoidElt::SingletonKV(e1, Some(e2)) => {
            validate_idents_expr(e1, kind, bound_names, field_names)?;
            validate_idents_expr(e2, kind, bound_names, field_names)?;
        }
        MonoidElt::SingletonKV(e1, None) => {
            validate_idents_expr(e1, kind, bound_names, field_names)?;
        }
    }
    Ok(())
}

fn validate_idents_expr(
    e: &Expr,
    kind: TransitionKind,
    bound_names: &HashSet<String>,
    field_names: &HashSet<String>,
) -> parse::Result<()> {
    let mut idv = IdentVisitor::new(kind, bound_names.clone(), field_names.clone());
    idv.visit_expr(e);

    combine_errors_or_ok(idv.errors)
}

fn validate_idents_pat(pat: &Pat, kind: TransitionKind) -> parse::Result<()> {
    let mut idv = IdentVisitor::new(kind, HashSet::new(), HashSet::new());
    idv.visit_pat(pat);

    combine_errors_or_ok(idv.errors)
}

struct IdentVisitor {
    pub errors: Vec<Error>,
    pub kind: TransitionKind,
    pub bound_names: HashSet<String>,
    pub field_names: HashSet<String>,
}

impl IdentVisitor {
    pub fn new(
        kind: TransitionKind,
        bound_names: HashSet<String>,
        field_names: HashSet<String>,
    ) -> IdentVisitor {
        IdentVisitor { errors: Vec::new(), kind, bound_names, field_names }
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

    fn visit_expr(&mut self, node: &'ast Expr) {
        match node {
            Expr::Verbatim(_) => {
                // In some odd cases, syn can return parse results that use
                // Expr::Verbatim. For example, a lone underscore returns
                // an Expr::Verbatim even though I don't think that's a valid expression.
                // Anyway, in the event of something unexpected like this,
                // just error on it immediately. Later, we will assume that any
                // Expr::Verbatim node was produced by our own code.
                self.errors.push(Error::new(
                    node.span(),
                    format!("Verus does not support this expression"),
                ));
            }
            Expr::Path(expr_path) => {
                if expr_path.qself.is_none()
                    && expr_path.path.segments.len() == 1
                    && expr_path.path.leading_colon.is_none()
                {
                    let id = expr_path.path.segments[0].ident.to_string();
                    if self.field_names.contains(&id) && !self.bound_names.contains(&id) {
                        self.errors.push(Error::new(
                            node.span(),
                            format!("Use `pre.{:}` to access this field's value", id),
                        ));
                    }
                }

                visit::visit_expr(self, node);
            }
            _ => {
                visit::visit_expr(self, node);
            }
        }
    }
}

/// Validate a single identifier.
pub fn validate_ident(ident: &Ident) -> Result<(), Error> {
    for kw in vec!["post", "instance", "tmp_tuple", "tmp_e", "tmp_assert"] {
        if ident.to_string() == kw {
            return Err(Error::new(
                ident.span(),
                format!("'{kw:}' is a reserved identifier in state machine definitions"),
            ));
        }
    }

    for prefix in vec!["param_token_", "original_field_", UPDATE_TMP_PREFIX] {
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
        visit::visit_pat_ident(self, node);
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
        visit::visit_path(self, node);
    }
}
