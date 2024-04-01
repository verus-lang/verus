use crate::messages::{error, error_with_label, Span};
use air::ast::{Expr, Stmt, StmtX};
use air::ast_util::{mk_eq, mk_false, mk_not, mk_or};
use std::sync::Arc;

/// This is where we handle VCs to ensure that the same invariant is not opened
/// more than once at a time when the user opens nested invariants.
/// The idea is to keep a "mask" at every program point, the set of invariants
/// which are allowed to be opened.
///
/// In general, the mask set takes the form
///
///    base U {x_1,...,x_n} \ {y_1,...,y_n}
///
/// The MaskSet struct, below, represents these three components as `base`, `plus`, and `minus`
/// respectively.
///
/// During SST -> AIR conversion, we track the mask set (in terms of AIR expressions) at each
/// point and generate the approriate VCs. (See sst_to_air.rs). For example:
///
///   // MASK SET: T
///   open_invariant!(&i => inner => {      // VC:    i.namespace() !in T
///     // MASK SET: T \ { i.namespace() }
///     open_invariant!(&j => inner2 => {   // VC:    j.namespace() !in T \ { i.namespace() }
///       // MASK SET: T \ { i.namespace(), j.namespace() }
///     }
///   }
///
/// When generating a VC, like `j.namespace() !in T \ { i.namespace() }`
/// we do so by generating individual assertions like
///   j.namespace() != i.namespace()
/// This lets us generate an error message that points to the two open_invariant statements.
///
/// Also note that this is designed to not generate ANY extra VCs in the common case
/// (fns that have default specifications, and no open_invariant statements).

#[derive(Clone, Debug)]
pub enum SetBase {
    Full,
    Empty,
}

#[derive(Clone, Debug)]
pub struct MaskSingleton {
    pub expr: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct MaskSet {
    pub base: SetBase,
    pub plus: Vec<MaskSingleton>,
    pub minus: Vec<MaskSingleton>,
}

impl MaskSet {
    // assert that e in self
    pub fn assert_contains(
        &self,
        span: &Span,
        e: &Expr,
        results: &mut Vec<Stmt>,
        call_span: Option<&Span>,
    ) {
        match self.base {
            SetBase::Empty => {
                let mut disjuncts = Vec::new();
                for plus_e in &self.plus {
                    disjuncts.push(mk_eq(e, &plus_e.expr));
                }
                let equals_one = mk_or(&disjuncts);
                let error = match call_span {
                    None => error_with_label(
                        span,
                        "cannot show invariant namespace is in the mask given by the function signature".to_string(),
                        "invariant opened here".to_string()),
                    Some(call_span) => error_with_label(
                        span,
                        "cannot show this invariant namespace is allowed to be opened".to_string(),
                        "function might open this invariant namespace".to_string())
                    .primary_label(call_span, "might not be allowed at this call-site"),
                };
                results.push(Arc::new(StmtX::Assert(None, error, None, equals_one)));
            }
            SetBase::Full => {}
        }

        for prev_e in &self.minus {
            let not_equal = mk_not(&mk_eq(e, &prev_e.expr));
            let mut error = error_with_label(
                &prev_e.span,
                "possible invariant collision".to_string(),
                "this invariant".to_string(),
            )
            .primary_label(span, "might be the same as this invariant".to_string());
            match call_span {
                None => {}
                Some(call_span) => {
                    error = error.primary_label(call_span, "at this call-site");
                }
            }
            results.push(Arc::new(StmtX::Assert(None, error, None, not_equal)));
        }
    }

    // assert that self \subseteq other
    pub fn assert_is_contained_in(
        &self,
        other: &MaskSet,
        call_span: &Span,
        results: &mut Vec<Stmt>,
    ) {
        match self.base {
            SetBase::Empty => {
                if self.minus.len() != 0 {
                    panic!("assert_is_contained_in: not implemented");
                }

                for e in &self.plus {
                    other.assert_contains(&e.span, &e.expr, results, Some(call_span));
                }
            }
            SetBase::Full => match other.base {
                SetBase::Empty => {
                    let fa = mk_false();
                    let error = if self.minus.len() == 0 {
                        error(
                            call_span,
                            "callee may open invariants that caller cannot (callee may open any invariant)",
                        )
                    } else {
                        error(call_span, "callee may open invariants that caller cannot")
                    };
                    results.push(Arc::new(StmtX::Assert(None, error, None, fa)));
                }
                SetBase::Full => {
                    for e in &other.minus {
                        let mut disjuncts = Vec::new();
                        for minus_e in &self.minus {
                            disjuncts.push(mk_eq(&e.expr, &minus_e.expr));
                        }
                        let equals_one = mk_or(&disjuncts);
                        let error = error_with_label(
                            &e.span,
                            "callee may open invariants disallowed at call-site".to_string(),
                            "invariant opened here".to_string(),
                        )
                        .primary_label(call_span, "might be opened again in this call".to_string());
                        results.push(Arc::new(StmtX::Assert(None, error, None, equals_one)));
                    }
                }
            },
        }
    }

    // return another set representing self \ {r}
    pub fn remove_element(&self, span: Span, r: Expr) -> MaskSet {
        let mut n = self.clone();
        n.minus.push(MaskSingleton { expr: r, span: span });
        n
    }

    pub fn full() -> MaskSet {
        MaskSet { base: SetBase::Full, plus: vec![], minus: vec![] }
    }

    pub fn empty() -> MaskSet {
        MaskSet { base: SetBase::Empty, plus: vec![], minus: vec![] }
    }

    pub fn from_list_complement(l: Vec<MaskSingleton>) -> MaskSet {
        MaskSet { base: SetBase::Full, plus: vec![], minus: l }
    }

    pub fn from_list(l: Vec<MaskSingleton>) -> MaskSet {
        MaskSet { base: SetBase::Empty, plus: l, minus: vec![] }
    }
}
