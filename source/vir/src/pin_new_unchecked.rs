//! Extra restrictions on calls to `Pin::new_unchecked`.
//!
//! `Pin::new_unchecked` is an unsafe function: the caller must guarantee that the pointee
//! is never moved again (until it is dropped). Verus doesn't model this obligation in the
//! function's spec. Instead, we syntactically restrict calls to it, so that the obligation
//! is guaranteed to hold:
//!
//!  - The argument must be a mutable borrow of a local variable of the function,
//!    i.e., `Pin::new_unchecked(&mut x)`. The variable cannot be a local of a closure
//!    (i.e., the call cannot be inside a closure).
//!  - There can be no move out of `x` (or any sub-place of `x`) anywhere in the function.
//!    For this purpose, `ReadKind::Unused` counts as a move.
//!  - There can be no mutable borrow of `x` (or any sub-place of `x`) anywhere in the
//!    function, other than the borrows that are passed directly to `Pin::new_unchecked`.
//!    (Otherwise, e.g., `core::mem::swap(&mut x, &mut y)` could move the pinned value.)
//!    This includes `ref mut` bindings in patterns.
//!  - `x` cannot be captured by any closure.
//!
//! This check needs to run after mode-checking, because it relies on the final read kinds
//! computed by modes.rs (e.g., reads in ghost code are finalized as `Spec` and are not moves),
//! and because modes.rs resolves each `ImplicitReborrowOrSpecRead` into either a mutable
//! borrow or a spec read.

use crate::ast::{
    ByRef, CallTarget, CtorUpdateTail, Datatype, Expr, ExprX, Fun, Function, Path, Pattern, Place,
    PlaceX, ReadKind, Stmt, StmtX, Typ, UnfinalizedReadKind, VarIdent, VirErr,
};
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::messages::{Span, error};
use crate::resolution_inference::ResolutionInfo;
use std::collections::HashMap;

const PIN_ERROR_MSG: &str = "possible safety violation: unable to check that the argument to `Pin::new_unchecked` obeys pinning restrictions";

const COND_ARG: &str =
    "the argument must be a mutable borrow of a local variable, e.g., `Pin::new_unchecked(&mut x)`";
const COND_NOT_IN_CLOSURE: &str = "the call must not be inside a closure";
const COND_NO_MOVE: &str =
    "the local variable must not be moved (in whole or in part) anywhere in the function";
const COND_NO_MUT_BORROW: &str = "the local variable must not be mutably borrowed (in whole or in part) anywhere in the function, other than by `Pin::new_unchecked`";
const COND_NO_CAPTURE: &str = "the local variable must not be captured by any closure";

const CONDITIONS: [&str; 5] =
    [COND_ARG, COND_NOT_IN_CLOSURE, COND_NO_MOVE, COND_NO_MUT_BORROW, COND_NO_CAPTURE];

/// Builds the error, with one help message listing all the conditions and a second
/// help message naming the specific condition that is violated.
fn pin_error(span: &Span, violated: &str) -> VirErr {
    let mut help = "Verus requires the following conditions to be met:".to_string();
    for c in CONDITIONS {
        help += "\n  - ";
        help += c;
    }
    error(span, PIN_ERROR_MSG).help(help).help(format!("this condition is violated: {violated}"))
}

struct Visitor<'a> {
    info: &'a ResolutionInfo,
    datatypes: &'a HashMap<Path, Datatype>,
    functions: &'a HashMap<Fun, Function>,
    /// Number of NonSpecClosures we are currently inside
    closure_depth: usize,
    /// Locals passed (via `&mut x`) to `Pin::new_unchecked`, with the span of the call
    pinned: Vec<(VarIdent, Span)>,
    /// Locals that are moved from (in whole or in part), with the span of the first move
    moved: HashMap<VarIdent, Span>,
    /// Locals that are mutably borrowed (in whole or in part), with the span of the first borrow,
    /// not counting the borrows passed directly to `Pin::new_unchecked`
    mut_borrowed: HashMap<VarIdent, Span>,
    /// Locals that are referenced from within a closure, with the span of the first reference
    captured: HashMap<VarIdent, Span>,
}

fn place_root_local(place: &Place) -> Option<&VarIdent> {
    match &place.x {
        PlaceX::Local(x) => Some(x),
        PlaceX::Field(_, p)
        | PlaceX::DerefMut(p)
        | PlaceX::ModeUnwrap(p, _)
        | PlaceX::Index(p, _, _, _)
        | PlaceX::WithExpr(_, p)
        | PlaceX::UserDefinedTypInvariantObligation(p, _) => place_root_local(p),
        PlaceX::Temporary(_) => None,
    }
}

impl<'a> Visitor<'a> {
    fn is_pin_new_unchecked(&self, fun: &Fun) -> bool {
        self.functions.get(fun).is_some_and(|f| f.x.attrs.is_pin_new_unchecked)
    }

    /// Is this read a move? Note that unlike in resolution_inference,
    /// `Unused` is conservatively treated as a move here.
    fn is_move_or_unused(&self, rk: &UnfinalizedReadKind) -> bool {
        match rk.preliminary_kind {
            ReadKind::Move(_) | ReadKind::Unused => match self.info.read_kind_finals.get(&rk.id) {
                Some(ReadKind::Move(_) | ReadKind::Unused) | None => true,
                Some(ReadKind::Copy | ReadKind::ImmutBor)
                | Some(ReadKind::Spec | ReadKind::SpecAfterBorrow) => false,
            },
            ReadKind::Copy | ReadKind::ImmutBor | ReadKind::Spec | ReadKind::SpecAfterBorrow => {
                false
            }
        }
    }

    /// Returns (does the pattern move from the matched place?,
    ///          does the pattern mutably borrow from the matched place?)
    fn pattern_moves_and_muts(&self, pattern: &Pattern) -> (bool, bool) {
        // Any errors here will be reported by resolution_inference
        let mut errors = vec![];
        let projs = crate::resolution_inference::moves_and_muts_for_pattern(
            pattern,
            self.datatypes,
            &self.info.var_modes,
            &mut errors,
        );
        (
            projs.iter().any(|(_, by_ref)| *by_ref == ByRef::No),
            projs.iter().any(|(_, by_ref)| *by_ref == ByRef::MutRef),
        )
    }

    fn record_pattern(&mut self, pattern: &Pattern, place: &Place, span: &Span) {
        let (moves, muts) = self.pattern_moves_and_muts(pattern);
        if moves {
            self.record_move(place, span);
        }
        if muts {
            self.record_mut_borrow(place, span);
        }
    }

    fn record_mut_borrow(&mut self, place: &Place, span: &Span) {
        if let Some(x) = place_root_local(place) {
            self.mut_borrowed.entry(x.clone()).or_insert_with(|| span.clone());
        }
    }

    fn record_move(&mut self, place: &Place, span: &Span) {
        if let Some(x) = place_root_local(place) {
            self.moved.entry(x.clone()).or_insert_with(|| span.clone());
        }
    }

    fn record_capture(&mut self, x: &VarIdent, span: &Span) {
        if self.closure_depth > 0 {
            self.captured.entry(x.clone()).or_insert_with(|| span.clone());
        }
    }

    fn check_call(&mut self, expr: &Expr, args: &[Expr]) -> Result<(), VirErr> {
        if self.closure_depth > 0 {
            return Err(pin_error(&expr.span, COND_NOT_IN_CLOSURE)
                .primary_label(&expr.span, "`Pin::new_unchecked` is called inside a closure"));
        }
        let arg_err = || {
            pin_error(&expr.span, COND_ARG).primary_label(
                &expr.span,
                "the argument is not a mutable borrow of a local variable",
            )
        };
        if args.len() != 1 {
            return Err(arg_err());
        }
        match &args[0].x {
            ExprX::BorrowMut(place) | ExprX::TwoPhaseBorrowMut(place) => match &place.x {
                PlaceX::Local(x) => {
                    self.pinned.push((x.clone(), expr.span.clone()));
                    Ok(())
                }
                _ => Err(arg_err()),
            },
            _ => Err(arg_err()),
        }
    }
}

impl<'a> AstVisitor<Walk, VirErr, NoScoper> for Visitor<'a> {
    fn visit_typ(&mut self, _typ: &Typ) -> Result<(), VirErr> {
        Ok(())
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        // This match is intentionally exhaustive, so that any new ExprX variant
        // (in particular, any variant with a Place child) must be considered here.
        match &expr.x {
            ExprX::Call { target, args, post_args, body } => {
                if let CallTarget::Fun(_, fun, _, _, _) = target {
                    if self.is_pin_new_unchecked(fun) {
                        self.check_call(expr, args)?;
                        // check_call ensures the only argument is `&mut x` for a local `x`.
                        // Don't recurse into it, since this borrow is the one that's allowed.
                        self.visit_opt_expr(post_args)?;
                        self.visit_opt_expr(body)?;
                        return Ok(());
                    }
                }
            }

            // Variants with Place children
            ExprX::ReadPlace(place, rk) => {
                if self.is_move_or_unused(rk) {
                    self.record_move(place, &expr.span);
                }
            }
            ExprX::Ctor(_, _, _, update) => {
                if let Some(CtorUpdateTail { place, taken_fields }) = update {
                    if taken_fields.iter().any(|(_, rk)| self.is_move_or_unused(rk)) {
                        self.record_move(place, &expr.span);
                    }
                }
            }
            ExprX::Match(place, arms, _) => {
                for arm in arms.iter() {
                    self.record_pattern(&arm.x.pattern, place, &expr.span);
                }
            }
            ExprX::BorrowMut(place)
            | ExprX::TwoPhaseBorrowMut(place)
            | ExprX::BorrowMutTracked(place)
            | ExprX::ImplicitReborrowOrSpecRead(place, _, _) => {
                self.record_mut_borrow(place, &expr.span);
            }
            ExprX::Assign { place: _, rhs: _, op: _, typ: _, resolve: _ } => {
                // Assigning to the pinned place (or a sub-place) drops the old value in place,
                // which is permitted by the pinning contract.
            }
            ExprX::MatchGuardFreeze(..) => {
                return Err(crate::messages::internal_error(
                    &expr.span,
                    "MatchGuardFreeze shouldn't be created yet",
                ));
            }

            // Variables and closures
            ExprX::Var(x) | ExprX::VarAt(x, _) => {
                self.record_capture(x, &expr.span);
            }
            ExprX::NonSpecClosure { .. } => {
                self.closure_depth += 1;
                let r = self.visit_expr_rec(expr);
                self.closure_depth -= 1;
                return r;
            }

            // Variants with no Place children and nothing to check
            ExprX::Const(_)
            | ExprX::ConstVar(..)
            | ExprX::StaticVar(_)
            | ExprX::NullaryOpr(_)
            | ExprX::Unary(..)
            | ExprX::UnaryOpr(..)
            | ExprX::Logical(..)
            | ExprX::Binary(..)
            | ExprX::BinaryOpr(..)
            | ExprX::Multi(..)
            | ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::ArrayLiteral(_)
            | ExprX::ExecFnByName(_)
            | ExprX::Choose { .. }
            | ExprX::WithTriggers { .. }
            | ExprX::Fuel(..)
            | ExprX::RevealString(_)
            | ExprX::RevealByteString(_)
            | ExprX::Header(_)
            | ExprX::AssertAssume { .. }
            | ExprX::AssertAssumeUserDefinedTypeInvariant { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..)
            | ExprX::If(..)
            | ExprX::Loop { .. }
            | ExprX::OpenInvariant(..)
            | ExprX::TryOpenAtomicUpdate(..)
            | ExprX::AtomicUpdateInitDummy
            | ExprX::Atomically(..)
            | ExprX::Update(_)
            | ExprX::InvMask(_)
            | ExprX::Return(_)
            | ExprX::BreakOrContinue { .. }
            | ExprX::Ghost { .. }
            | ExprX::ProofInSpec(_)
            | ExprX::Block(..)
            | ExprX::AirStmt(_)
            | ExprX::NeverToAny(_)
            | ExprX::Nondeterministic
            | ExprX::EvalAndResolve(..)
            | ExprX::Old(_)
            | ExprX::ForcePureAndNonProphetic(..)
            | ExprX::Await(_)
            | ExprX::ShrRefStructWrap(..) => {}
        }
        self.visit_expr_rec(expr)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), VirErr> {
        if let StmtX::Decl { pattern, init: Some(place), .. } = &stmt.x {
            self.record_pattern(pattern, place, &stmt.span);
        }
        self.visit_stmt_rec(stmt)
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
        if let PlaceX::Local(x) = &place.x {
            self.record_capture(x, &place.span);
        }
        self.visit_place_rec(place)
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<(), VirErr> {
        self.visit_pattern_rec(pattern)
    }
}

pub(crate) fn check_function(
    function: &Function,
    info: &ResolutionInfo,
    datatypes: &HashMap<Path, Datatype>,
    functions: &HashMap<Fun, Function>,
) -> Result<(), VirErr> {
    let Some(body) = &function.x.body else {
        return Ok(());
    };
    let mut visitor = Visitor {
        info,
        datatypes,
        functions,
        closure_depth: 0,
        pinned: vec![],
        moved: HashMap::new(),
        mut_borrowed: HashMap::new(),
        captured: HashMap::new(),
    };
    visitor.visit_expr(body)?;

    for (x, call_span) in visitor.pinned.iter() {
        let name = crate::def::user_local_name(x);
        let violation = if let Some(span) = visitor.moved.get(x) {
            Some((span, format!("`{name}` is moved here"), COND_NO_MOVE))
        } else if let Some(span) = visitor.mut_borrowed.get(x) {
            Some((span, format!("`{name}` is mutably borrowed here"), COND_NO_MUT_BORROW))
        } else if let Some(span) = visitor.captured.get(x) {
            Some((span, format!("`{name}` is captured by a closure here"), COND_NO_CAPTURE))
        } else {
            None
        };
        if let Some((span, label, cond)) = violation {
            return Err(pin_error(call_span, cond)
                .primary_label(call_span, format!("`{name}` is pinned here"))
                .secondary_label(span, label));
        }
    }
    Ok(())
}
