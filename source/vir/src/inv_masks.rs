use crate::ast::{BinaryOp, Constant, Dt, IntRange, SpannedTyped, Typ, TypX, Typs, UnaryOp};
use crate::context::Ctx;
use crate::messages::{Message, Span, error, error_with_label};
use crate::sst::{CallFun, Exp, ExpX};
use std::sync::Arc;

/// This is where we handle VCs to ensure that the same invariant is not opened
/// more than once at a time when the user opens nested invariants.
/// The idea is to keep a "mask" at every program point, the set of invariants
/// which are allowed to be opened.
///
/// In general, the mask set is represented by a vstd::set::Set.  As an optimization,
/// we keep track of whether the mask is empty or full, and elide certain checks in
/// those cases.

#[derive(Clone)]
pub enum MaskSet {
    Empty { span: Span },
    Full { span: Span },
    Insert { base: Box<MaskSet>, elem: Exp },
    Remove { base: Box<MaskSet>, elem: Exp },
    Arbitrary { set: Exp },
}

pub struct Assertion {
    pub err: Message,
    pub cond: Exp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MaskQueryKind {
    OpenInvariant,
    FunctionCall,
    OpenAtomicUpdate,
    UpdateFunctionCall,
    AtomicUpdateWellFormed,
}

/// The operations on invariant masks here have been phrased as generic set operations
/// to align with their theoretical model, yet to emit more precise and helpful diagnostics,
/// we make some strong assumptions about how mask sets are constucted in the current
/// implementation, in particular:
///
///  - `MaskSet::Empty` corresponds to the mask "none" of an empty list of namespaces,
///  - `MaskSet::Full` always corresponds to the mask "any",
///  - `MaskSet::Insert` is exclusively used as a list constructor, and
///  - `MaskSet::Remove` is only used when opening an invariant.
///
/// All invariant mask related checks are either subset (⊆) or membership (∈) queries.
/// An assertion of the form `A ⊆ B`, and by extention `a ∈ B = {a} ⊆ B`, can fail for
/// different reasons, we distinguish four different cases, from which we attempt to
/// abduce different causes using the assumptions listed above:
///
/// - [`err_elem_removed`]: `elem` is equal to an element removed from B,
///     meaning the user is trying to open an invariant twice.
///
/// - [`err_elem_not_member`]: `elem` is not a member of B,
///     meaning the user is trying to open an invariant that is not in the current mask.
///
/// - [`err_set_removed_elem`]: A contains an element that was removed from B,
///     meaning a mask in an open invariant block contains the open invariant.
///
/// - [`err_not_subset`]: A is not a subset of B,
///     meaning there is a conflict between two masks (fallback case).

impl MaskQueryKind {
    fn err_elem_removed(self, primary: &Span, elem: &Span, removed_elem: &Span) -> Message {
        let base_err = || {
            error_with_label(removed_elem, "possible invariant collision", "this invariant")
                .primary_label(elem, "might be the same as this invariant")
        };

        match self {
            MaskQueryKind::OpenInvariant => base_err(),

            MaskQueryKind::FunctionCall | MaskQueryKind::UpdateFunctionCall => {
                base_err().primary_label(primary, "at this call-site")
            }

            MaskQueryKind::OpenAtomicUpdate => error_with_label(
                removed_elem,
                "possible invariant collision with atomic update inner mask",
                "this invariant",
            )
            .primary_label(elem, "might be the same as this invariant")
            .primary_label(primary, "tried to open atomic update here"),

            MaskQueryKind::AtomicUpdateWellFormed => unreachable!(),
        }
    }

    fn err_elem_not_member(self, primary: &Span, elem: &Span, _set: &Span) -> Message {
        match self {
            MaskQueryKind::OpenInvariant => error_with_label(
                elem,
                "cannot show invariant namespace is in the mask given by the scope",
                "invariant opened here",
            ),

            MaskQueryKind::FunctionCall | MaskQueryKind::UpdateFunctionCall => error_with_label(
                elem,
                "cannot show this invariant namespace is allowed to be opened",
                "function might open this invariant namespace",
            )
            .primary_label(primary, "might not be allowed at this call-site"),

            MaskQueryKind::OpenAtomicUpdate => error_with_label(
                elem,
                "cannot show this invariant namespace is allowed to be opened",
                "atomic update might open this invariant namespace",
            )
            .primary_label(primary, "might not be allowed when opening atomic update here"),

            MaskQueryKind::AtomicUpdateWellFormed => error(
                primary,
                "inner mask of atomic update is not contained in the outer mask; \
                this may make it impossible to construct the atomic update",
            ),
        }
    }

    fn err_set_removed_elem(self, primary: &Span, _set: &Span, removed_elem: &Span) -> Message {
        match self {
            MaskQueryKind::OpenInvariant => unreachable!(),

            MaskQueryKind::FunctionCall | MaskQueryKind::UpdateFunctionCall => error_with_label(
                &removed_elem,
                "callee may open invariants disallowed at call-site",
                "invariant opened here",
            )
            .primary_label(primary, "might be opened again in this call"),

            MaskQueryKind::OpenAtomicUpdate => error_with_label(
                &removed_elem,
                "atomic update may open invariants disallowed at call-site",
                "invariant opened here",
            )
            .primary_label(primary, "might be opened again here"),

            MaskQueryKind::AtomicUpdateWellFormed => unreachable!(),
        }
    }

    fn err_not_subset(self, primary: &Span, left_set: &Span, right_set: &Span) -> Message {
        match self {
            MaskQueryKind::OpenInvariant => unreachable!(),

            MaskQueryKind::FunctionCall | MaskQueryKind::UpdateFunctionCall => error_with_label(
                primary,
                "callee may open invariants that caller cannot",
                "at this call-site",
            )
            .primary_label(left_set, "invariants opened by callee")
            .primary_label(right_set, "invariants opened by caller"),

            MaskQueryKind::OpenAtomicUpdate => error_with_label(
                primary,
                "atomic update may open invariants that caller cannot",
                "tried to open atomic update here",
            )
            .primary_label(left_set, "atomic update inner mask here")
            .primary_label(right_set, "invariants opened here"),

            MaskQueryKind::AtomicUpdateWellFormed => error(
                primary,
                "inner mask of atomic update is not contained in the outer mask; \
                this may make it impossible to construct the atomic update",
            ),
        }
    }
}

pub fn namespace_id_typ() -> Typ {
    Arc::new(TypX::Int(IntRange::Int))
}

pub fn namespace_set_typs() -> Typs {
    Arc::new(vec![namespace_id_typ()])
}

pub fn namespace_set_typ(ctx: &Ctx) -> Typ {
    Arc::new(TypX::Datatype(
        Dt::Path(crate::def::set_type_path(&ctx.global.vstd_crate_name)),
        namespace_set_typs(),
        Arc::new(vec![]),
    ))
}

impl MaskSet {
    pub fn span(&self) -> &Span {
        match self {
            MaskSet::Empty { span } => span,
            MaskSet::Full { span } => span,
            MaskSet::Insert { base: _, elem } => &elem.span,
            MaskSet::Remove { base: _, elem } => &elem.span,
            MaskSet::Arbitrary { set } => &set.span,
        }
    }

    pub fn to_exp(self: &Self, ctx: &Ctx) -> Exp {
        match self {
            MaskSet::Empty { span } => {
                let empty_fun =
                    CallFun::Fun(crate::def::fn_set_empty_name(&ctx.global.vstd_crate_name), None);
                let empty_expx = ExpX::Call(empty_fun, namespace_set_typs(), Arc::new(vec![]));
                let empty_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), empty_expx);
                empty_exp
            }
            MaskSet::Full { span } => {
                let full_fun =
                    CallFun::Fun(crate::def::fn_set_full_name(&ctx.global.vstd_crate_name), None);
                let full_expx = ExpX::Call(full_fun, namespace_set_typs(), Arc::new(vec![]));
                let full_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), full_expx);
                full_exp
            }
            MaskSet::Insert { base, elem } => {
                let insert_fun =
                    CallFun::Fun(crate::def::fn_set_insert_name(&ctx.global.vstd_crate_name), None);
                let insert_expx = ExpX::Call(
                    insert_fun,
                    namespace_set_typs(),
                    Arc::new(vec![base.to_exp(ctx), elem.clone()]),
                );
                let insert_exp =
                    SpannedTyped::new(&elem.span, &namespace_set_typ(ctx), insert_expx);
                insert_exp
            }
            MaskSet::Remove { base, elem } => {
                let remove_fun =
                    CallFun::Fun(crate::def::fn_set_remove_name(&ctx.global.vstd_crate_name), None);
                let remove_expx = ExpX::Call(
                    remove_fun,
                    namespace_set_typs(),
                    Arc::new(vec![base.to_exp(ctx), elem.clone()]),
                );
                let remove_exp =
                    SpannedTyped::new(&elem.span, &namespace_set_typ(ctx), remove_expx);
                remove_exp
            }
            MaskSet::Arbitrary { set } => set.clone(),
        }
    }

    pub fn empty(span: &Span) -> MaskSet {
        MaskSet::Empty { span: span.clone() }
    }

    pub fn full(span: &Span) -> MaskSet {
        MaskSet::Full { span: span.clone() }
    }

    pub fn insert(self: &Self, elem: &Exp) -> Self {
        MaskSet::Insert { base: Box::new(self.clone()), elem: elem.clone() }
    }

    pub fn remove(self: &Self, elem: &Exp) -> Self {
        MaskSet::Remove { base: Box::new(self.clone()), elem: elem.clone() }
    }

    pub fn arbitrary(exp: &Exp) -> Self {
        MaskSet::Arbitrary { set: exp.clone() }
    }

    pub fn from_list(exps: &Vec<Exp>, span: &Span) -> MaskSet {
        exps.into_iter().fold(Self::empty(span), |mask, exp| mask.insert(exp))
    }

    pub fn from_list_complement(exps: &Vec<Exp>, span: &Span) -> MaskSet {
        assert!(
            exps.is_empty(),
            "The error messages generated in this module have been designed with \
            the assumption that `opens_invariants_except` is not implemented. \
            If you remove this panic, please also adjust the diagnostics."
        );

        exps.into_iter().fold(Self::full(span), |mask, exp| mask.remove(exp))
    }

    pub fn contains(
        self: &Self,
        ctx: &Ctx,
        elem: &Exp,
        call_span: &Span,
        kind: MaskQueryKind,
    ) -> Vec<Assertion> {
        match self {
            MaskSet::Full { span: _ } => Vec::new(),
            MaskSet::Remove { base, elem: removed } => {
                let mut asserts = base.contains(ctx, elem, call_span, kind);

                let neq_exp = SpannedTyped::new(
                    &elem.span,
                    &Arc::new(TypX::Bool),
                    ExpX::Binary(BinaryOp::Ne, removed.clone(), elem.clone()),
                );

                let err = kind.err_elem_removed(call_span, &elem.span, &removed.span);
                asserts.push(Assertion { err: err, cond: neq_exp });
                asserts
            }
            _ => {
                let contains_fun = CallFun::Fun(
                    crate::def::fn_set_contains_name(&ctx.global.vstd_crate_name),
                    None,
                );

                let set_exp = self.to_exp(ctx);
                let contains_exp = SpannedTyped::new(
                    &elem.span,
                    &Arc::new(TypX::Bool),
                    ExpX::Call(
                        contains_fun,
                        namespace_set_typs(),
                        Arc::new(vec![set_exp.clone(), elem.clone()]),
                    ),
                );

                let err = kind.err_elem_not_member(call_span, &elem.span, &set_exp.span);
                vec![Assertion { err: err, cond: contains_exp }]
            }
        }
    }

    pub fn subset_of(
        self: &Self,
        ctx: &Ctx,
        other: &Self,
        call_span: &Span,
        kind: MaskQueryKind,
    ) -> Vec<Assertion> {
        match self {
            MaskSet::Empty { span: _ } => return Vec::new(),
            MaskSet::Insert { base, elem: inserted } => {
                let mut asserts = base.subset_of(ctx, other, call_span, kind);
                asserts.append(&mut other.contains(ctx, inserted, call_span, kind));
                return asserts;
            }
            _ => {}
        }

        match other {
            MaskSet::Full { span: _ } => return Vec::new(),
            MaskSet::Remove { base, elem: removed } => {
                let mut asserts = self.subset_of(ctx, base, call_span, kind);
                let mut removed_in_self = SpannedTyped::new(
                    &removed.span,
                    &Arc::new(TypX::Bool),
                    ExpX::Const(Constant::Bool(true)),
                );

                for assertion in self.contains(ctx, removed, call_span, kind) {
                    removed_in_self = SpannedTyped::new(
                        &removed.span,
                        &Arc::new(TypX::Bool),
                        ExpX::Binary(BinaryOp::And, removed_in_self, assertion.cond),
                    );
                }

                let removed_not_in_self = SpannedTyped::new(
                    &removed.span,
                    &Arc::new(TypX::Bool),
                    ExpX::Unary(UnaryOp::Not, removed_in_self),
                );

                let self_span = self.span();
                let err = kind.err_set_removed_elem(call_span, &self_span, &removed.span);
                asserts.push(Assertion { err, cond: removed_not_in_self });
                return asserts;
            }
            _ => {}
        }

        let subset_of_fun =
            CallFun::Fun(crate::def::fn_set_subset_of_name(&ctx.global.vstd_crate_name), None);
        let self_exp = self.to_exp(ctx);
        let other_exp = other.to_exp(ctx);
        let subset_of_exp = SpannedTyped::new(
            &call_span,
            &Arc::new(TypX::Bool),
            ExpX::Call(
                subset_of_fun,
                namespace_set_typs(),
                Arc::new(vec![self_exp.clone(), other_exp.clone()]),
            ),
        );

        let err = kind.err_not_subset(call_span, &self_exp.span, &other_exp.span);
        vec![Assertion { err: err, cond: subset_of_exp }]
    }
}
