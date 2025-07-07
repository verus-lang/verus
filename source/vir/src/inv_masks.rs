use crate::ast::{BinaryOp, Constant, Dt, IntRange, SpannedTyped, Typ, TypX, Typs, UnaryOp};
use crate::context::Ctx;
use crate::messages::{Message, Span, error_with_label};
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
        let mut mask = Self::empty(span);

        for e in exps.iter() {
            mask = mask.insert(e)
        }

        mask
    }

    pub fn from_list_complement(exps: &Vec<Exp>, span: &Span) -> MaskSet {
        let mut mask = Self::full(span);

        for e in exps.iter() {
            mask = mask.remove(e)
        }

        mask
    }

    fn contains_internal(
        self: &Self,
        ctx: &Ctx,
        elem: &Exp,
        call_span: Option<&Span>,
    ) -> Vec<Assertion> {
        match self {
            MaskSet::Full { span: _ } => vec![],
            MaskSet::Remove { base, elem: removed } => {
                let mut asserts = base.contains_internal(ctx, elem, call_span);

                let neq_expx = ExpX::Binary(BinaryOp::Ne, removed.clone(), elem.clone());
                let neq_exp = SpannedTyped::new(&elem.span, &Arc::new(TypX::Bool), neq_expx);

                let mut err = error_with_label(
                    &removed.span,
                    "possible invariant collision",
                    "this invariant",
                )
                .primary_label(&elem.span, "might be the same as this invariant");
                match call_span {
                    None => {}
                    Some(call_span) => {
                        err = err.primary_label(call_span, "at this call-site");
                    }
                }

                asserts.push(Assertion { err: err, cond: neq_exp });
                asserts
            }
            _ => {
                let contains_fun = CallFun::Fun(
                    crate::def::fn_set_contains_name(&ctx.global.vstd_crate_name),
                    None,
                );
                let contains_expx = ExpX::Call(
                    contains_fun,
                    namespace_set_typs(),
                    Arc::new(vec![self.to_exp(ctx), elem.clone()]),
                );
                let contains_exp =
                    SpannedTyped::new(&elem.span, &Arc::new(TypX::Bool), contains_expx);

                let err = match call_span {
                    None => error_with_label(
                        &elem.span,
                        "cannot show invariant namespace is in the mask given by the function signature",
                        "invariant opened here",
                    ),
                    Some(call_span) => error_with_label(
                        &elem.span,
                        "cannot show this invariant namespace is allowed to be opened",
                        "function might open this invariant namespace",
                    )
                    .primary_label(call_span, "might not be allowed at this call-site"),
                };

                vec![Assertion { err: err, cond: contains_exp }]
            }
        }
    }

    pub fn contains(self: &Self, ctx: &Ctx, elem: &Exp) -> Vec<Assertion> {
        self.contains_internal(ctx, elem, None)
    }

    pub fn subset_of(self: &Self, ctx: &Ctx, other: &Self, call_span: &Span) -> Vec<Assertion> {
        match self {
            MaskSet::Empty { span: _ } => vec![],
            MaskSet::Insert { base, elem: inserted } => {
                let mut asserts = base.subset_of(ctx, other, call_span);
                asserts.append(&mut other.contains_internal(ctx, inserted, Some(call_span)));
                asserts
            }
            _ => match other {
                MaskSet::Full { span: _ } => vec![],
                MaskSet::Remove { base, elem: removed } => {
                    let mut asserts = self.subset_of(ctx, base, call_span);

                    let mut removed_in_self = SpannedTyped::new(
                        &removed.span,
                        &Arc::new(TypX::Bool),
                        ExpX::Const(Constant::Bool(true)),
                    );
                    for assertion in self.contains_internal(ctx, removed, Some(call_span)) {
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
                    asserts.push(Assertion {
                        err: error_with_label(
                            &removed.span,
                            "callee may open invariants disallowed at call-site",
                            "invariant opened here",
                        )
                        .primary_label(call_span, "might be opened again in this call"),
                        cond: removed_not_in_self,
                    });
                    asserts
                }
                _ => {
                    let subset_of_fun = CallFun::Fun(
                        crate::def::fn_set_subset_of_name(&ctx.global.vstd_crate_name),
                        None,
                    );
                    let self_exp = self.to_exp(ctx);
                    let other_exp = other.to_exp(ctx);
                    let subset_of_expx = ExpX::Call(
                        subset_of_fun,
                        namespace_set_typs(),
                        Arc::new(vec![self_exp.clone(), other_exp.clone()]),
                    );
                    let subset_of_exp =
                        SpannedTyped::new(&call_span, &Arc::new(TypX::Bool), subset_of_expx);

                    let err = error_with_label(
                        call_span,
                        "callee may open invariants that caller cannot",
                        "at this call-site",
                    )
                    .primary_label(&self_exp.span, "invariants opened by callee")
                    .primary_label(&other_exp.span, "invariants opened by caller");

                    vec![Assertion { err: err, cond: subset_of_exp }]
                }
            },
        }
    }
}
