use crate::messages::{Span};
use crate::ast::{IntRange, SpannedTyped, Typ, TypX, Dt};
use crate::context::Ctx;
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
    Insert { span: Span, base: Box<MaskSet>, elem: Exp },
    Remove { span: Span, base: Box<MaskSet>, elem: Exp },

    // Not used at the moment, will be used when we add syntax and support
    // for specifying an std::Set expression as the mask.
    // Arbitrary { set: Exp },
}

fn namespace_set_typs() -> Arc<Vec<Typ>> {
    Arc::new(vec![Arc::new(TypX::Int(IntRange::Int))])
}

fn namespace_set_typ(ctx: &Ctx) -> Arc<TypX> {
    Arc::new(TypX::Datatype(Dt::Path(crate::def::set_type_path(&ctx.global.vstd_crate_name)), namespace_set_typs(), Arc::new(vec![])))
}

impl MaskSet {
    pub fn to_exp(self: &Self, ctx: &Ctx) -> Exp {
        match self {
            MaskSet::Empty { span } => {
                let empty_fun = CallFun::Fun(crate::def::fn_set_empty_name(&ctx.global.vstd_crate_name), None);
                let empty_expx = ExpX::Call(empty_fun, namespace_set_typs(), Arc::new(vec![]));
                let empty_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), empty_expx);
                empty_exp
            },
            MaskSet::Full { span } => {
                let full_fun = CallFun::Fun(crate::def::fn_set_full_name(&ctx.global.vstd_crate_name), None);
                let full_expx = ExpX::Call(full_fun, namespace_set_typs(), Arc::new(vec![]));
                let full_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), full_expx);
                full_exp
            },
            MaskSet::Insert { span, base, elem } => {
                let insert_fun = CallFun::Fun(crate::def::fn_set_insert_name(&ctx.global.vstd_crate_name), None);
                let insert_expx = ExpX::Call(insert_fun, namespace_set_typs(), Arc::new(vec![base.to_exp(ctx), elem.clone()]));
                let insert_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), insert_expx);
                insert_exp
            },
            MaskSet::Remove { span, base, elem } => {
                let remove_fun = CallFun::Fun(crate::def::fn_set_remove_name(&ctx.global.vstd_crate_name), None);
                let remove_expx = ExpX::Call(remove_fun, namespace_set_typs(), Arc::new(vec![base.to_exp(ctx), elem.clone()]));
                let remove_exp = SpannedTyped::new(&span, &namespace_set_typ(ctx), remove_expx);
                remove_exp
            },
            // MaskSet::Arbitrary { set } => { set.clone() },
        }
    }

    pub fn empty(span: &Span) -> MaskSet {
        MaskSet::Empty{ span: span.clone() }
    }

    pub fn full(span: &Span) -> MaskSet {
        MaskSet::Full{ span: span.clone() }
    }

    pub fn insert(self: &Self, elem: &Exp, span: &Span) -> Self {
        MaskSet::Insert{ span: span.clone(), base: Box::new(self.clone()), elem: elem.clone() }
    }

    pub fn remove(self: &Self, elem: &Exp, span: &Span) -> Self {
        MaskSet::Remove{ span: span.clone(), base: Box::new(self.clone()), elem: elem.clone() }
    }

    // pub fn arbitrary(exp: &Exp) -> Self {
    //     MaskSet::Arbitrary{ set: exp.clone() }
    // }

    pub fn from_list(exps: &Vec<Exp>, span: &Span) -> MaskSet {
        let mut mask = Self::empty(span);

        for e in exps.iter() {
            mask = mask.insert(e, span)
        }

        mask
    }

    pub fn from_list_complement(exps: &Vec<Exp>, span: &Span) -> MaskSet {
        let mut mask = Self::full(span);

        for e in exps.iter() {
            mask = mask.remove(e, span)
        }

        mask
    }

    pub fn contains(self: &Self, ctx: &Ctx, elem: &Exp, span: &Span) -> Option<Exp> {
        match self {
            MaskSet::Full { span: _ } => None,
            _ => {
                let contains_fun = CallFun::Fun(crate::def::fn_set_contains_name(&ctx.global.vstd_crate_name), None);
                let contains_expx = ExpX::Call(contains_fun, namespace_set_typs(), Arc::new(vec![self.to_exp(ctx), elem.clone()]));
                let contains_exp = SpannedTyped::new(&span, &Arc::new(TypX::Bool), contains_expx);

                Some(contains_exp)
            },
        }
    }

    pub fn subset_of(self: &Self, ctx: &Ctx, other: &Self, span: &Span) -> Option<Exp> {
        match self {
            MaskSet::Empty { span: _ } => None,
            _ => match other {
                MaskSet::Full { span: _ } => None,
                _ => {
                    let subset_of_fun = CallFun::Fun(crate::def::fn_set_subset_of_name(&ctx.global.vstd_crate_name), None);
                    let subset_of_expx = ExpX::Call(subset_of_fun, namespace_set_typs(), Arc::new(vec![self.to_exp(ctx), other.to_exp(ctx)]));
                    let subset_of_exp = SpannedTyped::new(&span, &Arc::new(TypX::Bool), subset_of_expx);

                    Some(subset_of_exp)
                },
            },
        }
    }
}
