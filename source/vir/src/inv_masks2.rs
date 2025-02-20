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

enum Special {
    Empty,
    Full,
    Arbitrary,
}

pub struct MaskSet {
    set: crate::sst::Exp,
    spec: Special,
}

fn namespace_set_typs() -> Arc<Vec<Typ>> {
    Arc::new(vec![Arc::new(TypX::Int(IntRange::Int))])
}

fn namespace_set_typ(ctx: &Ctx) -> Arc<TypX> {
    Arc::new(TypX::Datatype(Dt::Path(crate::def::set_type_path(&ctx.global.vstd_crate_name)), namespace_set_typs(), Arc::new(vec![])))
}

impl MaskSet {
    pub fn empty(ctx: &Ctx, span: &Span) -> MaskSet {
        let empty_fun = CallFun::Fun(crate::def::fn_set_empty_name(&ctx.global.vstd_crate_name), None);
        let empty_expx = ExpX::Call(empty_fun, namespace_set_typs(), Arc::new(vec![]));
        let empty_exp = SpannedTyped::new(span, &namespace_set_typ(&ctx), empty_expx);

        MaskSet{
            set: empty_exp,
            spec: Special::Empty,
        }
    }

    pub fn full(ctx: &Ctx, span: &Span) -> MaskSet {
        let full_fun = CallFun::Fun(crate::def::fn_set_full_name(&ctx.global.vstd_crate_name), None);
        let full_expx = ExpX::Call(full_fun, namespace_set_typs(), Arc::new(vec![]));
        let full_exp = SpannedTyped::new(span, &namespace_set_typ(&ctx), full_expx);

        MaskSet{
            set: full_exp,
            spec: Special::Full,
        }
    }

    pub fn from_list(ctx: &Ctx, exps: &Vec<Exp>, span: &Span) -> MaskSet {
        let mut mask = Self::empty(ctx, span);

        for e in exps.iter() {
            mask = mask.insert(ctx, e, span)
        }

        mask
    }

    pub fn from_list_complement(ctx: &Ctx, exps: &Vec<Exp>, span: &Span) -> MaskSet {
        let mut mask = Self::full(ctx, span);

        for e in exps.iter() {
            mask = mask.remove(ctx, e, span)
        }

        mask
    }

    pub fn insert(self: &Self, ctx: &Ctx, exp: &Exp, span: &Span) -> Self {
        let insert_fun = CallFun::Fun(crate::def::fn_set_insert_name(&ctx.global.vstd_crate_name), None);
        let insert_expx = ExpX::Call(insert_fun, namespace_set_typs(), Arc::new(vec![self.set.clone(), exp.clone()]));
        let insert_exp = SpannedTyped::new(span, &namespace_set_typ(&ctx), insert_expx);

        MaskSet{
            set: insert_exp,
            spec: Special::Arbitrary,
        }
    }

    pub fn remove(self: &Self, ctx: &Ctx, exp: &Exp, span: &Span) -> Self {
        let remove_fun = CallFun::Fun(crate::def::fn_set_remove_name(&ctx.global.vstd_crate_name), None);
        let remove_expx = ExpX::Call(remove_fun, namespace_set_typs(), Arc::new(vec![self.set.clone(), exp.clone()]));
        let remove_exp = SpannedTyped::new(span, &namespace_set_typ(&ctx), remove_expx);

        MaskSet{
            set: remove_exp,
            spec: Special::Arbitrary,
        }
    }

    pub fn contains(self: &Self, ctx: &Ctx, exp: &Exp, span: &Span) -> Option<Exp> {
        match self.spec {
            Special::Full => None,
            _ => {
                let contains_fun = CallFun::Fun(crate::def::fn_set_contains_name(&ctx.global.vstd_crate_name), None);
                let contains_expx = ExpX::Call(contains_fun, namespace_set_typs(), Arc::new(vec![self.set.clone(), exp.clone()]));
                let contains_exp = SpannedTyped::new(span, &Arc::new(TypX::Bool), contains_expx);

                Some(contains_exp)
            },
        }
    }

    pub fn subset_of(self: &Self, ctx: &Ctx, other: &Self, span: &Span) -> Option<Exp> {
        match self.spec {
            Special::Empty => None,
            _ => match other.spec {
                Special::Full => None,
                _ => {
                    let subset_of_fun = CallFun::Fun(crate::def::fn_set_subset_of_name(&ctx.global.vstd_crate_name), None);
                    let subset_of_expx = ExpX::Call(subset_of_fun, namespace_set_typs(), Arc::new(vec![self.set.clone(), other.set.clone()]));
                    let subset_of_exp = SpannedTyped::new(span, &Arc::new(TypX::Bool), subset_of_expx);

                    Some(subset_of_exp)
                },
            },
        }
    }
}
