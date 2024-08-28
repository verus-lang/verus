use crate::ast::{
    BinaryOp, BinaryOpr, FieldOpr, Fun, Ident, Path, Quant, SpannedTyped, Typ, TypX, Typs, UnaryOp,
    UnaryOpr, VarBinders, VarIdent, VarIdentDisambiguate, Variant, VariantCheck,
};
use crate::ast_to_sst::get_function_sst;
use crate::ast_util::{is_transparent_to, type_is_bool, undecorate_typ};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::Span;
use crate::sst::PostConditionSst;
use crate::sst::{AssertId, BndX, CallFun, Exp, ExpX, Exps, LocalDecl, LocalDeclX, Stm, StmX};
use crate::sst::{FuncCheckSst, FunctionSst};
use crate::sst_util::{sst_conjoin, sst_equal_ext, sst_implies, sst_not, subst_typ_for_datatype};
use crate::sst_visitor::map_stm_prev_visitor;
use air::ast::Quant::{Exists, Forall};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum Introduction {
    UnfoldFunctionDef(Fun, Exp),
    SplitEquality(Exp),
    Let(VarBinders<Exp>),
    Forall(VarBinders<Typ>),
    Hypothesis(Exp),
}

#[derive(Clone, Debug)]
pub enum CanExpandFurther {
    Yes,
    No(Option<String>),
}

#[derive(Debug)]
pub enum ExpansionTree {
    Branch(Vec<ExpansionTree>),
    Intro(Introduction, Box<ExpansionTree>),
    Leaf(AssertId, Exp, CanExpandFurther),
}

impl ExpansionTree {
    pub fn count_leaves(&self) -> u64 {
        match self {
            ExpansionTree::Branch(v) => {
                let mut n = 0;
                for t in v.iter() {
                    n += t.count_leaves();
                }
                n
            }
            ExpansionTree::Leaf(..) => 1,
            ExpansionTree::Intro(_intro, child) => child.count_leaves(),
        }
    }

    pub fn get_exp_for_assert_id(&self, assert_id: &AssertId) -> Option<Exp> {
        match self {
            ExpansionTree::Branch(v) => {
                for t in v.iter() {
                    let res = t.get_exp_for_assert_id(assert_id);
                    if res.is_some() {
                        return res;
                    }
                }
                None
            }
            ExpansionTree::Leaf(a_id, exp, _) => {
                if a_id == assert_id {
                    Some(exp.clone())
                } else {
                    None
                }
            }
            ExpansionTree::Intro(_intro, child) => child.get_exp_for_assert_id(assert_id),
        }
    }
}

pub struct ExpansionContext {
    fuels: HashMap<Fun, u32>,
}

pub fn get_expansion_ctx(stm: &Stm, assert_id: &AssertId) -> ExpansionContext {
    let mut fuels = HashMap::<Fun, u32>::new();
    let found = get_fuel_at_id(stm, assert_id, &mut fuels);
    if !found {
        panic!("get_expansion_ctx: did not find the given assert_id");
    }
    ExpansionContext { fuels }
}

fn get_fuel_at_id(stm: &Stm, a_id: &AssertId, fuels: &mut HashMap<Fun, u32>) -> bool {
    match &stm.x {
        StmX::Call { assert_id, .. }
        | StmX::Assert(assert_id, ..)
        | StmX::Return { assert_id, .. } => *assert_id == Some(a_id.clone()),
        StmX::AssertBitVector { requires: _, ensures: _ }
        | StmX::AssertCompute(..)
        | StmX::Assume(..)
        | StmX::Assign { .. }
        | StmX::RevealString { .. }
        | StmX::Air { .. }
        | StmX::BreakOrContinue { .. } => false,
        StmX::Fuel(fun, fuel) => {
            fuels.insert(fun.clone(), *fuel);
            return false;
        }
        StmX::If(_cond, stm1, stm2_opt) => {
            let mut f1 = fuels.clone();
            if get_fuel_at_id(stm1, a_id, &mut f1) {
                std::mem::swap(fuels, &mut f1);
                return true;
            }
            if let Some(stm2) = stm2_opt {
                let mut f2 = fuels.clone();
                if get_fuel_at_id(stm2, a_id, &mut f2) {
                    std::mem::swap(fuels, &mut f2);
                    return true;
                }
            }
            return false;
        }
        StmX::Loop { body, cond, .. } => {
            if let Some((cond_stm, _cond_exp)) = cond {
                if get_fuel_at_id(cond_stm, a_id, fuels) {
                    return true;
                }
            }

            let mut inside_fuels = HashMap::<Fun, u32>::new();
            if get_fuel_at_id(body, a_id, &mut inside_fuels) {
                std::mem::swap(&mut inside_fuels, fuels);
                return true;
            }
            return false;
        }
        StmX::OpenInvariant(_, stm) => {
            if get_fuel_at_id(stm, a_id, fuels) {
                return true;
            }
            return false;
        }
        StmX::Block(stms) => {
            for stm in stms.iter() {
                if get_fuel_at_id(stm, a_id, fuels) {
                    return true;
                }
            }
            return false;
        }
        StmX::DeadEnd(body) | StmX::ClosureInner { body, .. } | StmX::AssertQuery { body, .. } => {
            let mut inside_fuels = fuels.clone();
            if get_fuel_at_id(body, a_id, &mut inside_fuels) {
                std::mem::swap(&mut inside_fuels, fuels);
                return true;
            }
            return false;
        }
    }
}

/// Given a function's SST body an assertion ID,
/// we expand the given assertion (or other obligation,
/// like a precondition or postcondition) into multiple assertions.
/// The assertion IDs are all extensions of the given assertion ID, e.g.,
/// if the given assertion ID is 42, then assertion 42 will be replaced
/// with assertions with IDs 42_0, 42_1, 42_2, ...
///
/// The second argument, the 'expansion tree' describes the transformations that were
/// performed to do the expansion.

pub fn do_expansion(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    func_check_sst: &Arc<FuncCheckSst>,
    assert_id: &AssertId,
) -> (Arc<FuncCheckSst>, ExpansionTree) {
    let mut fsst = (**func_check_sst).clone();
    let mut local_decls = (*fsst.local_decls).clone();
    let (body, tree) = do_expansion_body(
        ctx,
        ectx,
        &func_check_sst.post_condition,
        &func_check_sst.body,
        assert_id,
        &mut local_decls,
    );
    fsst.body = body;
    fsst.local_decls = Arc::new(local_decls);
    (Arc::new(fsst), tree)
}

pub fn do_expansion_body(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    post_condition_sst: &PostConditionSst,
    stm: &Stm,
    assert_id: &AssertId,
    local_decls: &mut Vec<LocalDecl>,
) -> (Stm, ExpansionTree) {
    let mut record = None;
    let new_stm = map_stm_prev_visitor(stm, &mut |one_stm, prev_stm| {
        let maybe_expanded = do_expansion_if_assert_id_matches(
            ctx,
            ectx,
            post_condition_sst,
            one_stm,
            prev_stm,
            assert_id,
            local_decls,
        );
        match maybe_expanded {
            None => Ok(one_stm.clone()),
            Some((new_stm, expansion_tree)) => {
                if record.is_some() {
                    panic!("do_expansion_body found duplicate assert_id");
                }
                record = Some(expansion_tree);
                Ok(new_stm)
            }
        }
    })
    .unwrap();

    if let Some(expansion_tree) = record {
        (new_stm, expansion_tree)
    } else {
        panic!("do_expansion_body did not find the given assert_id");
    }
}

fn do_expansion_if_assert_id_matches(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    post_condition_sst: &PostConditionSst,
    stm: &Stm,
    prev_stm: Option<&Stm>,
    assert_id: &AssertId,
    local_decls: &mut Vec<LocalDecl>,
) -> Option<(Stm, ExpansionTree)> {
    // TODO expand BreakOrContinue
    // TODO expand for invariant_open

    match &stm.x {
        StmX::Assert(Some(a_id), _message, exp) if a_id == assert_id => {
            let mut the_exp = exp;

            // If we have something like:
            //    assign tmp = $expr
            //    assert(tmp);
            // then we expand $expr
            // This special case is needed because of the way ast_to_sst translates
            // 'assert' statements. In principle, we could handle substitution more
            // generally, though we'd have to handle mutation, and it might not
            // be very important.
            if let ExpX::Var(uid) = &exp.x {
                if let Some(prev) = prev_stm {
                    if let StmX::Assign { lhs, rhs } = &prev.x {
                        if let ExpX::VarLoc(uid2) = &lhs.dest.x {
                            if uid == uid2 {
                                the_exp = rhs;
                            }
                        }
                    }
                }
            }

            Some(expand_exp(ctx, ectx, assert_id, the_exp, local_decls))
        }
        StmX::Call { assert_id: Some(a_id), fun, typ_args, args, .. } if a_id == assert_id => {
            let preconditions = split_precondition(ctx, &stm.span, fun, typ_args, args);
            // There might be multiple preconditions, there might be some preconditions
            // with multiple conjuncts ... we want to handle these all the same way,
            // so the easiest thing is conjoin everything and then use the common-case
            // logic, which will split it back up.
            let precondition = sst_conjoin(&stm.span, &preconditions);
            Some(expand_exp(ctx, ectx, assert_id, &precondition, local_decls))
        }
        StmX::Return { assert_id: Some(a_id), ret_exp, .. } if a_id == assert_id => {
            let postcondition = sst_conjoin(&stm.span, &post_condition_sst.ens_exps);
            let (stm, tree) = expand_exp(ctx, ectx, assert_id, &postcondition, local_decls);
            let stm = match (&post_condition_sst.dest, ret_exp) {
                (Some(dest_uid), Some(ret_exp)) => Spanned::new(
                    stm.span.clone(),
                    StmX::Block(Arc::new(vec![
                        crate::sst_to_air::assume_var(&stm.span, dest_uid, ret_exp),
                        stm,
                    ])),
                ),
                _ => stm,
            };
            Some((stm, tree))
        }
        _ => None,
    }
}

struct State {
    tmp_var_count: u64,
    base_id: AssertId,
    assert_id_count: u64,
    local_decls: Vec<LocalDecl>,
}

pub fn cons_id(assert_id: &AssertId, idx: u64) -> AssertId {
    let mut aid = (**assert_id).clone();
    aid.push(idx);
    Arc::new(aid)
}

impl State {
    fn get_next_assert_id(&mut self) -> AssertId {
        let id = cons_id(&self.base_id, self.assert_id_count);
        self.assert_id_count += 1;
        id
    }

    fn mk_fresh_ids<T: Clone>(
        &mut self,
        span: &Span,
        binders: &VarBinders<T>,
        e: &Exp,
        to_typ: impl Fn(&T) -> Typ,
    ) -> (Vec<(T, VarIdent)>, Vec<Stm>, Exp) {
        let mut v = vec![];
        let mut substs = HashMap::<VarIdent, Exp>::new();
        let mut typ_invs = vec![];
        for binder in binders.iter() {
            let new_name = VarIdent(
                binder.name.0.clone(),
                VarIdentDisambiguate::ExpandErrorsDecl(self.tmp_var_count),
            );
            self.tmp_var_count += 1;

            let typ = to_typ(&binder.a);
            let decl =
                Arc::new(LocalDeclX { ident: new_name.clone(), typ: typ.clone(), mutable: false });
            self.local_decls.push(decl);

            let var_exp = SpannedTyped::new(span, &typ, ExpX::Var(new_name.clone()));
            substs.insert(binder.name.clone(), var_exp);

            typ_invs.push(crate::ast_to_sst::assume_has_typ(&new_name, &typ, span));

            v.push((binder.a.clone(), new_name));
        }
        let new_exp = crate::sst_util::subst_exp(&HashMap::new(), &substs, &e);
        (v, typ_invs, new_exp)
    }
}

fn expand_exp(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    assert_id: &AssertId,
    exp: &Exp,
    local_decls: &mut Vec<LocalDecl>,
) -> (Stm, ExpansionTree) {
    let mut tmp_var_count_start = 0;
    for ld in local_decls.iter() {
        if let VarIdentDisambiguate::ExpandErrorsDecl(i) = &ld.ident.1 {
            tmp_var_count_start = std::cmp::max(tmp_var_count_start, i + 1);
        }
    }

    let mut state = State {
        tmp_var_count: tmp_var_count_start,
        assert_id_count: 0,
        base_id: assert_id.clone(),
        local_decls: std::mem::take(local_decls),
    };
    let (stm, tree) = expand_exp_rec(ctx, ectx, &mut state, exp, false, false);
    std::mem::swap(local_decls, &mut state.local_decls);
    (stm, tree)
}

fn branch_trees(tree1: ExpansionTree, tree2: ExpansionTree) -> ExpansionTree {
    let mut v = vec![];
    match tree1 {
        ExpansionTree::Branch(mut w) => {
            v.append(&mut w);
        }
        tree => {
            v.push(tree);
        }
    }
    match tree2 {
        ExpansionTree::Branch(mut w) => {
            v.append(&mut w);
        }
        tree => {
            v.push(tree);
        }
    }
    ExpansionTree::Branch(v)
}

fn expand_exp_rec(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    state: &mut State,
    exp: &Exp,
    did_split_yet: bool,
    negate: bool,
) -> (Stm, ExpansionTree) {
    let mk_stm = |stmx| Spanned::new(exp.span.clone(), stmx);
    let sequence_stms = |stm1: Stm, stm2: Stm| {
        let mut stms = vec![];
        match &stm1.x {
            StmX::Block(s) => stms.append(&mut (**s).clone()),
            _ => stms.push(stm1.clone()),
        }
        match &stm2.x {
            StmX::Block(s) => stms.append(&mut (**s).clone()),
            _ => stms.push(stm2.clone()),
        }
        mk_stm(StmX::Block(Arc::new(stms)))
    };

    let leaf = |state: &mut State, can_expand_further| {
        let e = crate::poly::coerce_exp_to_native(ctx, exp);
        let e = if negate { sst_not(&exp.span, &e) } else { e };
        let assert_id = state.get_next_assert_id();
        let stm1 = mk_stm(StmX::Assert(Some(assert_id.clone()), None, e.clone()));
        let stm2 = mk_stm(StmX::Assume(e.clone()));
        let stm = mk_stm(StmX::Block(Arc::new(vec![stm1, stm2])));
        let tree = ExpansionTree::Leaf(assert_id, e, can_expand_further);
        (stm, tree)
    };

    match &exp.x {
        ExpX::Unary(UnaryOp::Not, e) => expand_exp_rec(ctx, ectx, state, e, did_split_yet, !negate),
        ExpX::Binary(op @ (BinaryOp::And | BinaryOp::Or | BinaryOp::Implies), e1, e2) => {
            // Treat this like an '&&' or an '==>', negating either argument appropriately.
            let (is_and, neg1, neg2) = match (op, negate) {
                // (A && B)
                (BinaryOp::And, false) => (true, false, false),
                // (A ==> B)
                (BinaryOp::Implies, false) => (false, false, false),
                // (A || B) is (!A ==> B)
                (BinaryOp::Or, false) => (false, true, false),
                // !(A && B) is (A ==> !B)
                (BinaryOp::And, true) => (false, false, true),
                // !(A ==> B) is (A && !B)
                (BinaryOp::Implies, true) => (true, false, true),
                // !(A || B) is (!A && !B)
                (BinaryOp::Or, true) => (true, true, true),
                _ => unreachable!(),
            };

            if is_and {
                // A && B
                let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e1, true, neg1);
                let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e2, true, neg2);
                (sequence_stms(stm1, stm2), branch_trees(tree1, tree2))
            } else {
                // A ==> B
                let e1 = if neg1 { sst_not(&exp.span, &e1) } else { e1.clone() };
                let intro = Introduction::Hypothesis(e1.clone());
                let (stm, tree) = expand_exp_rec(ctx, ectx, state, e2, did_split_yet, neg2);
                (
                    mk_stm(StmX::If(e1.clone(), stm, None)),
                    ExpansionTree::Intro(intro, Box::new(tree)),
                )
            }
        }
        ExpX::Binary(BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Xor, e1, e2)
        | ExpX::BinaryOpr(BinaryOpr::ExtEq(..), e1, e2) => {
            if did_split_yet {
                return leaf(state, CanExpandFurther::Yes);
            }

            let (is_neq, ext) = match &exp.x {
                ExpX::Binary(BinaryOp::Eq(_), ..) => (false, None),
                ExpX::Binary(BinaryOp::Ne | BinaryOp::Xor, ..) => (true, None),
                ExpX::BinaryOpr(BinaryOpr::ExtEq(deep, _), ..) => (false, Some(*deep)),
                _ => unreachable!(),
            };
            let is_neq = negate ^ is_neq;

            let intro = Introduction::SplitEquality(exp.clone());

            if is_neq {
                if type_is_bool(&undecorate_typ(&e1.typ)) && type_is_bool(&undecorate_typ(&e2.typ))
                {
                    // Split 'e1 != e2' into
                    // !e1 ==> e2
                    // e2 ==> !e1

                    let hyp1 = sst_not(&exp.span, e1);
                    let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e2, true, false);

                    let hyp2 = e2.clone();
                    let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e1, true, true);

                    let hyp_tree1 =
                        ExpansionTree::Intro(Introduction::Hypothesis(hyp1), Box::new(tree1));
                    let hyp_tree2 =
                        ExpansionTree::Intro(Introduction::Hypothesis(hyp2), Box::new(tree2));
                    let tree = branch_trees(hyp_tree1, hyp_tree2);
                    let tree = ExpansionTree::Intro(intro, Box::new(tree));
                    return (sequence_stms(stm1, stm2), tree);
                }
            } else {
                if type_is_bool(&undecorate_typ(&e1.typ)) && type_is_bool(&undecorate_typ(&e2.typ))
                {
                    // Split 'e1 == e2' into
                    // e1 ==> e2
                    // e2 ==> e1

                    let hyp1 = e1.clone();
                    let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e2, true, false);

                    let hyp2 = e2.clone();
                    let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e1, true, false);

                    let hyp_tree1 =
                        ExpansionTree::Intro(Introduction::Hypothesis(hyp1), Box::new(tree1));
                    let hyp_tree2 =
                        ExpansionTree::Intro(Introduction::Hypothesis(hyp2), Box::new(tree2));
                    let tree = branch_trees(hyp_tree1, hyp_tree2);
                    let tree = ExpansionTree::Intro(intro, Box::new(tree));
                    return (sequence_stms(stm1, stm2), tree);
                } else {
                    match try_split_datatype_eq(ctx, e1, e2, ext) {
                        Ok(dt_eq) => {
                            let (stm, tree) = expand_exp_rec(ctx, ectx, state, &dt_eq, true, false);
                            return (stm, ExpansionTree::Intro(intro, Box::new(tree)));
                        }
                        Err(reason) => {
                            return leaf(state, CanExpandFurther::No(reason));
                        }
                    }
                }
            }
            leaf(state, CanExpandFurther::No(None))
        }
        ExpX::If(cond, e1, e2) => {
            let intro = Introduction::Hypothesis(cond.clone());
            let intro_neg = Introduction::Hypothesis(sst_not(&exp.span, &cond));
            let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e1, did_split_yet, negate);
            let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e2, did_split_yet, negate);
            (
                mk_stm(StmX::If(cond.clone(), stm1, Some(stm2))),
                branch_trees(
                    ExpansionTree::Intro(intro, Box::new(tree1)),
                    ExpansionTree::Intro(intro_neg, Box::new(tree2)),
                ),
            )
        }
        ExpX::Call(cf @ (CallFun::Fun(..) | CallFun::Recursive(..)), typs, args) => {
            let (fun_name, typs) = match cf {
                CallFun::Fun(_, Some((resolved_fun_name, resolved_typs))) => {
                    (resolved_fun_name, resolved_typs)
                }
                CallFun::Fun(fun_name, None) => (fun_name, typs),
                CallFun::Recursive(fun_name) => (fun_name, typs),
                _ => unreachable!(),
            };
            let (args, fuel_arg) = if matches!(cf, CallFun::Recursive(_)) {
                let main_args = Arc::new(args[..args.len() - 1].to_vec());
                let fuel_arg = fuel_arg_to_int(&args[args.len() - 1]);
                (main_args, fuel_arg)
            } else {
                (args.clone(), None)
            };
            let function = get_function_sst(ctx, &exp.span, fun_name).unwrap();
            let can_inline = can_inline_function(ctx, ectx, function.clone(), fuel_arg, &exp.span);
            if let Err(err) = can_inline {
                leaf(state, CanExpandFurther::No(err))
            } else if did_split_yet {
                // Don't unfold yet
                leaf(state, CanExpandFurther::Yes)
            } else {
                let typ_params = &function.x.typ_params;
                let pars = &function.x.pars;
                let body = &function.x.axioms.spec_axioms.as_ref().unwrap().body_exp;
                let mut inline_exp = inline_expression(ctx, &args, typs, pars, typ_params, body);

                let fuel = can_inline.unwrap();
                if let Some(fuel) = fuel {
                    inline_exp =
                        crate::recursion::rewrite_rec_call_with_fuel_const(&inline_exp, fuel - 1);
                }

                let (stm, tree) =
                    expand_exp_rec(ctx, ectx, state, &inline_exp, did_split_yet, negate);

                let intro = Introduction::UnfoldFunctionDef(fun_name.clone(), exp.clone());
                (stm, ExpansionTree::Intro(intro, Box::new(tree)))
            }
        }
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(binders) => {
                let (new_ids, _, e) =
                    state.mk_fresh_ids(&exp.span, binders, e, |e: &Exp| e.typ.clone());
                let mut stms = vec![];
                for (exp, uniq_id) in new_ids {
                    stms.push(crate::ast_to_sst::init_var(&exp.span, &uniq_id, &exp));
                }
                let (stm, tree) = expand_exp_rec(ctx, ectx, state, &e, did_split_yet, negate);
                stms.push(stm);
                let intro = Introduction::Let(binders.clone());
                (mk_stm(StmX::Block(Arc::new(stms))), ExpansionTree::Intro(intro, Box::new(tree)))
            }
            BndX::Quant(Quant { quant: q @ (Forall | Exists) }, binders, _trigs)
                if (*q == Exists) == negate =>
            {
                let (_, typ_invs, e) =
                    state.mk_fresh_ids(&exp.span, binders, e, |t: &Typ| t.clone());
                let (stm, tree) = expand_exp_rec(ctx, ectx, state, &e, did_split_yet, negate);
                let intro = Introduction::Forall(binders.clone());

                let mut stms = typ_invs;
                stms.push(stm);
                let sstm = mk_stm(StmX::Block(Arc::new(stms)));

                let dead_end = mk_stm(StmX::DeadEnd(sstm));
                let assume_stm = mk_stm(StmX::Assume(exp.clone()));
                let full_stm = mk_stm(StmX::Block(Arc::new(vec![dead_end, assume_stm])));

                (full_stm, ExpansionTree::Intro(intro, Box::new(tree)))
            }
            _ => leaf(state, CanExpandFurther::No(None)),
        },
        ExpX::WithTriggers(_, e) | ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => {
            expand_exp_rec(ctx, ectx, state, e, did_split_yet, negate)
        }
        _ => leaf(state, CanExpandFurther::No(None)),
    }
}

pub fn try_split_datatype_eq(
    ctx: &Ctx,
    e1: &Exp,
    e2: &Exp,
    ext: Option<bool>,
) -> Result<Exp, Option<String>> {
    let e1 = crate::poly::coerce_exp_to_poly(ctx, e1);
    let e1 = crate::poly::coerce_exp_to_native(ctx, &e1);

    let e2 = crate::poly::coerce_exp_to_poly(ctx, e2);
    let e2 = crate::poly::coerce_exp_to_native(ctx, &e2);

    let TypX::Datatype(dt_name, typ_args, _) = &*undecorate_typ(&e1.typ) else {
        return Err(None);
    };
    let Some(datatype) = ctx.datatype_map.get(dt_name) else {
        return Err(None);
    };
    if !is_transparent_to(&datatype.x.transparency, &ctx.module.x.path) {
        return Err(Some("datatype is opaque here".to_string()));
    }

    if variants_contradict(&e1, &e2) {
        return Err(Some("variants do not match".to_string()));
    }

    if datatype.x.variants.len() <= 2 && (is_no_arg_ctor(&e1) || is_no_arg_ctor(&e2)) {
        // This is a case like, `x == None`, it's not interesting to split
        // (If there are >= 3 variants, it's still useful to split because that
        // means there are >= 2 cases to negate)
        return Err(None);
    }

    // The logic below groups by the variant of the left-hand side.
    // This looks good for the `x == Some(y)` case because it means we can handle
    // the individual cases of x individually for variants other than 'Some'
    // It looks less good for `Some(y) == x`, so to handle that case, we just
    // swap around here and swap back later.
    let (e1, e2, swap) =
        if is_just_ctor(&e1) && !is_just_ctor(&e2) { (e2, e1, true) } else { (e1, e2, false) };

    let bool_typ = Arc::new(TypX::Bool);

    // Turn 'e1 == e2' into
    //  e1.is_Variant() ==>
    //      e2.is_Variant()
    //      && e1.field == e2.field
    //      && e1.g == e2.g
    //      && ...
    //  && ....
    // Of course, we can skip the variant checks if there's only 1 variant

    let mut w0 = vec![];
    let mut w = vec![];
    for variant in datatype.x.variants.iter() {
        let mut v = vec![];

        if is_ctor_for_other(&e1, variant) {
            // This whole block is vacuously true
            continue;
        }

        let e1_variant_trivial = datatype.x.variants.len() == 1 || is_ctor_for(&e1, variant);
        let e2_variant_trivial = datatype.x.variants.len() == 1 || is_ctor_for(&e2, variant);

        if !e2_variant_trivial {
            if is_ctor_for_other(&e2, variant) {
                w0.push(sst_not(
                    &e2.span,
                    &SpannedTyped::new(
                        &e2.span,
                        &bool_typ,
                        ExpX::UnaryOpr(
                            UnaryOpr::IsVariant {
                                datatype: dt_name.clone(),
                                variant: variant.name.clone(),
                            },
                            e1.clone(),
                        ),
                    ),
                ));
                continue;
            }
            v.push(SpannedTyped::new(
                &e2.span,
                &bool_typ,
                ExpX::UnaryOpr(
                    UnaryOpr::IsVariant {
                        datatype: dt_name.clone(),
                        variant: variant.name.clone(),
                    },
                    e2.clone(),
                ),
            ));
        }
        for field in variant.fields.iter() {
            let field_typ = subst_typ_for_datatype(&datatype.x.typ_params, typ_args, &field.a.0);
            let field_typ = if crate::poly::typ_is_poly(ctx, &field.a.0) {
                crate::poly::coerce_typ_to_poly(ctx, &field_typ)
            } else {
                crate::poly::coerce_typ_to_native(ctx, &field_typ)
            };
            let mut e1_field = field_exp(&e1, &field_typ, dt_name, &variant.name, &field.name);
            let mut e2_field = field_exp(&e2, &field_typ, dt_name, &variant.name, &field.name);

            if ext.is_some() {
                e1_field = crate::poly::coerce_exp_to_poly(ctx, &e1_field);
                e2_field = crate::poly::coerce_exp_to_poly(ctx, &e2_field);
            }
            if swap {
                v.push(sst_equal_ext(&e2.span, &e2_field, &e1_field, ext));
            } else {
                v.push(sst_equal_ext(&e1.span, &e1_field, &e2_field, ext));
            }
        }

        if v.len() == 0 {
            continue;
        }

        let vconjunct = sst_conjoin(&e1.span, &v);

        let vhyp = if e1_variant_trivial {
            vconjunct
        } else {
            sst_implies(
                &e1.span,
                &SpannedTyped::new(
                    &e2.span,
                    &bool_typ,
                    ExpX::UnaryOpr(
                        UnaryOpr::IsVariant {
                            datatype: dt_name.clone(),
                            variant: variant.name.clone(),
                        },
                        e1.clone(),
                    ),
                ),
                &vconjunct,
            )
        };

        w.push(vhyp)
    }

    w0.append(&mut w);
    Ok(sst_conjoin(&e1.span, &w0))
}

pub fn field_exp(
    exp: &Exp,
    field_typ: &Typ,
    datatype: &Path,
    variant: &Ident,
    field: &Ident,
) -> Exp {
    let e = remove_uninteresting_unary_ops(exp);

    match &e.x {
        ExpX::Ctor(_, variant_ident, fields) if variant_ident == variant => {
            return crate::ast_util::get_field(fields, field).a.clone();
        }
        _ => {}
    }

    SpannedTyped::new(
        &exp.span,
        field_typ,
        ExpX::UnaryOpr(
            UnaryOpr::Field(FieldOpr {
                datatype: datatype.clone(),
                variant: variant.clone(),
                field: field.clone(),
                get_variant: false,
                check: VariantCheck::None,
            }),
            exp.clone(),
        ),
    )
}

fn remove_uninteresting_unary_ops(exp: &Exp) -> &Exp {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e)
        | ExpX::Unary(UnaryOp::Trigger(_), e) => remove_uninteresting_unary_ops(e),
        _ => exp,
    }
}

fn variants_contradict(e1: &Exp, e2: &Exp) -> bool {
    let e1 = remove_uninteresting_unary_ops(e1);
    let e2 = remove_uninteresting_unary_ops(e2);
    match (&e1.x, &e2.x) {
        (ExpX::Ctor(_, variant_ident1, _), ExpX::Ctor(_, variant_ident2, _)) => {
            variant_ident1 != variant_ident2
        }
        _ => false,
    }
}

fn is_no_arg_ctor(e: &Exp) -> bool {
    let e = remove_uninteresting_unary_ops(e);
    match &e.x {
        ExpX::Ctor(_, _variant_ident, fields) => fields.len() == 0,
        _ => false,
    }
}

fn is_just_ctor(e: &Exp) -> bool {
    let e = remove_uninteresting_unary_ops(e);
    match &e.x {
        ExpX::Ctor(_, _variant_ident, _) => true,
        _ => false,
    }
}

fn is_ctor_for(e: &Exp, variant: &Variant) -> bool {
    let e = remove_uninteresting_unary_ops(e);
    match &e.x {
        ExpX::Ctor(_, variant_ident, _) => variant_ident == &variant.name,
        _ => false,
    }
}

fn is_ctor_for_other(e: &Exp, variant: &Variant) -> bool {
    let e = remove_uninteresting_unary_ops(e);
    match &e.x {
        ExpX::Ctor(_, variant_ident, _) => variant_ident != &variant.name,
        _ => false,
    }
}

fn fuel_arg_to_int(e: &Exp) -> Option<usize> {
    match &e.x {
        ExpX::Var(_) => None,
        ExpX::FuelConst(i) => Some(*i),
        _ => panic!(
            "Verus Internal Error: expected fuel constant trying to unfold recursive function for --expand-errors"
        ),
    }
}

pub fn is_bool_type(t: &Typ) -> bool {
    match &**t {
        TypX::Bool => true,
        TypX::Boxed(b) => is_bool_type(b),
        _ => false,
    }
}

fn can_inline_function(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    fun_to_inline: FunctionSst,
    cur_fuel_level: Option<usize>,
    span: &Span,
) -> Result<Option<usize>, Option<String>> {
    let opaque_err = Err(Some("function is opaque".to_string()));
    let hidden_err = Err(Some("function is hidden".to_string()));
    let closed_err = Err(Some("function is closed".to_string()));
    let uninterp_err = Err(Some("function is uninterpreted".to_string()));
    let foreign_module_err = Err(None);
    let type_err = Err(Some("not bool type".to_string()));

    let fun_owner = match &ctx.fun {
        Some(f) => get_function_sst(ctx, span, &f.current_fun).unwrap(),
        None => {
            return Err(Some(
                "Internal error: cannot find the owning function of this function call".to_string(),
            ));
        }
    };

    if cur_fuel_level == Some(0) {
        return Err(Some("reached fuel limit for recursion".to_string()));
    }

    let mut fuel = fun_to_inline.x.fuel;
    let mut hidden = false;

    let fs_to_hide = &fun_owner.x.attrs.hidden;
    for f_to_hide in &**fs_to_hide {
        if **f_to_hide == *fun_to_inline.x.name {
            fuel = 0;
            hidden = true;
        };
    }

    match ectx.fuels.get(&fun_to_inline.x.name) {
        Some(local_fuel) => {
            fuel = *local_fuel;
        }
        None => {}
    };

    if fuel == 0 {
        if hidden {
            return hidden_err;
        } else {
            return opaque_err;
        }
    } else {
        if fun_to_inline.x.owning_module.is_none() {
            return foreign_module_err;
        }

        let body = match fun_to_inline.x.axioms.spec_axioms.as_ref() {
            Some(body) => body,
            None => {
                return uninterp_err;
            }
        };
        if !crate::ast_util::is_visible_to_of_owner(
            &fun_to_inline.x.owning_module,
            &ctx.module.x.path,
        ) {
            // if the target inline function is outside this module, track `open` `closed` at module boundaries
            match fun_to_inline.x.publish {
                Some(b) => {
                    if !b {
                        return opaque_err;
                    }
                }
                None => {
                    return closed_err;
                }
            };
        }

        // Note: this should never happen
        if !is_bool_type(&body.body_exp.typ) {
            return type_err;
        }

        //if unfold_count >= fuel {
        //    return Err(format!("exhaused fuel {fuel}"));
        //}
        let fun = &fun_to_inline.x.name;

        if !ctx.func_sst_map.contains_key(fun) {
            return Err(Some(format!("Internal error: not in SstMap")));
        }

        if fun_to_inline.x.has.has_decrease {
            let f = match cur_fuel_level {
                Some(f) => f,
                None => fuel as usize,
            };
            return Ok(Some(f));
        } else {
            return Ok(None);
        }
    }
}

fn split_precondition(ctx: &Ctx, span: &Span, name: &Fun, typs: &Typs, args: &Exps) -> Vec<Exp> {
    let fun = get_function_sst(ctx, span, name).unwrap();
    let mut exps: Vec<Exp> = Vec::new();

    // We split the `requires` expression on the call site.
    // (If we were to split the `requires` expression on the function itself,
    // this split encoding would take effect on every call site, which is not desirable.)
    //
    // Also, note that pervasive::assert consists of `requires` and `ensures`,
    // so we are also splitting pervasive::assert here.
    let params = &fun.x.pars;
    let typ_params = &fun.x.typ_params;
    for exp in fun.x.decl.reqs.iter().cloned() {
        // In requires, old(x) is really just x:
        let mut f_var_at = |e: &Exp| match &e.x {
            ExpX::VarAt(x, crate::ast::VarAt::Pre) => e.new_x(ExpX::Var(x.clone())),
            _ => e.clone(),
        };
        let exp = crate::sst_visitor::map_exp_visitor(&exp, &mut f_var_at);
        let exp_substituted = inline_expression(ctx, args, typs, params, typ_params, &exp);

        exps.push(exp_substituted);
    }
    exps
}

struct DiagnosticsVoid {}
impl air::messages::Diagnostics for DiagnosticsVoid {
    fn report_as(&self, _msg: &air::messages::ArcDynMessage, _level: air::messages::MessageLevel) {}
    fn report(&self, _msg: &air::messages::ArcDynMessage) {}
    fn report_now(&self, _msg: &air::messages::ArcDynMessage) {}
    fn report_as_now(
        &self,
        _msg: &air::messages::ArcDynMessage,
        _msg_as: air::messages::MessageLevel,
    ) {
    }
}

// This function is to
// 1) inline a function body at a call site
// 2) inline a function's requires expression at a call site
pub fn inline_expression(
    ctx: &Ctx,
    args: &Exps,
    typs: &Typs,
    params: &crate::sst::Pars,
    typ_params: &crate::ast::Idents,
    body: &Exp,
) -> Exp {
    // code copied from crate::ast_to_sst::finalized_exp
    let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
    let mut substs: HashMap<VarIdent, Exp> = HashMap::new();
    assert!(typ_params.len() == typs.len());
    for (name, typ) in typ_params.iter().zip(typs.iter()) {
        assert!(!typ_substs.contains_key(name));
        let typ = crate::poly::coerce_typ_to_poly(ctx, typ);
        typ_substs.insert(name.clone(), typ.clone());
    }
    assert!(params.len() == args.len());
    for (param, arg) in params.iter().zip(args.iter()) {
        let unique = &param.x.name;
        assert!(!substs.contains_key(unique));
        substs.insert(unique.clone(), arg.clone());
    }
    let e = crate::sst_util::subst_exp(&typ_substs, &substs, body);
    let e = SpannedTyped::new(&body.span, &e.typ, e.x.clone());
    return e;
}
