use crate::ast::{
    BinaryOp, BinaryOpr, FieldOpr, Fun, Function, Ident, Path, Quant, SpannedTyped, Typ, TypX,
    Typs, UnaryOp, UnaryOpr, Variant, VariantCheck,
};
use crate::ast_to_sst::get_function;
use crate::ast_util::{is_transparent_to, type_is_bool, undecorate_typ};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::func_to_air::FunctionSst;
use crate::func_to_air::SstInfo;
use crate::func_to_air::SstMap;
use crate::messages::Span;
use crate::sst::{
    AssertId, BndX, CallFun, Exp, ExpX, Exps, LocalDecl, LocalDeclX, Stm, StmX, UniqueIdent,
};
use crate::sst_to_air::PostConditionSst;
use crate::sst_util::{sst_conjoin, sst_equal_ext, sst_implies, sst_not, subst_typ_for_datatype};
use crate::sst_visitor::map_stm_visitor_for_assert_id_nodes;
use air::ast::Binders;
use air::ast::Quant::{Exists, Forall};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum Introduction {
    UnfoldFunctionDef(Fun, Exp),
    SplitEquality(Exp),
    Let(Binders<Exp>),
    Forall(Binders<Typ>),
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

    pub fn intros_up_to(&self, assert_id: &AssertId) -> Option<Vec<Introduction>> {
        match self {
            ExpansionTree::Branch(v) => {
                for t in v.iter() {
                    let res = t.intros_up_to(assert_id);
                    if res.is_some() {
                        return res;
                    }
                }
                None
            }
            ExpansionTree::Leaf(a_id, ..) => {
                if a_id == assert_id {
                    Some(vec![])
                } else {
                    None
                }
            }
            ExpansionTree::Intro(intro, child) => {
                if let Some(mut v) = child.intros_up_to(assert_id) {
                    v.push(intro.clone());
                    Some(v)
                } else {
                    None
                }
            }
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
        | StmX::Assume(..)
        | StmX::Assign { .. }
        | StmX::RevealString { .. }
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
        StmX::Loop { body, .. } => {
            let mut inside_fuels = HashMap::<Fun, u32>::new();
            if get_fuel_at_id(body, a_id, &mut inside_fuels) {
                std::mem::swap(&mut inside_fuels, fuels);
                return true;
            }
            return false;
        }
        StmX::OpenInvariant(_, _, _, stm, _) => {
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

pub fn do_expansion(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    previous_intros: &[Introduction],
    fun_ssts: &SstMap,
    function_sst: &FunctionSst,
    assert_id: &AssertId,
) -> (FunctionSst, ExpansionTree) {
    let (body, tree, mut local_decls) = do_expansion_body(
        ctx,
        ectx,
        previous_intros,
        fun_ssts,
        &function_sst.post_condition,
        &function_sst.body,
        assert_id,
    );
    let mut fsst = function_sst.clone();
    fsst.body = body;
    fsst.local_decls.append(&mut local_decls);
    (fsst, tree)
}

pub fn do_expansion_body(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    previous_intros: &[Introduction],
    fun_ssts: &SstMap,
    post_condition_sst: &PostConditionSst,
    stm: &Stm,
    assert_id: &AssertId,
) -> (Stm, ExpansionTree, Vec<LocalDecl>) {
    let mut record = None;
    let new_stm = map_stm_visitor_for_assert_id_nodes(stm, &mut |one_stm, prev_stm| {
        let maybe_expanded = do_expansion_if_assert_id_matches(
            ctx,
            ectx,
            previous_intros,
            fun_ssts,
            post_condition_sst,
            one_stm,
            prev_stm,
            assert_id,
        );
        match maybe_expanded {
            None => Ok(one_stm.clone()),
            Some((new_stm, expansion_tree, local_decls)) => {
                if record.is_some() {
                    panic!("do_expansion_body found duplicate assert_id");
                }
                record = Some((expansion_tree, local_decls));
                Ok(new_stm)
            }
        }
    })
    .unwrap();

    if let Some((expansion_tree, local_decls)) = record {
        (new_stm, expansion_tree, local_decls)
    } else {
        panic!("do_expansion_body did not find the given assert_id");
    }
}

fn do_expansion_if_assert_id_matches(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    previous_intros: &[Introduction],
    fun_ssts: &SstMap,
    post_condition_sst: &PostConditionSst,
    stm: &Stm,
    prev_stm: Option<&Stm>,
    assert_id: &AssertId,
) -> Option<(Stm, ExpansionTree, Vec<LocalDecl>)> {
    // TODO expand BreakOrContinue
    // TODO expand for invariant_open
    // TODO expand postcondition

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

            Some(expand_exp(ctx, ectx, previous_intros, fun_ssts, assert_id, the_exp))
        }
        StmX::Call { assert_id: Some(a_id), fun, typ_args, args, .. } if a_id == assert_id => {
            let preconditions = split_precondition(ctx, fun_ssts, &stm.span, fun, typ_args, args);
            // There might be multiple preconditions, there might be some preconditions
            // with multiple conjuncts ... we want to handle these all the same way,
            // so the easiest thing is conjoin everything and then use the common-case
            // logic, which will split it back up.
            let precondition = sst_conjoin(&stm.span, &preconditions);
            Some(expand_exp(ctx, ectx, previous_intros, fun_ssts, assert_id, &precondition))
        }
        StmX::Return { assert_id: Some(a_id), ret_exp, .. } if a_id == assert_id => {
            let postcondition = sst_conjoin(&stm.span, &post_condition_sst.ens_exps);
            let (stm, tree, decls) =
                expand_exp(ctx, ectx, previous_intros, fun_ssts, assert_id, &postcondition);
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
            Some((stm, tree, decls))
        }
        _ => None,
    }
}

struct State<'a> {
    fun_ssts: &'a SstMap,
    unfold_counts: HashMap<Fun, u32>,
    tmp_var_count: u64,
    base_id: AssertId,
    assert_id_count: u64,
    local_decls: Vec<LocalDecl>,
}

pub fn cons_id(assert_id: &AssertId, idx: u64) -> AssertId {
    Arc::new(format!("{:}_{:}", assert_id, idx))
}

impl<'a> State<'a> {
    fn get_next_assert_id(&mut self) -> AssertId {
        let id = cons_id(&self.base_id, self.assert_id_count);
        self.assert_id_count += 1;
        id
    }

    fn push_unfold(&mut self, fun: &Fun) {
        if self.unfold_counts.contains_key(fun) {
            *self.unfold_counts.get_mut(fun).unwrap() += 1;
        } else {
            self.unfold_counts.insert(fun.clone(), 1);
        }
    }

    fn pop_unfold(&mut self, fun: &Fun) {
        *self.unfold_counts.get_mut(fun).unwrap() -= 1;
    }

    fn mk_fresh_ids<T: Clone>(
        &mut self,
        span: &Span,
        binders: &Binders<T>,
        e: &Exp,
        to_typ: impl Fn(&T) -> Typ,
    ) -> (Vec<(T, UniqueIdent)>, Exp) {
        let mut v = vec![];
        let mut substs = HashMap::<UniqueIdent, Exp>::new();
        for binder in binders.iter() {
            let new_name = UniqueIdent {
                name: Arc::new(format!(
                    "{:}{:}",
                    crate::def::PREFIX_EXPAND_ERRORS_TEMP_VAR,
                    self.base_id
                )),
                local: Some(self.tmp_var_count),
            };
            self.tmp_var_count += 1;

            let typ = to_typ(&binder.a);
            let decl =
                Arc::new(LocalDeclX { ident: new_name.clone(), typ: typ.clone(), mutable: false });
            self.local_decls.push(decl);

            let var_exp = SpannedTyped::new(span, &typ, ExpX::Var(new_name.clone()));
            substs.insert(UniqueIdent { name: binder.name.clone(), local: None }, var_exp);

            v.push((binder.a.clone(), new_name));
        }
        let new_exp = crate::sst_util::subst_exp(&HashMap::new(), &substs, &e);
        (v, new_exp)
    }
}

fn expand_exp(
    ctx: &Ctx,
    ectx: &ExpansionContext,
    previous_intros: &[Introduction],
    fun_ssts: &SstMap,
    assert_id: &AssertId,
    exp: &Exp,
) -> (Stm, ExpansionTree, Vec<LocalDecl>) {
    let mut unfold_counts = HashMap::<Fun, u32>::new();
    for intro in previous_intros {
        if let Introduction::UnfoldFunctionDef(fun, _) = intro {
            if unfold_counts.contains_key(fun) {
                *unfold_counts.get_mut(fun).unwrap() += 1;
            } else {
                unfold_counts.insert(fun.clone(), 1);
            }
        }
    }

    let mut state = State {
        fun_ssts,
        unfold_counts,
        tmp_var_count: 0,
        assert_id_count: 0,
        base_id: assert_id.clone(),
        local_decls: vec![],
    };
    let (stm, tree) = expand_exp_rec(ctx, ectx, &mut state, exp, false, false, false);
    let State { local_decls, .. } = state;
    (stm, tree, local_decls)
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
    unbox: bool,
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
        let e = if unbox { crate::poly::coerce_exp_to_native(ctx, exp) } else { exp.clone() };
        let e = if negate { sst_not(&exp.span, &e) } else { e };
        let assert_id = state.get_next_assert_id();
        let stm1 = mk_stm(StmX::Assert(Some(assert_id.clone()), None, e.clone()));
        let stm2 = mk_stm(StmX::Assume(e.clone()));
        let stm = mk_stm(StmX::Block(Arc::new(vec![stm1, stm2])));
        let tree = ExpansionTree::Leaf(assert_id, e, can_expand_further);
        (stm, tree)
    };

    match &exp.x {
        ExpX::Unary(UnaryOp::Not, e) => {
            expand_exp_rec(ctx, ectx, state, e, did_split_yet, !negate, unbox)
        }
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
                let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e1, true, neg1, unbox);
                let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e2, true, neg2, unbox);
                (sequence_stms(stm1, stm2), branch_trees(tree1, tree2))
            } else {
                // A ==> B
                let e1 = if neg1 { sst_not(&exp.span, &e1) } else { e1.clone() };
                let intro = Introduction::Hypothesis(e1.clone());
                let (stm, tree) = expand_exp_rec(ctx, ectx, state, e2, did_split_yet, neg2, unbox);
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
                    let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e2, true, false, unbox);

                    let hyp2 = e2.clone();
                    let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e1, true, true, unbox);

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
                    let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e2, true, false, unbox);

                    let hyp2 = e2.clone();
                    let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e1, true, false, unbox);

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
                            let (stm, tree) =
                                expand_exp_rec(ctx, ectx, state, &dt_eq, true, false, unbox);
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
            let (stm1, tree1) = expand_exp_rec(ctx, ectx, state, e1, did_split_yet, negate, unbox);
            let (stm2, tree2) = expand_exp_rec(ctx, ectx, state, e2, did_split_yet, negate, unbox);
            (
                mk_stm(StmX::If(cond.clone(), stm1, Some(stm2))),
                branch_trees(
                    ExpansionTree::Intro(intro, Box::new(tree1)),
                    ExpansionTree::Intro(intro_neg, Box::new(tree2)),
                ),
            )
        }
        ExpX::Call(CallFun::Fun(fun_name, resolved), typs, args) => {
            let fun_name = match resolved {
                Some((resolved_fun_name, _)) => resolved_fun_name,
                None => fun_name,
            };
            let function = get_function(ctx, &exp.span, fun_name).unwrap();
            let can_inline = can_inline_function(ctx, state, ectx, function, &exp.span);
            if let Err(err) = can_inline {
                leaf(state, CanExpandFurther::No(err))
            } else if did_split_yet {
                // Don't unfold yet
                leaf(state, CanExpandFurther::Yes)
            } else {
                let SstInfo { inline, params, body, .. } =
                    state.fun_ssts.borrow().get(fun_name).unwrap();
                let inline_exp = crate::split_expression::inline_expression(
                    ctx,
                    args,
                    typs,
                    params,
                    &inline.typ_params,
                    body,
                );

                state.push_unfold(fun_name);
                let (stm, tree) =
                    expand_exp_rec(ctx, ectx, state, &inline_exp, did_split_yet, negate, unbox);
                state.pop_unfold(fun_name);

                let intro = Introduction::UnfoldFunctionDef(fun_name.clone(), exp.clone());
                (stm, ExpansionTree::Intro(intro, Box::new(tree)))
            }
        }
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(binders) => {
                let (new_ids, e) =
                    state.mk_fresh_ids(&exp.span, binders, e, |e: &Exp| e.typ.clone());
                let mut stms = vec![];
                for (exp, uniq_id) in new_ids {
                    stms.push(crate::ast_to_sst::init_var(&exp.span, &uniq_id, &exp));
                }
                let (stm, tree) =
                    expand_exp_rec(ctx, ectx, state, &e, did_split_yet, negate, unbox);
                stms.push(stm);
                let intro = Introduction::Let(binders.clone());
                (mk_stm(StmX::Block(Arc::new(stms))), ExpansionTree::Intro(intro, Box::new(tree)))
            }
            BndX::Quant(Quant { quant: q @ (Forall | Exists) }, binders, _trigs)
                if (*q == Exists) == negate =>
            {
                let (_, e) = state.mk_fresh_ids(&exp.span, binders, e, |t: &Typ| t.clone());
                let (stm, tree) =
                    expand_exp_rec(ctx, ectx, state, &e, did_split_yet, negate, unbox);
                let intro = Introduction::Forall(binders.clone());

                let dead_end = mk_stm(StmX::DeadEnd(stm));
                let assume_stm = mk_stm(StmX::Assume(exp.clone()));
                let full_stm = mk_stm(StmX::Block(Arc::new(vec![dead_end, assume_stm])));

                (full_stm, ExpansionTree::Intro(intro, Box::new(tree)))
            }
            _ => leaf(state, CanExpandFurther::No(None)),
        },
        ExpX::WithTriggers(_, e) => {
            expand_exp_rec(ctx, ectx, state, e, did_split_yet, negate, unbox)
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_), e) => {
            expand_exp_rec(ctx, ectx, state, e, did_split_yet, negate, false)
        }
        ExpX::UnaryOpr(UnaryOpr::Unbox(_), e) => {
            expand_exp_rec(ctx, ectx, state, e, did_split_yet, negate, true)
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
    if !is_transparent_to(&datatype.x.transparency, &ctx.module) {
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

fn can_inline_function(
    ctx: &Ctx,
    state: &State,
    ectx: &ExpansionContext,
    fun_to_inline: Function,
    span: &Span,
) -> Result<(), Option<String>> {
    let opaque_err = Err(Some("function is opaque".to_string()));
    let hidden_err = Err(Some("function is hidden".to_string()));
    let closed_err = Err(Some("function is closed".to_string()));
    let uninterp_err = Err(Some("function is uninterpreted".to_string()));
    let foreign_module_err = Err(None);
    let type_err = Err(Some("not bool type".to_string()));
    let recursive_err =
        Err(Some("recursive function (not supported in expand-errors)".to_string()));

    let mut found_local_fuel = false;
    let fuel = match ectx.fuels.get(&fun_to_inline.x.name) {
        Some(local_fuel) => {
            found_local_fuel = true;
            *local_fuel
        }
        None => fun_to_inline.x.fuel,
    };

    let mut hidden = false; // track `hide` statement
    match &ctx.fun {
        Some(f) => {
            let fun_owner = get_function(ctx, span, &f.current_fun).unwrap();
            let fs_to_hide = &fun_owner.x.attrs.hidden;
            for f_to_hide in &**fs_to_hide {
                if **f_to_hide == *fun_to_inline.x.name {
                    hidden = true;
                };
            }
        }
        None => {
            return Err(Some(
                "Internal error: cannot find the owning function of this function call".to_string(),
            ));
        }
    };

    let _unfold_count = match state.unfold_counts.get(&fun_to_inline.x.name) {
        Some(x) => *x,
        None => 0,
    };

    if fuel == 0 || (!found_local_fuel && hidden) {
        if hidden {
            return hidden_err;
        } else {
            return opaque_err;
        }
    } else {
        if fun_to_inline.x.owning_module.is_none() {
            return foreign_module_err;
        }

        let body = match fun_to_inline.x.body.as_ref() {
            Some(body) => body,
            None => {
                return uninterp_err;
            }
        };
        if !crate::ast_util::is_visible_to_of_owner(&fun_to_inline.x.owning_module, &ctx.module) {
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
        if !crate::split_expression::is_bool_type(&body.typ) {
            return type_err;
        }

        if fun_to_inline.x.decrease.len() != 0 {
            return recursive_err;
        }

        //if unfold_count >= fuel {
        //    return Err(format!("exhaused fuel {fuel}"));
        //}
        let fun = &fun_to_inline.x.name;
        let fun_ssts = &state.fun_ssts;

        if fun_ssts.borrow().get(fun).is_none() {
            return Err(Some(format!("Internal error: not in SstMap")));
        }

        return Ok(());
    }
}

fn split_precondition(
    ctx: &Ctx,
    fun_ssts: &SstMap,
    span: &Span,
    name: &Fun,
    typs: &Typs,
    args: &Exps,
) -> Vec<Exp> {
    let fun = get_function(ctx, span, name).unwrap();
    let mut exps: Vec<Exp> = Vec::new();

    // We split the `requires` expression on the call site.
    // (If we were to split the `requires` expression on the function itself,
    // this split encoding would take effect on every call site, which is not desirable.)
    //
    // Also, note that pervasive::assert consists of `requires` and `ensures`,
    // so we are also splitting pervasive::assert here.
    let params = &fun.x.params;
    let typ_params = &fun.x.typ_params;
    for e in &**fun.x.require {
        // skip checks on require, since this is checked when the function is checked
        let exp = crate::ast_to_sst::expr_to_exp_as_spec_skip_checks(
            &ctx,
            &DiagnosticsVoid {},
            fun_ssts,
            &crate::func_to_air::params_to_pars(params, true), // REVIEW: is `true` here desirable?
            &e,
        )
        .expect("expr_to_exp_as_spec_skip_checks");

        // In requires, old(x) is really just x:
        let mut f_var_at = |e: &Exp| match &e.x {
            ExpX::VarAt(x, crate::ast::VarAt::Pre) => e.new_x(ExpX::Var(x.clone())),
            _ => e.clone(),
        };
        let exp = crate::sst_visitor::map_exp_visitor(&exp, &mut f_var_at);
        let exp_substituted =
            crate::split_expression::inline_expression(ctx, args, typs, params, typ_params, &exp);

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
