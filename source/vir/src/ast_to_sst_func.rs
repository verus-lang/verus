use crate::ast::{
    Fun, Function, FunctionKind, Ident, Idents, MaskSpec, Mode, Param, ParamX, Params,
    SpannedTyped, Typ, TypX, VarBinder, VarBinderX, VarIdent, VirErr,
};
use crate::ast_visitor;
use crate::context::Ctx;
use crate::def::{unique_local, Spanned};
use crate::inv_masks::MaskSet;
use crate::messages::{error, Message};
use crate::sst::{BndX, Exp, ExpX, Par, ParPurpose, ParX, Pars, Stm, StmX};
use crate::sst::{FunctionSst, LocalDecl, PostConditionKind, PostConditionSst};
use crate::sst_to_air::{exp_to_expr, ExprCtxt, ExprMode};
use crate::sst_util::{subst_exp, subst_stm};
use crate::update_cell::UpdateCell;
use crate::util::vec_map;
use std::collections::HashMap;
use std::sync::Arc;

pub struct SstInline {
    pub(crate) typ_params: Idents,
    pub do_inline: bool,
}

pub struct SstInfo {
    pub(crate) inline: SstInline,
    pub(crate) params: Params,
    pub(crate) memoize: bool,
    pub(crate) body: Exp,
}

pub type SstMap = UpdateCell<HashMap<Fun, SstInfo>>;

pub struct FuncBodySst {
    pub pars: Pars,
    pub decrease_when: Option<Exp>,
    pub termination_decls: Vec<LocalDecl>,
    pub termination_stm: Stm,
    pub is_recursive: bool,
    pub body_exp: Exp,
}

pub struct FuncAxiomsSst {
    pub pars: Pars,
    pub spec_axioms: Option<FuncBodySst>,
    pub proof_exec_axioms: Option<(Pars, Exp)>,
}

pub struct FuncDeclSst {
    pub req_inv_pars: Pars,
    pub ens_pars: Pars,
    pub post_pars: Pars,
    pub reqs: Vec<Exp>,
    pub enss: Vec<Exp>,
    pub inv_masks: Vec<Vec<Exp>>,
    pub fndef_axioms: Vec<Exp>,
}

pub(crate) fn param_to_par(param: &Param, allow_is_mut: bool) -> Par {
    param.map_x(|p| {
        let ParamX { name, typ, mode, is_mut, unwrapped_info: _ } = p;
        if *is_mut && !allow_is_mut {
            panic!("mut unexpected here");
        }
        ParX { name: name.clone(), typ: typ.clone(), mode: *mode, purpose: ParPurpose::Regular }
    })
}

pub(crate) fn params_to_pars(params: &Params, allow_is_mut: bool) -> Pars {
    Arc::new(vec_map(params, |p| param_to_par(p, allow_is_mut)))
}

pub(crate) fn params_to_pre_post_pars(params: &Params, pre: bool) -> Pars {
    Arc::new(
        params
            .iter()
            .flat_map(|param| {
                let mut res = Vec::new();
                if param.x.is_mut {
                    res.push(param.map_x(|p| ParX {
                        name: p.name.clone(),
                        typ: p.typ.clone(),
                        mode: p.mode,
                        purpose: ParPurpose::MutPre,
                    }));
                }
                if !(param.x.is_mut && pre) {
                    res.push(param.map_x(|p| ParX {
                        name: p.name.clone(),
                        typ: p.typ.clone(),
                        mode: p.mode,
                        purpose: if param.x.is_mut {
                            ParPurpose::MutPost
                        } else {
                            ParPurpose::Regular
                        },
                    }));
                }
                res
            })
            .collect::<Vec<_>>(),
    )
}

fn func_body_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
    body: &crate::ast::Expr,
    not_verifying_owning_bucket: bool,
) -> Result<(SstMap, FuncBodySst), VirErr> {
    let pars = params_to_pars(&function.x.params, false);

    // ast --> sst
    let mut state = crate::ast_to_sst::State::new(diagnostics);
    state.declare_params(&pars);
    state.view_as_spec = true;
    state.fun_ssts = fun_ssts;
    // Use expr_to_pure_exp_skip_checks here
    // because spec precondition checking is performed as a separate query
    let body_exp = crate::ast_to_sst::expr_to_pure_exp_skip_checks(&ctx, &mut state, &body)?;
    let body_exp = state.finalize_exp(ctx, diagnostics, &state.fun_ssts, &body_exp)?;
    let inline =
        SstInline { typ_params: function.x.typ_params.clone(), do_inline: function.x.attrs.inline };
    let info = SstInfo {
        inline,
        params: function.x.params.clone(),
        memoize: function.x.attrs.memoize,
        body: body_exp.clone(),
    };
    assert!(!state.fun_ssts.borrow().contains_key(&function.x.name));
    state.fun_ssts.borrow_mut().insert(function.x.name.clone(), info);
    state.finalize();

    // Rewrite recursive calls to use fuel
    let (is_recursive, body_exp, scc_rep) =
        crate::recursion::rewrite_recursive_fun_with_fueled_rec_call(
            ctx, function, &body_exp, None,
        )?;

    // Check termination and/or recommends
    let mut check_state = crate::ast_to_sst::State::new(diagnostics);
    // don't check recommends during decreases checking; these are separate passes:
    check_state.disable_recommends = 1;
    check_state.declare_params(&pars);
    check_state.view_as_spec = true;
    check_state.fun_ssts = state.fun_ssts;
    check_state.check_spec_decreases = Some((function.x.name.clone(), scc_rep));
    let check_body_stm =
        crate::ast_to_sst::expr_to_one_stm_with_post(&ctx, &mut check_state, &body)?;
    let check_body_stm =
        check_state.finalize_stm(ctx, diagnostics, &check_state.fun_ssts, &check_body_stm)?;

    let mut proof_body: Vec<crate::ast::Expr> = Vec::new();
    let decrease_when = if let Some(req) = &function.x.decrease_when {
        // "when" means the function is only defined if the requirements hold

        // first, set up proof_body
        let mut reqs = crate::traits::trait_bounds_to_ast(ctx, &req.span, &function.x.typ_bounds);
        reqs.push(req.clone());
        for expr in reqs {
            let assumex = crate::ast::ExprX::AssertAssume { is_assume: true, expr: expr.clone() };
            proof_body.push(SpannedTyped::new(
                &req.span,
                &Arc::new(TypX::Tuple(Arc::new(vec![]))),
                assumex,
            ));
        }
        proof_body.push(req.clone()); // check spec preconditions

        // Skip checks because we check decrease_when below
        let exp = crate::ast_to_sst::expr_to_pure_exp_skip_checks(ctx, &mut check_state, req)?;
        let exp = check_state.finalize_exp(ctx, diagnostics, &check_state.fun_ssts, &exp)?;
        Some(exp)
    } else {
        None
    };
    if let Some(fun) = &function.x.decrease_by {
        check_state.view_as_spec = false;
        if let Some(decrease_by_fun) = ctx.func_map.get(fun) {
            let decrease_by_fun_body =
                decrease_by_fun.x.body.as_ref().expect("decreases_by has body").clone();
            ast_visitor::expr_visitor_check(&decrease_by_fun_body, &mut |_scope_map, expr| {
                match &expr.x {
                    crate::ast::ExprX::Return(_) => Err(error(
                        &expr.span,
                        "explicit returns are not allowed in decreases_by function",
                    )),
                    _ => Ok(()),
                }
            })?;
            proof_body.push(decrease_by_fun_body);
        } else {
            assert!(not_verifying_owning_bucket);
        }
    }
    let mut proof_body_stms: Vec<Stm> = Vec::new();
    for expr in proof_body {
        let (mut stms, exp) = crate::ast_to_sst::expr_to_stm_opt(ctx, &mut check_state, &expr)?;
        assert!(!matches!(exp, crate::ast_to_sst::ReturnValue::Never));
        proof_body_stms.append(&mut stms);
    }
    let proof_body_stm = crate::ast_to_sst::stms_to_one_stm(&body.span, proof_body_stms);
    let proof_body_stm =
        check_state.finalize_stm(ctx, diagnostics, &check_state.fun_ssts, &proof_body_stm)?;
    check_state.finalize();

    let (mut termination_decls, termination_stm) = crate::recursion::check_termination_stm(
        ctx,
        diagnostics,
        &check_state.fun_ssts,
        function,
        Some(proof_body_stm),
        &check_body_stm,
    )?;
    termination_decls.splice(0..0, check_state.local_decls.into_iter());

    Ok((
        check_state.fun_ssts,
        FuncBodySst {
            pars,
            decrease_when,
            termination_decls,
            termination_stm,
            is_recursive,
            body_exp,
        },
    ))
}

fn req_ens_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
    specs: &Vec<crate::ast::Expr>,
    pre: bool,
) -> Result<(Pars, Vec<Exp>), VirErr> {
    let mut pars = params_to_pre_post_pars(&function.x.params, pre);
    if !pre && matches!(function.x.mode, Mode::Exec | Mode::Proof) && function.x.has_return_name() {
        let mut ps = (*pars).clone();
        ps.push(param_to_par(&function.x.ret, false));
        pars = Arc::new(ps);
    }
    let mut exps: Vec<Exp> = Vec::new();
    for e in specs.iter() {
        // Use expr_to_exp_skip_checks because we check req/ens in body
        let exp = crate::ast_to_sst::expr_to_exp_skip_checks(ctx, diagnostics, fun_ssts, &pars, e)?;
        exps.push(exp);
    }
    Ok((pars, exps))
}

pub fn func_decl_to_sst(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
) -> Result<FuncDeclSst, VirErr> {
    let (pars, reqs) =
        req_ens_to_sst(ctx, diagnostics, fun_ssts, function, &function.x.require, true)?;
    let (ens_pars, enss) =
        req_ens_to_sst(ctx, diagnostics, fun_ssts, function, &function.x.ensure, false)?;
    let post_pars = params_to_pre_post_pars(&function.x.params, false);

    let mut inv_masks: Vec<Vec<Exp>> = Vec::new();
    match &function.x.mask_spec {
        None => {}
        Some(MaskSpec::InvariantOpens(es) | MaskSpec::InvariantOpensExcept(es)) => {
            for e in es.iter() {
                let (_pars, inv_mask) =
                    req_ens_to_sst(ctx, diagnostics, fun_ssts, function, &vec![e.clone()], true)?;
                inv_masks.push(inv_mask);
            }
        }
    }

    let mut fndef_axiom_exps: Vec<Exp> = Vec::new();
    if crate::ast_simplify::need_fndef_axiom(&ctx.fndef_type_set, function) {
        let fndef_axioms = function
            .x
            .fndef_axioms
            .as_ref()
            .expect("expected FnDef axioms to have been generated in ast_simplify");
        for fndef_axiom in fndef_axioms.iter() {
            let mut state = crate::ast_to_sst::State::new(diagnostics);
            let exp =
                crate::ast_to_sst::expr_to_pure_exp_skip_checks(ctx, &mut state, fndef_axiom)?;
            let exp = state.finalize_exp(ctx, diagnostics, &fun_ssts, &exp)?;
            state.finalize();

            // Add forall-binders for each type param
            // The fndef_axiom shoudld already be a 'forall' statement
            // so we can add them to the existing forall node

            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for name in function.x.typ_params.iter() {
                let typ = Arc::new(TypX::TypeId);
                let bind = VarBinderX { name: crate::ast_util::typ_unique_var(name), a: typ };
                binders.push(Arc::new(bind));
            }

            let exp = match &exp.x {
                ExpX::Bind(bnd, e) => match &bnd.x {
                    BndX::Quant(quant, qbinders, trigs) => {
                        let mut qbinders = (&**qbinders).clone();
                        qbinders.append(&mut binders);
                        let bndx = BndX::Quant(*quant, Arc::new(qbinders), trigs.clone());
                        let bnd = Spanned::new(bnd.span.clone(), bndx);
                        let expx = ExpX::Bind(bnd, e.clone());
                        SpannedTyped::new(&exp.span, &exp.typ, expx)
                    }
                    _ => {
                        panic!("fndef_axiom should be forall");
                    }
                },
                _ => {
                    panic!("fndef_axiom should be forall");
                }
            };
            fndef_axiom_exps.push(exp);
        }
    }

    Ok(FuncDeclSst {
        req_inv_pars: pars,
        ens_pars,
        post_pars,
        reqs,
        enss,
        inv_masks,
        fndef_axioms: fndef_axiom_exps,
    })
}

pub fn func_axioms_to_sst(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
    public_body: bool,
    not_verifying_owning_bucket: bool,
) -> Result<(SstMap, FuncAxiomsSst), VirErr> {
    let pars = params_to_pars(&function.x.params, true);
    match function.x.mode {
        Mode::Spec => {
            // Body
            if public_body {
                if let Some(body) = &function.x.body {
                    let (fun_ssts, function_sst) = func_body_to_sst(
                        ctx,
                        diagnostics,
                        fun_ssts,
                        function,
                        body,
                        not_verifying_owning_bucket,
                    )?;
                    let axioms = FuncAxiomsSst {
                        pars: params_to_pars(&function.x.params, false),
                        spec_axioms: Some(function_sst),
                        proof_exec_axioms: None,
                    };
                    return Ok((fun_ssts, axioms));
                }
            }
        }
        Mode::Exec | Mode::Proof => {
            assert!(!function.x.attrs.is_decrease_by);

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we inherit the trait requires/ensures,
                // so we can just return here.
                return Ok((
                    fun_ssts,
                    FuncAxiomsSst { pars, spec_axioms: None, proof_exec_axioms: None },
                ));
            }
            if let Some((params, req_ens)) = &function.x.broadcast_forall {
                let params = params_to_pre_post_pars(params, false);
                // Use expr_to_bind_decls_exp_skip_checks, skipping checks on req_ens,
                // because the requires/ensures are checked when the function itself is checked
                let exp = crate::ast_to_sst::expr_to_bind_decls_exp_skip_checks(
                    ctx,
                    diagnostics,
                    &fun_ssts,
                    &params,
                    req_ens,
                )?;
                let axioms = FuncAxiomsSst {
                    pars,
                    spec_axioms: None,
                    proof_exec_axioms: Some((params, exp)),
                };
                return Ok((fun_ssts, axioms));
            }
        }
    }
    Ok((fun_ssts, FuncAxiomsSst { pars, spec_axioms: None, proof_exec_axioms: None }))
}

pub(crate) fn map_expr_rename_vars(
    e: &Arc<SpannedTyped<crate::ast::ExprX>>,
    req_ens_e_rename: &HashMap<VarIdent, VarIdent>,
) -> Result<Arc<SpannedTyped<crate::ast::ExprX>>, Message> {
    ast_visitor::map_expr_visitor(e, &|expr| {
        use crate::ast::ExprX;
        Ok(match &expr.x {
            ExprX::Var(i) => expr.new_x(ExprX::Var(req_ens_e_rename.get(i).unwrap_or(i).clone())),
            ExprX::VarLoc(i) => {
                expr.new_x(ExprX::VarLoc(req_ens_e_rename.get(i).unwrap_or(i).clone()))
            }
            ExprX::VarAt(i, at) => {
                expr.new_x(ExprX::VarAt(req_ens_e_rename.get(i).unwrap_or(i).clone(), *at))
            }
            _ => expr.clone(),
        })
    })
}

pub fn func_def_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
) -> Result<(SstMap, FunctionSst), VirErr> {
    let body = match &function.x.body {
        Some(body) => body,
        _ => {
            panic!("func_def_to_air should only be called for function with a body");
        }
    };

    // Note: since is_const functions serve double duty as exec and spec,
    // we generate an exec check for them here to catch any arithmetic overflows.
    let (trait_typ_substs, req_ens_function, inherit) =
        if let FunctionKind::TraitMethodImpl { method, trait_path, trait_typ_args, .. } =
            &function.x.kind
        {
            // Inherit requires/ensures from trait method declaration
            let tr = &ctx.trait_map[trait_path];
            let mut typ_params = vec![crate::def::trait_self_type_param()];
            for (x, _) in tr.x.typ_params.iter() {
                typ_params.push(x.clone());
            }
            let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
            assert!(typ_params.len() == trait_typ_args.len());
            for (x, t) in typ_params.iter().zip(trait_typ_args.iter()) {
                let t = crate::poly::coerce_typ_to_poly(ctx, t);
                trait_typ_substs.insert(x.clone(), t);
            }
            (trait_typ_substs, &ctx.func_map[method], true)
        } else {
            (HashMap::new(), function, false)
        };

    let mut state = crate::ast_to_sst::State::new(diagnostics);
    state.fun_ssts = fun_ssts;

    let mut ens_params = (*function.x.params).clone();
    let dest = if function.x.has_return_name() {
        let ParamX { name, typ, .. } = &function.x.ret.x;
        ens_params.push(function.x.ret.clone());
        state.declare_var_stm(name, typ, false, false);
        Some(unique_local(name))
    } else {
        None
    };

    let ens_params = Arc::new(ens_params);
    let req_pars = params_to_pars(&function.x.params, true);
    let ens_pars = params_to_pars(&ens_params, true);

    for param in function.x.params.iter() {
        state.declare_var_stm(&param.x.name, &param.x.typ, param.x.is_mut, false);
    }

    let mut req_ens_e_rename: HashMap<_, _> = req_ens_function
        .x
        .params
        .iter()
        .zip(function.x.params.iter())
        .map(|(p1, p2)| (p1.x.name.clone(), p2.x.name.clone()))
        .collect();
    req_ens_e_rename.insert(req_ens_function.x.ret.x.name.clone(), function.x.ret.x.name.clone());

    let mut req_stms: Vec<Stm> = Vec::new();
    let mut reqs: Vec<Exp> = Vec::new();
    reqs.extend(crate::traits::trait_bounds_to_sst(ctx, &function.span, &function.x.typ_bounds));
    for e in req_ens_function.x.require.iter() {
        let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
        if ctx.checking_spec_preconditions() {
            // TODO: apply trait_typs_substs here?
            let (stms, exp) =
                crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, &e_with_req_ens_params)?;
            req_stms.extend(stms);
            req_stms.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
        } else {
            // skip checks because we call expr_to_pure_exp_check above
            let exp = crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &req_pars,
                &e_with_req_ens_params,
            )?;
            let exp = subst_exp(&trait_typ_substs, &HashMap::new(), &exp);
            reqs.push(exp);
        }
    }

    let mask_spec = req_ens_function.x.mask_spec_or_default();
    let inv_spec_exprs = match &mask_spec {
        MaskSpec::InvariantOpens(exprs) | MaskSpec::InvariantOpensExcept(exprs) => exprs.clone(),
    };
    let mut inv_spec_air_exprs = vec![];
    for e in inv_spec_exprs.iter() {
        let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
        let exp = if ctx.checking_spec_preconditions() {
            let (stms, exp) =
                crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, &e_with_req_ens_params)?;
            req_stms.extend(stms);
            exp
        } else {
            crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &req_pars,
                &e_with_req_ens_params,
            )?
        };

        let is_singular = function.x.attrs.integer_ring;
        let expr_ctxt = ExprCtxt::new_mode_singular(ExprMode::Body, is_singular);
        let exp = state.finalize_exp(ctx, diagnostics, &state.fun_ssts, &exp)?;
        let air_expr = exp_to_expr(ctx, &exp, &expr_ctxt)?;
        inv_spec_air_exprs
            .push(crate::inv_masks::MaskSingleton { expr: air_expr, span: e.span.clone() });
    }
    let mask_set = match mask_spec {
        MaskSpec::InvariantOpens(_exprs) => MaskSet::from_list(inv_spec_air_exprs),
        MaskSpec::InvariantOpensExcept(_exprs) => MaskSet::from_list_complement(inv_spec_air_exprs),
    };

    for e in function.x.decrease.iter() {
        if ctx.checking_spec_preconditions() {
            let stms = crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e)?;
            req_stms.extend(stms);
        }
    }
    let mut ens_spec_precondition_stms: Vec<Stm> = Vec::new();
    let mut enss: Vec<Exp> = Vec::new();
    if inherit {
        for e in req_ens_function.x.ensure.iter() {
            let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
            if ctx.checking_spec_preconditions() {
                let stms =
                    crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e_with_req_ens_params)?;
                let stms: Vec<_> = stms
                    .iter()
                    .map(|stm| subst_stm(&trait_typ_substs, &HashMap::new(), &stm))
                    .collect();
                ens_spec_precondition_stms.extend(stms);
            } else {
                // skip checks because we call expr_to_pure_exp_check above
                let exp = crate::ast_to_sst::expr_to_exp_skip_checks(
                    ctx,
                    diagnostics,
                    &state.fun_ssts,
                    &ens_pars,
                    &e_with_req_ens_params,
                )?;
                let exp = subst_exp(&trait_typ_substs, &HashMap::new(), &exp);
                enss.push(exp);
            }
        }
    }
    for e in function.x.ensure.iter() {
        if ctx.checking_spec_preconditions() {
            ens_spec_precondition_stms
                .extend(crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e)?);
        } else {
            // skip checks because we call expr_to_pure_exp_check above
            enss.push(crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &ens_pars,
                &e,
            )?);
        }
    }

    // AST --> SST
    let mut stm = crate::ast_to_sst::expr_to_one_stm_with_post(&ctx, &mut state, &body)?;
    if ctx.checking_spec_preconditions() && trait_typ_substs.len() == 0 {
        if let Some(fun) = &function.x.decrease_by {
            let decrease_by_fun = &ctx.func_map[fun];
            let (body_stms, _exp) = crate::ast_to_sst::expr_to_stm_or_error(
                &ctx,
                &mut state,
                decrease_by_fun.x.body.as_ref().expect("decreases_by has body"),
            )?;
            req_stms.extend(body_stms);
        }
        req_stms.push(stm);
        stm = crate::ast_to_sst::stms_to_one_stm(&body.span, req_stms);
    }

    let stm = state.finalize_stm(&ctx, diagnostics, &state.fun_ssts, &stm)?;
    let ens_spec_precondition_stms: Result<Vec<_>, _> = ens_spec_precondition_stms
        .iter()
        .map(|s| state.finalize_stm(&ctx, diagnostics, &state.fun_ssts, &s))
        .collect();
    let ens_spec_precondition_stms = ens_spec_precondition_stms?;

    // Check termination
    let no_termination_check = function.x.mode == Mode::Exec && function.x.decrease.len() == 0;
    let (decls, stm) = if no_termination_check || ctx.checking_spec_preconditions() {
        (vec![], stm)
    } else {
        crate::recursion::check_termination_stm(
            ctx,
            diagnostics,
            &state.fun_ssts,
            function,
            None,
            &stm,
        )?
    };

    // SST --> AIR
    for decl in decls {
        state.local_decls.push(decl.clone());
    }

    state.finalize();
    let crate::ast_to_sst::State { local_decls, statics, fun_ssts, .. } = state;

    Ok((
        fun_ssts,
        FunctionSst {
            reqs: Arc::new(reqs),
            post_condition: PostConditionSst {
                dest,
                ens_exps: enss,
                ens_spec_precondition_stms,
                kind: PostConditionKind::Ensures,
            },
            mask_set,
            body: stm,
            local_decls: local_decls,
            statics: statics.into_iter().collect(),
        },
    ))
}
