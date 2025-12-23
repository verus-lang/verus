use crate::ast::{
    Expr, ExprX, Fun, Function, FunctionKind, Ident, ItemKind, MaskSpec, Mode, Param, ParamX,
    Params, Path, PlaceX, SpannedTyped, Typ, TypX, UnaryOp, UnwindSpec, VarBinder, VarBinderX,
    VarIdent, VirErr,
};
use crate::ast_to_sst::{
    FinalState, State, expr_to_bind_decls_exp_skip_checks, expr_to_exp_skip_checks,
    expr_to_one_stm_with_post, expr_to_pure_exp_check, expr_to_pure_exp_check_with_typ_substs,
    expr_to_pure_exp_skip_checks, expr_to_stm_opt, expr_to_stm_or_error, stms_to_one_stm,
};
use crate::ast_util::{is_body_visible_to, unit_typ};
use crate::ast_visitor;
use crate::context::{Ctx, FunctionCtx};
use crate::def::{Spanned, unique_local};
use crate::inv_masks::MaskSet;
use crate::messages::{Message, error};
use crate::sst::{BndX, Exp, ExpX, Exps, LocalDeclKind, Par, ParPurpose, ParX, Pars, Stm, StmX};
use crate::sst::{
    FuncAxiomsSst, FuncCheckSst, FuncDeclSst, FuncSpecBodySst, FunctionSst, FunctionSstHas,
    FunctionSstX, PostConditionKind, PostConditionSst, UnwindSst,
};
use crate::sst_util::subst_exp;
use crate::util::vec_map;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub type SstMap = Arc<HashMap<Fun, FunctionSst>>;

pub trait FunctionCommon {
    fn name(&self) -> &Fun;
    fn owning_module(&self) -> &Option<Path>;
    fn mode(&self) -> crate::ast::Mode;
    fn attrs(&self) -> &crate::ast::FunctionAttrs;
}

impl FunctionCommon for crate::ast::FunctionX {
    fn name(&self) -> &Fun {
        &self.name
    }

    fn owning_module(&self) -> &Option<Path> {
        &self.owning_module
    }

    fn mode(&self) -> crate::ast::Mode {
        self.mode
    }

    fn attrs(&self) -> &crate::ast::FunctionAttrs {
        &self.attrs
    }
}

impl FunctionCommon for FunctionSstX {
    fn name(&self) -> &Fun {
        &self.name
    }

    fn owning_module(&self) -> &Option<Path> {
        &self.owning_module
    }

    fn mode(&self) -> crate::ast::Mode {
        self.mode
    }

    fn attrs(&self) -> &crate::ast::FunctionAttrs {
        &self.attrs
    }
}

pub fn mk_fun_ctx_dec<F: FunctionCommon>(
    f: &Arc<Spanned<F>>,
    checking_spec_preconditions: bool,
    checking_spec_decreases: bool,
) -> Option<FunctionCtx> {
    assert!(!(checking_spec_preconditions && checking_spec_decreases));
    Some(FunctionCtx {
        checking_spec_preconditions,
        checking_spec_preconditions_for_non_spec: checking_spec_preconditions
            && f.x.mode() != Mode::Spec,
        checking_spec_decreases,
        module_for_chosen_triggers: f.x.owning_module().clone(),
        current_fun: f.x.name().clone(),
        current_fun_attrs: f.x.attrs().clone(),
    })
}

pub fn mk_fun_ctx<F: FunctionCommon>(
    f: &Arc<Spanned<F>>,
    checking_spec_preconditions: bool,
) -> Option<FunctionCtx> {
    mk_fun_ctx_dec(f, checking_spec_preconditions, false)
}

pub(crate) fn param_to_par(param: &Param, allow_is_mut: bool) -> Par {
    param.map_x(|p| {
        let ParamX { name, typ, mode, is_mut, unwrapped_info: _ } = p;
        if *is_mut && !allow_is_mut {
            panic!("mut unexpected here");
        }
        ParX {
            name: name.clone(),
            typ: typ.clone(),
            mode: *mode,
            is_mut: *is_mut,
            purpose: ParPurpose::Regular,
        }
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
                        is_mut: p.is_mut,
                        purpose: ParPurpose::MutPre,
                    }));
                }
                if !(param.x.is_mut && pre) {
                    res.push(param.map_x(|p| ParX {
                        name: p.name.clone(),
                        typ: p.typ.clone(),
                        mode: p.mode,
                        is_mut: p.is_mut,
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
    function: &Function,
    body: &Expr,
    verifying_owning_bucket: bool,
) -> Result<FuncSpecBodySst, VirErr> {
    let pars = params_to_pars(&function.x.params, false);

    // ast --> sst
    let mut state = State::new(diagnostics);
    state.declare_params(&pars);
    state.view_as_spec = true;
    // Use expr_to_pure_exp_skip_checks here
    // because spec precondition checking is performed as a separate query
    let body_exp = expr_to_pure_exp_skip_checks(&ctx, &mut state, &body)?;
    let body_exp = state.finalize_exp(ctx, &body_exp)?;
    state.finalize();

    // Check termination and/or recommends
    let scc_rep = ctx
        .global
        .func_call_graph
        .get_scc_rep(&crate::recursion::Node::Fun(function.x.name.clone()));
    let mut check_state = State::new(diagnostics);
    // don't check recommends during decreases checking; these are separate passes:
    check_state.disable_recommends = 1;
    check_state.declare_params(&pars);
    check_state.view_as_spec = true;
    check_state.check_spec_decreases = Some((function.x.name.clone(), scc_rep));
    let check_body_stm = expr_to_one_stm_with_post(&ctx, &mut check_state, &body, &function.span)?;
    let check_body_stm = check_state.finalize_stm(ctx, &check_body_stm)?;

    let mut proof_body: Vec<Expr> = Vec::new();
    let decrease_when = if let Some(req) = &function.x.decrease_when {
        // "when" means the function is only defined if the requirements hold

        // first, set up proof_body
        let mut reqs = crate::traits::trait_bounds_to_ast(ctx, &req.span, &function.x.typ_bounds);
        reqs.push(req.clone());
        for expr in reqs {
            let assumex = ExprX::AssertAssume { is_assume: true, expr: expr.clone(), msg: None };
            proof_body.push(SpannedTyped::new(&req.span, &unit_typ(), assumex));
        }
        proof_body.push(req.clone()); // check spec preconditions

        // Skip checks because we check decrease_when below
        let exp = expr_to_pure_exp_skip_checks(ctx, &mut check_state, req)?;
        let exp = check_state.finalize_exp(ctx, &exp)?;
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
                    ExprX::Return(_) => Err(error(
                        &expr.span,
                        "explicit returns are not allowed in decreases_by function",
                    )),
                    _ => Ok(()),
                }
            })?;
            proof_body.push(decrease_by_fun_body);
        } else {
            assert!(!verifying_owning_bucket);
        }
    }
    let mut proof_body_stms: Vec<Stm> = Vec::new();
    for expr in proof_body {
        let (mut stms, exp) = expr_to_stm_opt(ctx, &mut check_state, &expr)?;
        assert!(!matches!(exp, crate::ast_to_sst::Maybe::Never));
        proof_body_stms.append(&mut stms);
    }
    let proof_body_stm = stms_to_one_stm(&body.span, proof_body_stms);
    let proof_body_stm = check_state.finalize_stm(ctx, &proof_body_stm)?;
    let FinalState { local_decls, statics: _ } = check_state.finalize();

    let is_recursive = crate::recursion::fun_is_recursive(ctx, function);
    let termination_check = if is_recursive && verifying_owning_bucket {
        let (mut termination_decls, termination_inits, termination_stm) =
            crate::recursion::check_termination_stm(
                ctx,
                diagnostics,
                function,
                Some(proof_body_stm),
                &check_body_stm,
                false,
            )?;
        termination_decls.splice(0..0, local_decls.into_iter());

        let termination_check = FuncCheckSst {
            post_condition: Arc::new(crate::sst::PostConditionSst {
                dest: None,
                kind: if function.x.decrease_by.is_some() {
                    PostConditionKind::DecreasesBy
                } else {
                    PostConditionKind::DecreasesImplicitLemma
                },
                ens_exps: Arc::new(vec![]),
                ens_spec_precondition_stms: Arc::new(vec![]),
            }),
            body: termination_stm,
            local_decls: Arc::new(termination_decls),
            local_decls_decreases_init: termination_inits,
            statics: Arc::new(vec![]),
            reqs: Arc::new(vec![]),
            unwind: UnwindSst::NoUnwind,
        };
        Some(termination_check)
    } else {
        if function.x.decrease.len() > 0 && !is_recursive {
            let msg = "proof blocks inside spec code is currently supported only for recursion";
            // TODO: remove this restriction when we generalize ProofInSpec beyond termination
            ast_visitor::expr_visitor_check(&body, &mut |_scope_map, expr| match &expr.x {
                ExprX::ProofInSpec(_) => Err(error(&expr.span, msg)),
                _ => Ok(()),
            })?;
        }
        None
    };

    Ok(FuncSpecBodySst { decrease_when, termination_check, body_exp })
}

fn req_ens_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    function: &Function,
    specs: &Vec<Expr>,
    pre: bool,
) -> Result<(Pars, Vec<Exp>), VirErr> {
    let mut pars = params_to_pre_post_pars(&function.x.params, pre);
    let pars_mut = Arc::make_mut(&mut pars);
    if !pre && matches!(function.x.mode, Mode::Exec | Mode::Proof) && function.x.ens_has_return {
        pars_mut.push(param_to_par(&function.x.ret, false));
    }
    let mut exps: Vec<Exp> = Vec::new();
    for e in specs.iter() {
        // Use expr_to_exp_skip_checks because we check req/ens in body
        let exp = expr_to_exp_skip_checks(ctx, diagnostics, &pars, e)?;
        exps.push(exp);
    }
    Ok((pars, exps))
}

pub fn func_decl_to_sst(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    function: &Function,
) -> Result<FuncDeclSst, VirErr> {
    let (pars, reqs) = req_ens_to_sst(ctx, diagnostics, function, &function.x.require, true)?;
    let (ens_pars, enss0) =
        req_ens_to_sst(ctx, diagnostics, function, &function.x.ensure.0, false)?;
    let (_, enss1) = req_ens_to_sst(ctx, diagnostics, function, &function.x.ensure.1, false)?;

    let mut inv_masks: Vec<Exps> = Vec::new();
    match &function.x.mask_spec {
        None => {}
        Some(MaskSpec::InvariantOpens(_span, es) | MaskSpec::InvariantOpensExcept(_span, es)) => {
            for e in es.iter() {
                let (_pars, inv_mask) =
                    req_ens_to_sst(ctx, diagnostics, function, &vec![e.clone()], true)?;
                inv_masks.push(Arc::new(inv_mask));
            }
        }
        Some(MaskSpec::InvariantOpensSet(e)) => {
            let (_pars, inv_mask) =
                req_ens_to_sst(ctx, diagnostics, function, &vec![e.clone()], true)?;
            inv_masks.push(Arc::new(inv_mask));
        }
    }

    let unwind_condition = match &function.x.unwind_spec {
        None => None,
        Some(UnwindSpec::NoUnwind) => None,
        Some(UnwindSpec::MayUnwind) => None,
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            let (_pars, exps) = req_ens_to_sst(ctx, diagnostics, function, &vec![e.clone()], true)?;
            assert!(exps.len() == 1);
            Some(exps[0].clone())
        }
    };

    let mut fndef_axiom_exps: Vec<Exp> = Vec::new();
    if crate::ast_simplify::need_fndef_axiom(&ctx.fndef_type_set, function) {
        let fndef_axioms = function
            .x
            .fndef_axioms
            .as_ref()
            .expect("expected FnDef axioms to have been generated in ast_simplify");
        for fndef_axiom in fndef_axioms.iter() {
            let mut state = State::new(diagnostics);
            let exp = expr_to_pure_exp_skip_checks(ctx, &mut state, fndef_axiom)?;
            let exp = state.finalize_exp(ctx, &exp)?;
            state.finalize();

            // Add forall-binders for each type param
            // The fndef_axiom should already be a 'forall' statement
            // so we can add them to the existing forall node

            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for name in function.x.typ_params.iter() {
                let typ = Arc::new(TypX::TypeId);
                let bind = VarBinderX { name: crate::ast_util::typ_unique_var(name), a: typ };
                binders.push(Arc::new(bind));
            }

            let exp = match &exp.x {
                ExpX::Unary(UnaryOp::MustBeElaborated, ebind) => match &ebind.x {
                    ExpX::Bind(bnd, e) => match &bnd.x {
                        BndX::Quant(quant, qbinders, trigs, None) => {
                            let mut qbinders = (&**qbinders).clone();
                            qbinders.append(&mut binders);
                            let bndx = BndX::Quant(*quant, Arc::new(qbinders), trigs.clone(), None);
                            let bnd = Spanned::new(bnd.span.clone(), bndx);
                            let ebind = ebind.new_x(ExpX::Bind(bnd, e.clone()));
                            exp.new_x(ExpX::Unary(UnaryOp::MustBeElaborated, ebind))
                        }
                        _ => {
                            panic!("fndef_axiom should be forall");
                        }
                    },
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
        reqs: Arc::new(reqs),
        enss: (Arc::new(enss0), Arc::new(enss1)),
        inv_masks: Arc::new(inv_masks),
        unwind_condition,
        fndef_axioms: Arc::new(fndef_axiom_exps),
    })
}

pub fn func_axioms_to_sst(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    function: &Function,
    public_body: bool,
    verifying_owning_bucket: bool,
) -> Result<FuncAxiomsSst, VirErr> {
    match function.x.mode {
        Mode::Spec => {
            // Body
            if public_body {
                if let Some(body) = &function.x.body {
                    let func_spec_body = func_body_to_sst(
                        ctx,
                        diagnostics,
                        function,
                        body,
                        verifying_owning_bucket,
                    )?;
                    let axioms = FuncAxiomsSst {
                        spec_axioms: Some(func_spec_body),
                        proof_exec_axioms: None,
                    };
                    return Ok(axioms);
                }
            }
        }
        Mode::Exec | Mode::Proof => {
            assert!(!function.x.attrs.is_decrease_by);

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we inherit the trait requires/ensures,
                // so we can just return here.
                return Ok(FuncAxiomsSst { spec_axioms: None, proof_exec_axioms: None });
            }
            if function.x.attrs.broadcast_forall {
                let span = &function.span;
                let mut reqs: Vec<Expr> = Vec::new();
                reqs.extend(crate::traits::trait_bounds_to_ast(ctx, span, &function.x.typ_bounds));
                reqs.extend((*function.x.require).clone());
                let req = crate::ast_util::conjoin(span, &reqs);
                assert!(function.x.ensure.1.len() == 0);
                let ens = crate::ast_util::conjoin(span, &*function.x.ensure.0);
                let req_ens = crate::ast_util::mk_implies(span, &req, &ens);
                let params = params_to_pre_post_pars(&function.x.params, false);
                // Use expr_to_bind_decls_exp_skip_checks, skipping checks on req_ens,
                // because the requires/ensures are checked when the function itself is checked
                let exp = expr_to_bind_decls_exp_skip_checks(ctx, diagnostics, &params, &req_ens)?;
                let axioms = FuncAxiomsSst {
                    spec_axioms: None,
                    proof_exec_axioms: Some((params, exp, Arc::new(vec![]))),
                };
                return Ok(axioms);
            }
        }
    }
    Ok(FuncAxiomsSst { spec_axioms: None, proof_exec_axioms: None })
}

pub(crate) fn map_expr_rename_vars(
    e: &Arc<SpannedTyped<ExprX>>,
    param_renames: &HashMap<VarIdent, VarIdent>,
) -> Result<Arc<SpannedTyped<ExprX>>, Message> {
    ast_visitor::map_expr_place_visitor(
        e,
        &|expr| {
            Ok(match &expr.x {
                ExprX::Var(i) => expr.new_x(ExprX::Var(param_renames.get(i).unwrap_or(i).clone())),
                ExprX::VarLoc(i) => {
                    expr.new_x(ExprX::VarLoc(param_renames.get(i).unwrap_or(i).clone()))
                }
                ExprX::VarAt(i, at) => {
                    expr.new_x(ExprX::VarAt(param_renames.get(i).unwrap_or(i).clone(), *at))
                }
                _ => expr.clone(),
            })
        },
        &|place| {
            Ok(match &place.x {
                PlaceX::Local(i) => {
                    place.new_x(PlaceX::Local(param_renames.get(i).unwrap_or(i).clone()))
                }
                _ => place.clone(),
            })
        },
    )
}

struct InheritanceSubstitutions {
    trait_typ_substs: HashMap<Ident, Typ>,
    param_renames: HashMap<VarIdent, VarIdent>,
}

/// We need to lower a bunch of expressions from AST to SST, some of which come from the
/// trait method. For those expressions, we need to perform substitutions on params and type params.
/// The `Lowerer` is a helper object which can be configured for either context: the current
/// function or the trait method.
struct Lowerer<'a, D: air::messages::Diagnostics> {
    function: Function,
    inherit: Option<InheritanceSubstitutions>,
    ens_pars: Pars,
    diagnostics: &'a D,
}

impl<'a, D> Lowerer<'a, D>
where
    D: air::messages::Diagnostics,
{
    fn current(function: &Function, ens_pars: &Pars, diagnostics: &'a D) -> Self {
        Lowerer {
            function: function.clone(),
            inherit: None,
            ens_pars: ens_pars.clone(),
            diagnostics,
        }
    }

    fn inheritance(
        ctx: &Ctx,
        function: &Function,
        ens_pars: &Pars,
        diagnostics: &'a D,
    ) -> Option<Self> {
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
                trait_typ_substs.insert(x.clone(), t.clone());
            }

            let trait_function = ctx.func_map[method].clone();

            let mut param_renames: HashMap<_, _> = trait_function
                .x
                .params
                .iter()
                .zip(function.x.params.iter())
                .map(|(p1, p2)| (p1.x.name.clone(), p2.x.name.clone()))
                .collect();
            param_renames
                .insert(trait_function.x.ret.x.name.clone(), function.x.ret.x.name.clone());

            let inherit = InheritanceSubstitutions { trait_typ_substs, param_renames };

            Some(Lowerer {
                function: trait_function,
                inherit: Some(inherit),
                ens_pars: ens_pars.clone(),
                diagnostics,
            })
        } else {
            None
        }
    }

    /// Lower a pure expression (e.g. from a requires clause)
    /// Outside of recommends checking:
    ///    this produces a pure SST expression, no Stms, no LocalDecls
    /// Inside recommends checking:
    ///    may produce local decls (appended to state.local_decls) and Stms (appended to stms)
    fn lower_pure(
        &self,
        ctx: &Ctx,
        state: &mut State,
        expr: &Expr,
        stms: &mut Vec<Stm>,
    ) -> Result<Exp, VirErr> {
        if ctx.checking_spec_preconditions() {
            match &self.inherit {
                None => {
                    let (mut stms0, exp) = expr_to_pure_exp_check(ctx, state, expr)?;
                    stms.append(&mut stms0);
                    Ok(exp)
                }
                Some(inh) => {
                    // REVIEW: This works, but it is likely confusing and brittle.
                    //
                    // We need to perform substitutions so that the expression from the trait
                    // function context makes sense in the trait implementation with has different
                    // argument names and type arguments.
                    //
                    // Right now, we: do the param renames, then do the lowering,
                    // then (inside the call `expr_to_pure_exp_check_with_substs`)
                    // do type param substitution, and fix up the local decls.
                    // Though it seems to work fine, it does mean that the main lowering step
                    // (i.e., the big recursive function over Expr in ast_to_sst)
                    // takes place in a weird "half-substituted" state.

                    let expr = map_expr_rename_vars(expr, &inh.param_renames)?;
                    let (mut stms0, exp) = expr_to_pure_exp_check_with_typ_substs(
                        ctx,
                        state,
                        &expr,
                        &inh.trait_typ_substs,
                    )?;

                    stms.append(&mut stms0);
                    Ok(exp)
                }
            }
        } else {
            // In this case, we don't modify the state
            // (expr_to_exp_skip_checks creates its own State object which is thrown away)
            match &self.inherit {
                None => {
                    let exp = expr_to_exp_skip_checks(ctx, self.diagnostics, &self.ens_pars, expr)?;
                    Ok(exp)
                }
                Some(inh) => {
                    let expr = map_expr_rename_vars(expr, &inh.param_renames)?;
                    let exp =
                        expr_to_exp_skip_checks(ctx, self.diagnostics, &self.ens_pars, &expr)?;
                    let exp = subst_exp(&inh.trait_typ_substs, &HashMap::new(), &exp);
                    Ok(exp)
                }
            }
        }
    }
}

impl MaskSpec {
    fn map_to_sst(
        &self,
        f: &mut impl FnMut(&Expr) -> Result<Exp, VirErr>,
    ) -> Result<MaskSet, VirErr> {
        let mask_set = match self {
            MaskSpec::InvariantOpens(span, exprs) => {
                let mut exps = vec![];
                for expr in exprs.iter() {
                    exps.push(f(expr)?);
                }
                MaskSet::from_list(&exps, &span)
            }
            MaskSpec::InvariantOpensExcept(span, exprs) => {
                let mut exps = vec![];
                for expr in exprs.iter() {
                    exps.push(f(expr)?);
                }
                MaskSet::from_list_complement(&exps, &span)
            }
            MaskSpec::InvariantOpensSet(expr) => {
                let exp = f(expr)?;
                MaskSet::arbitrary(&exp)
            }
        };
        Ok(mask_set)
    }
}

impl UnwindSpec {
    fn map_to_sst(
        &self,
        f: &mut impl FnMut(&Expr) -> Result<Exp, VirErr>,
    ) -> Result<UnwindSst, VirErr> {
        let unwind_sst = match self {
            UnwindSpec::NoUnwind => UnwindSst::NoUnwind,
            UnwindSpec::MayUnwind => UnwindSst::MayUnwind,
            UnwindSpec::NoUnwindWhen(expr) => UnwindSst::NoUnwindWhen(f(expr)?),
        };
        Ok(unwind_sst)
    }
}

impl UnwindSst {
    fn map(&self, f: &impl Fn(&Exp) -> Result<Exp, VirErr>) -> Result<UnwindSst, VirErr> {
        let unwind_sst = match self {
            UnwindSst::NoUnwind => UnwindSst::NoUnwind,
            UnwindSst::MayUnwind => UnwindSst::MayUnwind,
            UnwindSst::NoUnwindWhen(exp) => UnwindSst::NoUnwindWhen(f(exp)?),
        };
        Ok(unwind_sst)
    }
}

pub fn func_def_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    function: &Function,
    check_api_safety: bool,
) -> Result<FuncCheckSst, VirErr> {
    let body = if check_api_safety {
        &crate::safe_api::body_that_havocs_all_outputs(function)
    } else {
        match &function.x.body {
            Some(body) => body,
            _ => {
                panic!("func_def_to_sst should only be called for function with a body");
            }
        }
    };

    let mut state = State::new(diagnostics);

    let mut ens_params = (*function.x.params).clone();
    let dest = if function.x.ens_has_return {
        let ParamX { name, typ, .. } = &function.x.ret.x;
        ens_params.push(function.x.ret.clone());
        state.declare_var_stm(name, typ, LocalDeclKind::Return, false);
        Some(unique_local(name))
    } else {
        None
    };
    let ens_params = Arc::new(ens_params);
    let ens_pars = params_to_pars(&ens_params, true);

    for param in function.x.params.iter() {
        state.declare_var_stm(
            &param.x.name,
            &param.x.typ,
            LocalDeclKind::Param { mutable: param.x.is_mut },
            false,
        );
    }

    // This is used for lowering expressions from the function
    let lo_current = Lowerer::current(&function, &ens_pars, diagnostics);

    // This is used for lowering expressions from the *trait method* that this function
    // inherits a signature from. (If it exists.)
    let lo_inheritance = Lowerer::inheritance(ctx, &function, &ens_pars, diagnostics);
    let inherit = lo_inheritance.is_some();

    // For most kinds of specs (requires, unwind, mask), we always use the trait method
    // if it exists and otherwise use the original method.
    // The `lo_specs` is the appropriate Lowerer object for this case.
    let lo_specs = if inherit { &lo_inheritance.as_ref().unwrap() } else { &lo_current };
    let specs_function = lo_specs.function.clone();

    // These are used for the normal case (no recommends-checking)
    let mut reqs: Vec<Exp> = Vec::new();
    let mut enss: Vec<Exp> = Vec::new();

    // These are used for recommends-checking
    let mut req_stms: Vec<Stm> = Vec::new();
    let mut ens_spec_precondition_stms: Vec<Stm> = Vec::new();

    // Requires: take from trait method if it exists
    let requires = specs_function.x.require.clone();
    for r in requires.iter() {
        let r = lo_specs.lower_pure(ctx, &mut state, r, &mut req_stms)?;
        if ctx.checking_spec_preconditions() {
            req_stms.push(Spanned::new(r.span.clone(), StmX::Assume(r)));
        } else {
            reqs.push(r);
        }
    }

    // Inv mask: take from trait method if it exists
    let mask_ast = specs_function.x.mask_spec_or_default(&specs_function.span);
    let mask_sst = mask_ast
        .map_to_sst(&mut |expr| lo_specs.lower_pure(ctx, &mut state, expr, &mut req_stms))?;
    state.mask = Some(mask_sst);

    // Unwind spec: take from trait method if it exists
    let unwind_ast = specs_function.x.unwind_spec_or_default();
    let unwind_sst = unwind_ast
        .map_to_sst(&mut |expr| lo_specs.lower_pure(ctx, &mut state, expr, &mut req_stms))?;

    // Decreases: add recommends if necessary; otherwise nothing to do
    if ctx.checking_spec_preconditions() {
        for d in function.x.decrease.iter() {
            let _d = lo_current.lower_pure(ctx, &mut state, d, &mut req_stms)?;
        }
    }

    // Ensures: combine from both sources
    if let Some(lo_inheritance) = &lo_inheritance {
        // We're overriding req_ens_function, so we only inherit the non-default-ensures
        let non_default_ensure = &lo_inheritance.function.x.ensure.0.clone();
        for expr in non_default_ensure.iter() {
            let exp = lo_inheritance.lower_pure(
                ctx,
                &mut state,
                expr,
                &mut ens_spec_precondition_stms,
            )?;
            if !ctx.checking_spec_preconditions() {
                let exp = crate::heuristics::maybe_insert_auto_ext_equal(ctx, &exp, |x| x.ensures);
                enss.push(exp);
            }
        }
    }
    for expr in lo_current.function.x.ensure.0.iter().chain(lo_current.function.x.ensure.1.iter()) {
        let exp = lo_current.lower_pure(ctx, &mut state, expr, &mut ens_spec_precondition_stms)?;
        if !ctx.checking_spec_preconditions() {
            let exp = crate::heuristics::maybe_insert_auto_ext_equal(ctx, &exp, |x| x.ensures);
            enss.push(exp);
        }
    }

    if check_api_safety {
        let exps = crate::safe_api::axioms_for_default_spec_fns(ctx, diagnostics, function)?;
        reqs.extend(exps);
    }

    // AST --> SST
    let mut stm = expr_to_one_stm_with_post(&ctx, &mut state, &body, &function.span)?;

    // TODO handle via the Lowerer
    if ctx.checking_spec_preconditions() && !inherit {
        if let Some(fun) = &function.x.decrease_by {
            let decrease_by_fun = &ctx.func_map[fun];
            let (body_stms, _exp) = expr_to_stm_or_error(
                &ctx,
                &mut state,
                decrease_by_fun.x.body.as_ref().expect("decreases_by has body"),
            )?;
            req_stms.extend(body_stms);
        }
        req_stms.push(stm);
        stm = stms_to_one_stm(&body.span, req_stms);
    }

    let stm = state.finalize_stm(&ctx, &stm)?;
    let ens_spec_precondition_stms: Result<Vec<_>, _> =
        ens_spec_precondition_stms.iter().map(|s| state.finalize_stm(&ctx, &s)).collect();
    let ens_spec_precondition_stms = ens_spec_precondition_stms?;
    let unwind_sst = unwind_sst.map(&|e| state.finalize_exp(&ctx, e))?;

    // Check termination
    let exec_with_no_termination_check = function.x.mode == Mode::Exec
        && (function.x.attrs.exec_allows_no_decreases_clause
            || function.x.attrs.exec_assume_termination);
    let no_termination_check = function.x.decrease.len() == 0 && exec_with_no_termination_check;
    let (decls, local_decls_decreases_init, stm) =
        if no_termination_check || ctx.checking_spec_preconditions() || check_api_safety {
            (vec![], Arc::new(vec![]), stm)
        } else {
            crate::recursion::check_termination_stm(
                ctx,
                diagnostics,
                function,
                None,
                &stm,
                exec_with_no_termination_check,
            )?
        };

    let FinalState { mut local_decls, statics } = state.finalize();

    // SST --> AIR
    for decl in decls {
        local_decls.push(decl.clone());
    }

    Ok(FuncCheckSst {
        reqs: Arc::new(reqs),
        post_condition: Arc::new(PostConditionSst {
            dest,
            ens_exps: Arc::new(enss),
            ens_spec_precondition_stms: Arc::new(ens_spec_precondition_stms),
            kind: if check_api_safety {
                PostConditionKind::EnsuresSafeApiCheck
            } else {
                PostConditionKind::Ensures
            },
        }),
        unwind: unwind_sst,
        body: stm,
        local_decls: Arc::new(local_decls),
        local_decls_decreases_init,
        statics: Arc::new(statics.into_iter().collect()),
    })
}

pub fn function_to_sst(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    bucket_funs: &HashSet<Fun>,
    function: &Function,
) -> Result<FunctionSst, VirErr> {
    let module = ctx.module_path();
    let is_recursive = crate::recursion::fun_is_recursive(ctx, function);

    let verifying_owning_bucket = bucket_funs.contains(&function.x.name);
    ctx.fun = mk_fun_ctx(&function, false);
    let func_decl_sst = crate::ast_to_sst_func::func_decl_to_sst(ctx, diagnostics, function)?;
    ctx.fun = None;

    ctx.fun = mk_fun_ctx_dec(&function, false, true);
    let func_axioms_sst = crate::ast_to_sst_func::func_axioms_to_sst(
        ctx,
        diagnostics,
        function,
        is_body_visible_to(&function.x.body_visibility, &module),
        verifying_owning_bucket,
    )?;
    ctx.fun = None;

    let exec_proof_check = match (function.x.mode, function.x.body.is_some(), function.x.item_kind)
    {
        (Mode::Exec | Mode::Proof, true, _) | (Mode::Spec, true, ItemKind::Const) => {
            ctx.fun = mk_fun_ctx(&function, false);
            let def = crate::ast_to_sst_func::func_def_to_sst(ctx, diagnostics, function, false)?;
            ctx.fun = None;
            Some(Arc::new(def))
        }
        _ => None,
    };

    let recommends_check = match function.x.mode {
        Mode::Spec if !verifying_owning_bucket => None,
        Mode::Spec if !is_recursive && !function.x.attrs.check_recommends => None,
        _ if function.x.body.is_some() => {
            // We eagerly generate SST for recommends_check even if we might not use it.
            // Experiments with veritas indicate that this generally causes < 1% overhead.
            ctx.fun = mk_fun_ctx(&function, true);
            let def = crate::ast_to_sst_func::func_def_to_sst(ctx, diagnostics, function, false)?;
            ctx.fun = None;
            Some(Arc::new(def))
        }
        _ => None,
    };

    let safe_api_check = if crate::safe_api::function_has_obligation(ctx, function) {
        ctx.fun = mk_fun_ctx(&function, false);
        let def = crate::ast_to_sst_func::func_def_to_sst(ctx, diagnostics, function, true)?;
        ctx.fun = None;
        Some(Arc::new(def))
    } else {
        None
    };

    let has = FunctionSstHas {
        has_body: function.x.body.is_some(),
        has_requires: function.x.require.len() > 0,
        has_ensures: function.x.ensure.0.len() + function.x.ensure.1.len() > 0,
        has_decrease: function.x.decrease.len() > 0,
        has_mask_spec: function.x.mask_spec.is_some(),
        has_return_name: function.x.ens_has_return,
        is_recursive: crate::recursion::fun_is_recursive(ctx, function),
    };

    let functionx = FunctionSstX {
        name: function.x.name.clone(),
        kind: function.x.kind.clone(),
        body_visibility: function.x.body_visibility.clone(),
        owning_module: function.x.owning_module.clone(),
        mode: function.x.mode,
        opaqueness: function.x.opaqueness.clone(),
        typ_params: function.x.typ_params.clone(),
        typ_bounds: function.x.typ_bounds.clone(),
        pars: params_to_pars(&function.x.params, true),
        ret: param_to_par(&function.x.ret, true),
        ens_has_return: function.x.ens_has_return,
        item_kind: function.x.item_kind,
        attrs: function.x.attrs.clone(),
        has,
        decl: Arc::new(func_decl_sst),
        axioms: Arc::new(func_axioms_sst),
        exec_proof_check,
        recommends_check,
        safe_api_check,
    };
    Ok(function.new_x(functionx))
}
