use crate::ast::{
    ComputeMode, Fun, Ident, Mode, SpannedTyped, Typ, TypX, UnaryOp, VarIdent, VirErr,
};
use crate::ast_to_sst_func::SstMap;
use crate::context::Ctx;
use crate::def::{Spanned, unique_local};
use crate::messages::{ToAny, error_with_label, warning};
use crate::sst::{BndX, CallFun, Exp, ExpX, FuncCheckSst, FunctionSst, Stm, StmX, UniqueIdent};
use crate::sst_visitor::{NoScoper, Rewrite, Visitor};
use crate::triggers::build_triggers;
use crate::util::vec_map_result;
use crate::visitor::Returner;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::sync::Arc;

fn elaborate_one_exp<D: Diagnostics + ?Sized>(
    ctx: &Ctx,
    diagnostics: &D,
    fun_ssts: &HashMap<Fun, FunctionSst>,
    is_native: &mut Option<HashMap<VarIdent, bool>>,
    exp: &Exp,
) -> Result<Exp, VirErr> {
    match &exp.x {
        ExpX::Call(CallFun::Fun(fun, resolved_method), typs, args) => {
            let (fun, typs) =
                if let Some((f, ts)) = resolved_method { (f, ts) } else { (fun, typs) };
            if let Some(func) = fun_ssts.get(fun)
                && let Some(spec_axioms) = func.x.axioms.spec_axioms.as_ref()
                && func.x.attrs.inline
                && func.x.kind.inline_okay()
            {
                let typ_params = &func.x.typ_params;
                let pars = &func.x.pars;
                let body = &spec_axioms.body_exp;
                let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
                let mut substs: HashMap<UniqueIdent, Exp> = HashMap::new();
                assert!(typ_params.len() == typs.len());
                for (name, typ) in typ_params.iter().zip(typs.iter()) {
                    assert!(!typ_substs.contains_key(name));
                    typ_substs.insert(name.clone(), typ.clone());
                }
                assert!(pars.len() == args.len());
                for (par, arg) in pars.iter().zip(args.iter()) {
                    let unique = unique_local(&par.x.name);
                    assert!(!substs.contains_key(&unique));
                    substs.insert(unique, arg.clone());
                }
                let e = crate::sst_util::subst_exp(&typ_substs, &substs, body);
                // keep the original outer span for better trigger messages
                // keep the original type so that poly.rs can perform the proper box/unbox on e
                let e = SpannedTyped::new(&exp.span, &exp.typ, e.x.clone());
                return Ok(e);
            }
            Ok(exp.clone())
        }
        ExpX::Bind(bnd, body) => match &bnd.x {
            BndX::Quant(quant, bs, trigs, assert_by_vars) => {
                assert!(trigs.len() == 0);
                let mut vars: Vec<VarIdent> = Vec::new();
                for b in bs.iter() {
                    match &*b.a {
                        TypX::TypeId => vars.push(crate::def::suffix_typ_param_var(&b.name)),
                        _ => vars.push(b.name.clone()),
                    }
                }
                let trigs = build_triggers(ctx, &exp.span, &vars, &body, false)?;
                if let Some(assert_by_vars) = assert_by_vars {
                    let natives = crate::triggers::native_quant_vars(bs, &trigs);
                    assert!(assert_by_vars.len() == bs.len());
                    for (x, b) in assert_by_vars.iter().zip(bs.iter()) {
                        let native = natives.contains(&b.name);
                        if let Some(is_native) = is_native {
                            if let Some(n) = is_native.insert(x.clone(), native) {
                                assert!(n == native);
                            }
                        }
                    }
                }
                let bnd =
                    Spanned::new(bnd.span.clone(), BndX::Quant(*quant, bs.clone(), trigs, None));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            BndX::Choose(bs, trigs, cond) => {
                assert!(trigs.len() == 0);
                let vars = bs.iter().map(|b| b.name.clone()).collect();
                let trigs = build_triggers(ctx, &exp.span, &vars, &cond, false)?;
                let bnd =
                    Spanned::new(bnd.span.clone(), BndX::Choose(bs.clone(), trigs, cond.clone()));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            BndX::Lambda(bs, trigs) => {
                assert!(trigs.len() == 0);
                let vars = bs.iter().map(|b| b.name.clone()).collect();
                let trigs = build_triggers(ctx, &exp.span, &vars, &body, true)?;
                if trigs.len() > 0 {
                    let msg = "#[trigger] on a spec_fn closure is deprecated - \
                        generally spec_fn closures don't need triggers because spec_fn \
                        closures are triggered automatically by calls to to closures. \
                        If you think you need additional triggers, see the discussion in \
                        https://github.com/verus-lang/verus/pull/331 \
                        for alternatives.";
                    diagnostics.report(&warning(&exp.span, msg).to_any());
                }
                let bnd = Spanned::new(bnd.span.clone(), BndX::Lambda(bs.clone(), trigs));
                Ok(SpannedTyped::new(&exp.span, &exp.typ, ExpX::Bind(bnd, body.clone())))
            }
            _ => Ok(exp.clone()),
        },
        // remove MustBeElaborated marker to vouch that elaborate_one_exp was called
        ExpX::Unary(UnaryOp::MustBeElaborated, e1) => Ok(e1.clone()),
        _ => Ok(exp.clone()),
    }
}

fn elaborate_one_stm<D: Diagnostics + ?Sized>(
    ctx: &Ctx,
    diagnostics: &D,
    fun_ssts: &SstMap,
    stm: &Stm,
) -> Result<Stm, VirErr> {
    match &stm.x {
        StmX::AssertCompute(id, exp, compute) => {
            let interp_exp = crate::interpreter::eval_expr(
                &ctx.global,
                exp,
                Some(diagnostics),
                fun_ssts.clone(),
                ctx.global.rlimit,
                ctx.global.arch,
                *compute,
                &mut ctx.global.interpreter_log.lock().unwrap(),
            )?;
            let err = error_with_label(
                &exp.span.clone(),
                "assertion failed",
                format!("simplified to {}", interp_exp.x.to_user_string(&ctx.global)),
            );
            match compute {
                ComputeMode::Z3 => Ok(stm.new_x(StmX::Assert(id.clone(), Some(err), interp_exp))),
                ComputeMode::ComputeOnly => Ok(stm.new_x(StmX::Block(Arc::new(vec![])))),
            }
        }
        StmX::AssertBitVector { requires, ensures } => {
            if ctx.global.no_bv_simplify {
                return Ok(stm.clone());
            }
            let reqs = vec_map_result(requires, |e| {
                crate::interpreter::eval_expr(
                    &ctx.global,
                    e,
                    None::<&air::messages::Reporter>, // Don't print (internal) diagnostics
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    crate::ast::ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                )
            })?;
            let ens = vec_map_result(ensures, |e| {
                crate::interpreter::eval_expr(
                    &ctx.global,
                    e,
                    None::<&air::messages::Reporter>, // Don't print (internal) diagnostics
                    fun_ssts.clone(),
                    ctx.global.rlimit,
                    ctx.global.arch,
                    crate::ast::ComputeMode::Z3,
                    &mut ctx.global.interpreter_log.lock().unwrap(),
                )
            })?;
            Ok(stm.new_x(StmX::AssertBitVector { requires: reqs.into(), ensures: ens.into() }))
        }
        _ => Ok(stm.clone()),
    }
}

struct ElaborateVisitor1<'a, 'b, 'c, D: Diagnostics> {
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: &'c HashMap<Fun, FunctionSst>,
    is_native: Option<HashMap<VarIdent, bool>>,
}

impl<'a, 'b, 'c, D: Diagnostics> Visitor<Rewrite, VirErr, NoScoper>
    for ElaborateVisitor1<'a, 'b, 'c, D>
{
    fn visit_exp(&mut self, exp: &Exp) -> Result<Exp, VirErr> {
        let exp = self.visit_exp_rec(exp)?;
        elaborate_one_exp(self.ctx, self.diagnostics, &self.fun_ssts, &mut self.is_native, &exp)
    }

    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        self.visit_stm_rec(stm)
    }

    fn visit_func_check(&mut self, def: &FuncCheckSst) -> Result<FuncCheckSst, VirErr> {
        self.is_native = Some(HashMap::new());
        let reqs = self.visit_exps(&def.reqs)?;
        let post_condition = self.visit_postcondition(&def.post_condition)?;
        let body = self.visit_stm(&def.body)?;
        let local_decls =
            Rewrite::map_vec(&def.local_decls, &mut |decl| self.visit_local_decl(decl))?;
        let local_decls_decreases_init = self.visit_stms(&def.local_decls_decreases_init)?;
        let unwind = self.visit_unwind(&def.unwind)?;
        let is_native = self.is_native.take().expect("is_native");

        let mut def = FuncCheckSst {
            reqs: Arc::new(reqs),
            post_condition: Arc::new(post_condition),
            unwind,
            body,
            local_decls: Arc::new(local_decls),
            local_decls_decreases_init: Arc::new(local_decls_decreases_init),
            statics: def.statics.clone(),
        };

        rewrite_locals(&is_native, &mut def);

        Ok(def)
    }
}

fn rewrite_locals(is_native: &HashMap<VarIdent, bool>, function: &mut crate::sst::FuncCheckSst) {
    for local in Arc::make_mut(&mut function.local_decls) {
        use crate::sst::LocalDeclKind;
        if matches!(local.kind, LocalDeclKind::AssertByVar { .. }) {
            let native = is_native[&local.ident];
            Arc::make_mut(local).kind = LocalDeclKind::AssertByVar { native };
        }
    }
}

struct ElaborateVisitor2<'a, 'b, D: Diagnostics> {
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: SstMap,
}

impl<'a, 'b, D: Diagnostics> Visitor<Rewrite, VirErr, NoScoper> for ElaborateVisitor2<'a, 'b, D> {
    fn visit_stm(&mut self, stm: &Stm) -> Result<Stm, VirErr> {
        let stm = self.visit_stm_rec(stm)?;
        elaborate_one_stm(self.ctx, self.diagnostics, &self.fun_ssts, &stm)
    }
}

// Triggers and inlining
pub(crate) fn elaborate_function1<'a, 'b, 'c, D: Diagnostics>(
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: &'c HashMap<Fun, FunctionSst>,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let mut visitor = ElaborateVisitor1 { ctx, diagnostics, fun_ssts, is_native: None };
    *function = visitor.visit_function(function)?;

    if function.x.axioms.proof_exec_axioms.is_some() {
        let typ_params = function.x.typ_params.clone();
        let span = function.span.clone();
        let axioms = Arc::make_mut(&mut Arc::make_mut(function).x.axioms);
        let (params, exp, triggers) = axioms.proof_exec_axioms.as_ref().unwrap();
        assert!(triggers.len() == 0);
        let mut vars: Vec<VarIdent> = Vec::new();
        for name in typ_params.iter() {
            vars.push(crate::def::suffix_typ_param_id(&name));
        }
        for param in params.iter() {
            vars.push(param.x.name.clone());
        }
        let triggers = build_triggers(ctx, &span, &vars, exp, false)?;
        axioms.proof_exec_axioms = Some((params.clone(), exp.clone(), triggers));
    }

    Ok(())
}

// Compute and rewrite-recursive-calls
pub(crate) fn elaborate_function_rewrite_recursive<'a, 'b, D: Diagnostics>(
    ctx: &'a Ctx,
    diagnostics: &'b D,
    fun_ssts: SstMap,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let mut visitor = ElaborateVisitor2 { ctx, diagnostics, fun_ssts };
    *function = visitor.visit_function(function)?;

    if function.x.has.is_recursive && function.x.mode == Mode::Spec {
        let function_ref = &function.clone();
        let axioms = Arc::make_mut(&mut Arc::make_mut(function).x.axioms);
        if let Some(spec_body) = &mut axioms.spec_axioms {
            // Rewrite recursive calls to use fuel
            let (body_exp, _) = crate::recursion::rewrite_spec_recursive_fun_with_fueled_rec_call(
                ctx,
                function_ref,
                &spec_body.body_exp,
            )?;
            spec_body.body_exp = body_exp;
        }
    }

    Ok(())
}

// Expand expressions using the interpreter
fn expand<'a>(ctx: &'a Ctx, fun_ssts: &SstMap, exps: Vec<Exp>) -> Result<Vec<Exp>, VirErr> {
    vec_map_result(&exps, |e| {
        crate::interpreter::eval_expr(
            &ctx.global,
            e,
            None::<&air::messages::Reporter>,
            fun_ssts.clone(),
            ctx.global.rlimit,
            ctx.global.arch,
            crate::ast::ComputeMode::Z3,
            &mut ctx.global.interpreter_log.lock().unwrap(),
        )
    })
}

// Use the interpreter to inline spec functions (and otherwise apply its usual simplifications)
// to bit-vector assertions/proofs
pub(crate) fn elaborate_function_bv<'a>(
    ctx: &'a Ctx,
    fun_ssts: SstMap,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    if function.x.attrs.bit_vector {
        if let Some(exec_proof_check_arc) = &mut Arc::make_mut(function).x.exec_proof_check {
            let exec_proof_check_mut = Arc::make_mut(exec_proof_check_arc);
            // Expand reqs and ens_exps using the interpreter
            let reqs = expand(ctx, &fun_ssts, exec_proof_check_mut.reqs.to_vec())?;
            let ens_exps =
                expand(ctx, &fun_ssts, exec_proof_check_mut.post_condition.ens_exps.to_vec())?;

            // Update the exec_proof_check fields directly
            exec_proof_check_mut.reqs = Arc::new(reqs);
            let post = Arc::make_mut(&mut exec_proof_check_mut.post_condition);
            post.ens_exps = Arc::new(ens_exps);
        }
    }
    Ok(())
}
