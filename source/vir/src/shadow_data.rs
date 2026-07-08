use crate::ast::{
    Fun, FunctionKind, Mode, Primitive, SpannedTyped, Typ, TypX, UnaryOp, VarIdent,
    VarIdentDisambiguate, VirErr,
};
use crate::def::{Spanned, shadow_data_temp_var};
use crate::messages::{Span, error};
use crate::sst::{
    CallTarget, Dest, Exp, ExpX, FuncAxiomsSst, FuncCheckSst, FuncDeclSst, FunctionSst, LocalDecl,
    LocalDeclKind, LocalDeclX, Par, ParPurpose, ParX, PostConditionSst, Stm, StmX,
};
use crate::sst_visitor::{map_exp_visitor_result, map_stm_exp_visitor, map_stm_visitor};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

struct Ctxt {
    shadow_funs: Rc<HashSet<Fun>>,
    shadows: HashMap<VarIdent, VarIdent>,
    has_shadow_data: bool,
}

struct State {
    shadow_temps: Vec<Typ>,
}

impl State {
    fn havoc_ident(&mut self, typ: &Typ) -> VarIdent {
        let x = shadow_data_temp_var(self.shadow_temps.len() as u64);
        self.shadow_temps.push(typ.clone());
        x
    }
}

fn shadow_name(x: &VarIdent) -> VarIdent {
    let VarIdent(x, dis) = x;
    VarIdent(x.clone(), VarIdentDisambiguate::ShadowData(Box::new(dis.clone())))
}

fn shadow_typ(t: &Typ) -> Typ {
    Arc::new(TypX::Primitive(Primitive::ShadowData, Arc::new(vec![t.clone()])))
}

impl<X> SpannedTyped<X> {
    pub fn to_shadow(&self, x: X) -> Arc<SpannedTyped<X>> {
        let typ = shadow_typ(&self.typ);
        Arc::new(SpannedTyped { span: self.span.clone(), typ, x })
    }
}

fn shadow_data_exp(ctxt: &Ctxt, exp: &Exp) -> Result<Exp, VirErr> {
    match &exp.x {
        ExpX::Unary(UnaryOp::ShadowData, e) => match &e.x {
            ExpX::Var(x) => {
                if let Some(x_shadow) = ctxt.shadows.get(x) {
                    Ok(exp.new_x(ExpX::Var(x_shadow.clone())))
                } else {
                    Err(error(&exp.span, "unsupported shadow_data variable"))
                }
            }
            ExpX::VarAt(x, at) => {
                if let Some(x_shadow) = ctxt.shadows.get(x) {
                    Ok(exp.new_x(ExpX::VarAt(x_shadow.clone(), *at)))
                } else {
                    Err(error(&exp.span, "unsupported shadow_data variable"))
                }
            }
            _ => Err(error(&exp.span, "shadow_data expects a variable")),
        },
        _ => Ok(exp.clone()),
    }
}

// Shallowly update a single statement with shadow assignments and havocs
// Also add extra args, return value to calls
fn shadow_data_stm(ctxt: &Ctxt, state: &mut State, stm: &Stm) -> Stm {
    let mut extra: Vec<Stm> = Vec::new();
    let mut precise = false;
    let mut stmx = stm.x.clone();
    match &mut stmx {
        StmX::Call { fun, args, dest, .. } => {
            if let CallTarget::Fun(fun) = fun {
                if ctxt.shadow_funs.contains(fun) {
                    let mut new_args = (**args).clone();
                    for arg in args.iter() {
                        let mut arg_shadow: Option<VarIdent> = None;
                        if let ExpX::Var(arg_x) = &arg.x {
                            arg_shadow = ctxt.shadows.get(arg_x).cloned();
                        }
                        let arg_shadow = arg_shadow.unwrap_or_else(|| state.havoc_ident(&arg.typ));
                        new_args.push(arg.to_shadow(ExpX::Var(arg_shadow.clone())));
                    }
                    *args = Arc::new(new_args);

                    assert!(dest.len() <= 1);
                    if dest.len() == 1 {
                        let dest = Arc::make_mut(dest);
                        let mut dest_shadow: Option<VarIdent> = None;
                        if let ExpX::VarLoc(dest_x) = &dest[0].dest.x {
                            dest_shadow = ctxt.shadows.get(dest_x).cloned();
                            precise = true;
                        }
                        // If we don't have a precise shadow destination, dump into a havoc dest
                        // in order to ignore the shadow result.
                        // Example 1: we're in a non-shadow_data caller who ignores shadow data
                        // Example 2: a shadow_data caller has a complex dest,
                        //   which gets havoc'd below under "!precise"
                        let dest_shadow =
                            dest_shadow.unwrap_or_else(|| state.havoc_ident(&dest[0].dest.typ));
                        let dest_exp = dest[0].dest.to_shadow(ExpX::VarLoc(dest_shadow));
                        let dest_shadow = Dest { dest: dest_exp, is_init: dest[0].is_init };
                        dest.push(dest_shadow);
                    }
                }
            }
        }
        StmX::Assign { lhs, rhs } => {
            if let ExpX::VarLoc(lhs_x) = &lhs.dest.x {
                if let Some(lhs_shadow) = ctxt.shadows.get(lhs_x) {
                    if let ExpX::Var(rhs_x) = &rhs.x {
                        if let Some(rhs_shadow) = ctxt.shadows.get(rhs_x) {
                            precise = true;
                            let lhs_exp = lhs.dest.to_shadow(ExpX::VarLoc(lhs_shadow.clone()));
                            let dest = Dest { dest: lhs_exp, is_init: lhs.is_init };
                            let rhs_exp = rhs.to_shadow(ExpX::Var(rhs_shadow.clone()));
                            let stmx = StmX::Assign { lhs: dest, rhs: rhs_exp };
                            extra.push(stm.new_x(stmx));
                        }
                    }
                }
            }
        }
        StmX::Return { ret_exp, .. } if ctxt.has_shadow_data => {
            assert!(ret_exp.len() <= 1);
            if ret_exp.len() == 1 {
                let ret_exp = Arc::make_mut(ret_exp);
                let mut ret_shadow: Option<VarIdent> = None;
                if let ExpX::Var(ret_x) = &ret_exp[0].x {
                    ret_shadow = ctxt.shadows.get(ret_x).cloned();
                }
                let ret_shadow = ret_shadow.unwrap_or_else(|| state.havoc_ident(&ret_exp[0].typ));
                ret_exp.push(ret_exp[0].to_shadow(ExpX::Var(ret_shadow)));
            }
        }
        _ => {}
    };
    let stm = stm.new_x(stmx);
    if !precise {
        for lhs in crate::sst_vars::stm_get_dest_shallow(&stm).iter() {
            let lhs_x = crate::sst_vars::get_loc_var(&lhs.dest);
            if let Some(lhs_shadow) = ctxt.shadows.get(&lhs_x) {
                let rhs_shadow = state.havoc_ident(&lhs.dest.typ);
                let lhs_exp = lhs.dest.to_shadow(ExpX::VarLoc(lhs_shadow.clone()));
                let dest = Dest { dest: lhs_exp, is_init: lhs.is_init };
                let rhs_exp = lhs.dest.to_shadow(ExpX::Var(rhs_shadow));
                let stmx = StmX::Assign { lhs: dest, rhs: rhs_exp };
                extra.push(stm.new_x(stmx));
            }
        }
    }
    if extra.len() == 0 {
        stm.clone()
    } else {
        extra.insert(0, stm.clone());
        let stmx = StmX::Block(Arc::new(extra));
        stm.new_x(stmx)
    }
}

fn add_to_pars(pars: &mut Vec<Par>, span: &Span) {
    for p in pars.clone().into_iter() {
        let name = shadow_name(&p.x.name);
        let parx = ParX {
            name,
            typ: shadow_typ(&p.x.typ),
            mode: Mode::Spec,
            purpose: ParPurpose::Regular,
        };
        pars.push(Spanned::new(span.clone(), parx.clone()));
    }
}

fn shadow_data_fun_decl(
    shadow_funs: Rc<HashSet<Fun>>,
    fun_decl: &mut FuncDeclSst,
    span: &Span,
) -> Result<(), VirErr> {
    let mut shadows: HashMap<VarIdent, VarIdent> = HashMap::new();
    for x in fun_decl.ens_pars.iter() {
        let y_ident = shadow_name(&x.x.name);
        assert!(!shadows.contains_key(&x.x.name));
        shadows.insert(x.x.name.clone(), y_ident.clone());
    }
    let ctxt = Ctxt { shadow_funs, shadows, has_shadow_data: true };
    let f_exp = |e: &Exp| {
        let mut f = |e: &Exp| shadow_data_exp(&ctxt, e);
        map_exp_visitor_result(e, &mut f)
    };

    let n_params = fun_decl.req_inv_pars.len();
    add_to_pars(Arc::make_mut(&mut fun_decl.req_inv_pars), &span);
    let ens_pars = Arc::make_mut(&mut fun_decl.ens_pars);
    let mut rets = ens_pars.split_off(n_params);
    add_to_pars(ens_pars, &span);
    add_to_pars(&mut rets, &span);
    ens_pars.append(&mut rets);

    for req in Arc::make_mut(&mut fun_decl.reqs).iter_mut() {
        *req = f_exp(req)?;
    }
    for ens in Arc::make_mut(&mut fun_decl.enss.0).iter_mut() {
        *ens = f_exp(ens)?;
    }
    for ens in Arc::make_mut(&mut fun_decl.enss.1).iter_mut() {
        *ens = f_exp(ens)?;
    }
    if let Some(unwind_condition) = &mut fun_decl.unwind_condition {
        *unwind_condition = f_exp(unwind_condition)?;
    }

    // For now, just disable call_requires/call_ensures axioms:
    // (In the future, maybe we could try to generate proper axioms.)
    fun_decl.fndef_axioms = Arc::new(vec![]);

    Ok(())
}

fn shadow_data_fun_check_stms(
    ctxt: &Ctxt,
    state: &mut State,
    fun_check: &mut FuncCheckSst,
) -> Result<(), VirErr> {
    let post_condition = Arc::make_mut(&mut fun_check.post_condition);
    let body = &mut fun_check.body;
    let mut f_stm = |s: &Stm| Ok(shadow_data_stm(ctxt, state, s));
    let PostConditionSst { dest: _, ens_exps: _, ens_spec_precondition_stms, kind: _ } =
        post_condition;
    for stm in Arc::make_mut(ens_spec_precondition_stms).iter_mut() {
        *stm = map_stm_visitor(stm, &mut f_stm)?;
    }
    *body = map_stm_visitor(body, &mut f_stm)?;

    Ok(())
}

fn declare_havocs(state: &State, local_decls: &mut Vec<LocalDecl>) {
    for (i, typ) in state.shadow_temps.iter().enumerate() {
        let x = LocalDeclX {
            ident: shadow_data_temp_var(i as u64),
            typ: shadow_typ(typ),
            kind: LocalDeclKind::Nondeterministic,
        };
        local_decls.push(Arc::new(x));
    }
}

fn no_shadow_data_fun_check(
    shadow_funs: Rc<HashSet<Fun>>,
    fun_check: &mut FuncCheckSst,
) -> Result<(), VirErr> {
    let ctxt = Ctxt { shadow_funs, shadows: HashMap::new(), has_shadow_data: false };
    let mut state = State { shadow_temps: Vec::new() };
    shadow_data_fun_check_stms(&ctxt, &mut state, fun_check)?;
    declare_havocs(&state, Arc::make_mut(&mut fun_check.local_decls));

    Ok(())
}

fn shadow_data_fun_check(
    shadow_funs: Rc<HashSet<Fun>>,
    fun_check: &mut FuncCheckSst,
) -> Result<(), VirErr> {
    let mut shadows: HashMap<VarIdent, VarIdent> = HashMap::new();
    let local_decls = Arc::make_mut(&mut fun_check.local_decls);
    for x in local_decls.clone() {
        match &x.kind {
            LocalDeclKind::Param { .. }
            | LocalDeclKind::Return
            | LocalDeclKind::StmtLet { .. }
            | LocalDeclKind::TempViaAssign
            | LocalDeclKind::StmCallArg { .. } => {
                let y_ident = shadow_name(&x.ident);
                assert!(!shadows.contains_key(&x.ident));
                shadows.insert(x.ident.clone(), y_ident.clone());
                let y = LocalDeclX { ident: y_ident, typ: shadow_typ(&x.typ), kind: x.kind };
                local_decls.push(Arc::new(y));
            }
            _ => {}
        }
    }
    let ctxt = Ctxt { shadow_funs, shadows, has_shadow_data: true };
    let mut state = State { shadow_temps: Vec::new() };

    shadow_data_fun_check_stms(&ctxt, &mut state, fun_check)?;

    let reqs = Arc::make_mut(&mut fun_check.reqs);
    let post_condition = Arc::make_mut(&mut fun_check.post_condition);
    let body = &mut fun_check.body;
    let local_decls = Arc::make_mut(&mut fun_check.local_decls);

    let mut f_exp = |e: &Exp| {
        let mut f = |e: &Exp| shadow_data_exp(&ctxt, e);
        map_exp_visitor_result(e, &mut f)
    };
    for req in reqs.iter_mut() {
        *req = f_exp(req)?;
    }
    let PostConditionSst { dest, ens_exps, ens_spec_precondition_stms, kind: _ } = post_condition;
    assert!(dest.len() <= 1);
    if dest.len() == 1 {
        let shadow_dest = shadow_name(&dest[0]);
        dest.push(shadow_dest);
    }
    for ens in Arc::make_mut(ens_exps).iter_mut() {
        *ens = f_exp(ens)?;
    }
    for stm in Arc::make_mut(ens_spec_precondition_stms).iter_mut() {
        *stm = map_stm_exp_visitor(stm, &mut f_exp)?;
    }
    *body = map_stm_exp_visitor(body, &mut f_exp)?;

    declare_havocs(&state, local_decls);

    Ok(())
}

fn no_shadow_data_function(
    shadow_funs: Rc<HashSet<Fun>>,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let functionx = &mut Arc::make_mut(function).x;

    if let Some(exec_proof_check) = &mut functionx.exec_proof_check {
        no_shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }
    if let Some(exec_proof_check) = &mut functionx.recommends_check {
        no_shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }
    if let Some(exec_proof_check) = &mut functionx.safe_api_check {
        no_shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }

    Ok(())
}

fn shadow_data_function(
    shadow_funs: Rc<HashSet<Fun>>,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    let span = function.span.clone();
    let functionx = &mut Arc::make_mut(function).x;

    if functionx.mode == Mode::Spec {
        return Err(error(&span, "shadow_data only allowed for exec and proof functions"));
    }
    if !matches!(functionx.item_kind, crate::ast::ItemKind::Function) {
        return Err(error(&span, "shadow_data only allowed for functions, not const or static"));
    }

    add_to_pars(Arc::make_mut(&mut functionx.pars), &span);
    add_to_pars(Arc::make_mut(&mut functionx.ret), &span);
    shadow_data_fun_decl(shadow_funs.clone(), Arc::make_mut(&mut functionx.decl), &span)?;

    if let Some(exec_proof_check) = &mut functionx.exec_proof_check {
        shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }
    if let Some(exec_proof_check) = &mut functionx.recommends_check {
        shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }
    if let Some(exec_proof_check) = &mut functionx.safe_api_check {
        shadow_data_fun_check(shadow_funs.clone(), Arc::make_mut(exec_proof_check))?;
    }
    let FuncAxiomsSst { spec_axioms, proof_exec_axioms } = &*functionx.axioms;
    assert!(spec_axioms.is_none());
    assert!(proof_exec_axioms.is_none());

    Ok(())
}

pub(crate) fn shadow_data_function_sst(
    shadow_funs: &Rc<HashSet<Fun>>,
    function: &mut FunctionSst,
) -> Result<(), VirErr> {
    if shadow_funs.contains(&function.x.name) {
        shadow_data_function(shadow_funs.clone(), function)?;
    } else if function.x.mode == Mode::Exec && shadow_funs.len() != 0 {
        no_shadow_data_function(shadow_funs.clone(), function)?;
    }

    Ok(())
}

pub(crate) fn shadow_data_funs(krate: &crate::ast::Krate) -> Result<Rc<HashSet<Fun>>, VirErr> {
    let mut shadow_funs: HashSet<Fun> = HashSet::new();
    for f in krate.functions.iter() {
        if f.x.attrs.has_shadow_data {
            if let FunctionKind::TraitMethodImpl { .. } = &f.x.kind {
                return Err(error(&f.span, "shadow_data only allowed in trait, not in impl"));
            }
            shadow_funs.insert(f.x.name.clone());
        }
    }
    for f in krate.functions.iter() {
        if let FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if shadow_funs.contains(method) {
                shadow_funs.insert(f.x.name.clone());
            }
        }
    }
    Ok(Rc::new(shadow_funs))
}
