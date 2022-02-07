use crate::ast::{
    BinaryOp, CallTarget, Constant, Expr, ExprX, Fun, Function, Ident, Mode, PatternX,
    SpannedTyped, Stmt, StmtX, Typ, TypX, Typs, UnaryOp, UnaryOpr, VarAt, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{
    Bnd, BndX, Dest, Exp, ExpX, Exps, LocalDecl, LocalDeclX, ParPurpose, Pars, Stm, StmX,
    UniqueIdent,
};
use crate::sst_visitor::{map_exp_visitor, map_stm_exp_visitor};
use crate::util::{vec_map, vec_map_result};
use air::ast::{Binder, BinderX, Binders, Quant, Span};
use air::errors::error_with_label;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

type Arg = (Exp, Typ);
type Args = Arc<Vec<Arg>>;

pub(crate) struct State {
    // Counter to generate temporary variables
    next_var: u64,
    // Collect all local variable declarations
    pub(crate) local_decls: Vec<LocalDecl>,
    // Rename local variables when needed, using unique integers, to avoid collisions.
    // This is only needed for statement-level declarations (Some(unique_int)),
    // not for expression-level bindings (None).
    rename_map: ScopeMap<Ident, Option<u64>>,
    // Next integer to use for renaming each variable
    rename_counters: HashMap<Ident, u64>,
    // Variables that we considered renaming, but ended up being Bind variables
    // rather than LocalDecls
    dont_rename: HashSet<UniqueIdent>,
    // If we allow return expressions, this is the return variable and ensures clauses:
    pub(crate) ret_post: Option<(Option<UniqueIdent>, Exps)>,
}

impl State {
    pub fn new() -> Self {
        let mut rename_map = ScopeMap::new();
        rename_map.push_scope(true);
        State {
            next_var: 0,
            local_decls: Vec::new(),
            rename_map,
            rename_counters: HashMap::new(),
            dont_rename: HashSet::new(),
            ret_post: None,
        }
    }

    fn next_temp(&mut self, span: &Span, typ: &Typ) -> (Ident, Exp) {
        self.next_var += 1;
        let x = crate::def::prefix_temp_var(self.next_var);
        (x.clone(), SpannedTyped::new(span, typ, ExpX::Var((x.clone(), Some(0)))))
    }

    pub(crate) fn push_scope(&mut self) {
        self.rename_map.push_scope(true);
    }

    pub(crate) fn pop_scope(&mut self) {
        self.rename_map.pop_scope();
    }

    pub(crate) fn get_var_unique_id(&self, x: &Ident) -> UniqueIdent {
        match self.rename_map.get(x) {
            None => panic!("internal error: variable not in rename_map: {}", x),
            Some(id) => (x.clone(), *id),
        }
    }

    pub(crate) fn new_statement_var(&mut self, x: &Ident) {
        self.rename_counters.insert(x.clone(), 0);
        self.rename_map.insert(x.clone(), Some(0)).expect("new var");
    }

    pub(crate) fn declare_expression_var(&mut self, x: &Ident) {
        self.rename_map.insert(x.clone(), None).expect("declare var");
    }

    pub(crate) fn alloc_unique_var(&mut self, x: &Ident) -> UniqueIdent {
        let i = match self.rename_counters.get(x).copied() {
            None => 0,
            Some(i) => i + 1,
        };
        self.rename_counters.insert(x.clone(), i);
        (x.clone(), Some(i))
    }

    pub(crate) fn insert_unique_var(&mut self, x: &UniqueIdent) {
        self.rename_map.insert(x.0.clone(), x.1).expect("declare var");
    }

    pub(crate) fn declare_binders<A: Clone>(&mut self, binders: &Binders<A>) {
        for binder in binders.iter() {
            self.declare_expression_var(&binder.name);
        }
    }

    pub(crate) fn declare_new_var(
        &mut self,
        ident: &Ident,
        typ: &Typ,
        mutable: bool,
        may_need_rename: bool,
    ) -> UniqueIdent {
        let unique_ident = if may_need_rename {
            let id = self.alloc_unique_var(ident);
            self.insert_unique_var(&id);
            id
        } else {
            self.new_statement_var(&ident);
            (ident.clone(), Some(0))
        };
        let decl = LocalDeclX { ident: unique_ident.clone(), typ: typ.clone(), mutable };
        self.local_decls.push(Arc::new(decl));
        unique_ident
    }

    // Erase unused unique ids from Vars
    pub(crate) fn finalize_exp(&self, exp: &Exp) -> Exp {
        map_exp_visitor(exp, &mut |exp| match &exp.x {
            ExpX::Var(x) if self.dont_rename.contains(&x) => {
                SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var((x.0.clone(), None)))
            }
            _ => exp.clone(),
        })
    }

    // Erase unused unique ids from Vars
    pub(crate) fn finalize_stm(&self, stm: &Stm) -> Stm {
        map_stm_exp_visitor(stm, &|exp| self.finalize_exp(exp)).expect("finalize_stm")
    }

    pub(crate) fn finalize(&mut self) {
        self.pop_scope();
        assert_eq!(self.rename_map.num_scopes(), 0);
    }
}

fn init_var(span: &Span, x: &UniqueIdent, exp: &Exp) -> Stm {
    let lhs = x.clone();
    Spanned::new(span.clone(), StmX::Assign { lhs, rhs: exp.clone(), is_init: true })
}

fn get_function(ctx: &Ctx, expr: &Expr, name: &Fun) -> Result<Function, VirErr> {
    match ctx.func_map.get(name) {
        None => err_string(&expr.span, format!("could not find function {:?}", &name)),
        Some(func) => Ok(func.clone()),
    }
}

fn function_can_be_exp(ctx: &Ctx, expr: &Expr, path: &Fun) -> Result<bool, VirErr> {
    match get_function(ctx, expr, path)?.x.mode {
        Mode::Spec => Ok(true),
        Mode::Proof | Mode::Exec => Ok(false),
    }
}

fn expr_get_call(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Fun, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::FnSpec(..), _) => {
            panic!("internal error: CallTarget::FnSpec")
        }
        ExprX::Call(CallTarget::Static(x, typs), args) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut exps: Vec<Arg> = Vec::new();
            for arg in args.iter() {
                let (mut stms0, e0) = expr_to_stm(ctx, state, arg)?;
                stms.append(&mut stms0);
                exps.push((e0, arg.typ.clone()));
            }
            let has_ret = get_function(ctx, expr, x)?.x.has_return();
            Ok(Some((stms, x.clone(), typs.clone(), has_ret, Arc::new(exps))))
        }
        _ => Ok(None),
    }
}

// If the Expr is a call that must be a Stm (not an Exp), return it
fn expr_must_be_call_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Fun, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Static(x, _), _) if !function_can_be_exp(ctx, expr, x)? => {
            expr_get_call(ctx, state, expr)
        }
        _ => Ok(None),
    }
}

pub(crate) fn expr_to_exp_state(ctx: &Ctx, state: &mut State, expr: &Expr) -> Result<Exp, VirErr> {
    let (stms, exp) = expr_to_stm(ctx, state, expr)?;
    if stms.len() == 0 {
        Ok(exp)
    } else {
        err_str(&expr.span, "expected pure mathematical expression")
    }
}

pub(crate) fn expr_to_decls_exp(
    ctx: &Ctx,
    params: &Pars,
    expr: &Expr,
) -> Result<(Vec<LocalDecl>, Exp), VirErr> {
    let mut state = State::new();
    for param in params.iter() {
        if !matches!(param.x.purpose, ParPurpose::MutPost) {
            state.declare_new_var(&param.x.name, &param.x.typ, false, false);
        }
    }
    let exp = expr_to_exp_state(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(&exp);
    state.finalize();
    Ok((state.local_decls, exp))
}

pub(crate) fn expr_to_bind_decls_exp(ctx: &Ctx, params: &Pars, expr: &Expr) -> Result<Exp, VirErr> {
    let mut state = State::new();
    for param in params.iter() {
        let id = state.declare_new_var(&param.x.name, &param.x.typ, false, false);
        state.dont_rename.insert(id);
    }
    let exp = expr_to_exp_state(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(&exp);
    state.finalize();
    Ok(exp)
}

pub(crate) fn expr_to_exp(ctx: &Ctx, params: &Pars, expr: &Expr) -> Result<Exp, VirErr> {
    Ok(expr_to_decls_exp(ctx, params, expr)?.1)
}

pub(crate) fn expr_to_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    let (stms, exp_opt) = expr_to_stm_opt(ctx, state, expr)?;
    if let Some(exp) = exp_opt {
        Ok((stms, exp))
    } else {
        err_str(&expr.span, "expression must produce a value")
    }
}

pub(crate) fn stms_to_one_stm(span: &Span, stms: Vec<Stm>) -> Stm {
    if stms.len() == 1 {
        stms[0].clone()
    } else {
        Spanned::new(span.clone(), StmX::Block(Arc::new(stms)))
    }
}

fn check_no_exp(exp: &Option<Exp>) -> Result<(), VirErr> {
    match exp {
        None => Ok(()),
        Some(exp) => match &exp.x {
            ExpX::Var((x, _)) if crate::def::is_temp_var(x) => Ok(()),
            // REVIEW: we could lift this restriction by putting exp into a dummy VIR node:
            // (we can't just drop it; the erasure depends on information from VIR)
            _ => err_str(&exp.span, "expressions with no effect are not supported"),
        },
    }
}

pub(crate) fn expr_to_one_stm(ctx: &Ctx, state: &mut State, expr: &Expr) -> Result<Stm, VirErr> {
    let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
    check_no_exp(&exp)?;
    Ok(stms_to_one_stm(&expr.span, stms))
}

pub(crate) fn expr_to_one_stm_dest(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
    dest: &Option<UniqueIdent>,
) -> Result<Stm, VirErr> {
    let (mut stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
    match (dest, exp) {
        (None, _) => {}
        (Some(_), None) => return err_str(&expr.span, "expression must produce a value"),
        (Some(dest), Some(exp)) => {
            stms.push(init_var(&expr.span, &dest, &exp));
        }
    }
    Ok(stms_to_one_stm(&expr.span, stms))
}

fn is_small_exp_or_loc(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(..) => true,
        ExpX::Old(..) => true,
        ExpX::Loc(..) => true,
        ExpX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_exp_or_loc(e),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_exp_or_loc(e),
        _ => false,
    }
}

fn stm_call(
    state: &mut State,
    span: &Span,
    name: Fun,
    typs: Typs,
    args: Args,
    dest: Option<Dest>,
) -> Stm {
    let mut small_args: Vec<Exp> = Vec::new();
    let mut stms: Vec<Stm> = Vec::new();
    for arg in args.iter() {
        if is_small_exp_or_loc(&arg.0) {
            small_args.push(arg.0.clone());
        } else {
            // To avoid copying arg in preconditions and postconditions,
            // put arg into a temporary variable
            let (temp, temp_var) = state.next_temp(&arg.0.span, &arg.1);
            small_args.push(temp_var);
            let temp_id = state.declare_new_var(&temp, &arg.1, false, false);
            stms.push(init_var(&arg.0.span, &temp_id, &arg.0));
        }
    }
    let call = StmX::Call(name, typs, Arc::new(small_args), dest);
    stms.push(Spanned::new(span.clone(), call));
    stms_to_one_stm(span, stms)
}

fn if_to_stm(
    state: &mut State,
    expr: &Expr,
    stms0: &mut Vec<Stm>,
    e0: Exp,
    mut stms1: Vec<Stm>,
    e1: &Exp,
    mut stms2: Vec<Stm>,
    e2: &Exp,
) -> Exp {
    // If statement, put results from e1/e2 in a temp variable, return temp variable
    let (temp, temp_var) = state.next_temp(&expr.span, &expr.typ);
    let temp_id = state.declare_new_var(&temp, &expr.typ, false, false);
    // if e0 { stms1; temp = e1; } else { stms2; temp = e2; }
    stms1.push(init_var(&expr.span, &temp_id, &e1));
    stms2.push(init_var(&expr.span, &temp_id, &e2));
    let stm1 = stms_to_one_stm(&expr.span, stms1);
    let stm2 = stms_to_one_stm(&expr.span, stms2);
    let if_stmt = StmX::If(e0, stm1, Some(stm2));
    stms0.push(Spanned::new(expr.span.clone(), if_stmt));
    // temp
    temp_var
}

pub(crate) fn expr_to_stm_opt(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Option<Exp>), VirErr> {
    let mk_exp = |expx: ExpX| SpannedTyped::new(&expr.span, &expr.typ, expx);
    match &expr.x {
        ExprX::Const(c) => Ok((vec![], Some(mk_exp(ExpX::Const(c.clone()))))),
        ExprX::Var(x) => {
            let unique_id = state.get_var_unique_id(&x);
            Ok((vec![], Some(mk_exp(ExpX::Var(unique_id)))))
        }
        ExprX::VarLoc(x) => {
            let unique_id = state.get_var_unique_id(&x);
            Ok((vec![], Some(mk_exp(ExpX::VarLoc(unique_id)))))
        }
        ExprX::VarAt(x, VarAt::Pre) => {
            if let Some((scope, _)) = state.rename_map.scope_and_index_of_key(x) {
                if scope != 0 {
                    err_str(&expr.span, "the parameter is shadowed here")?;
                }
            }
            Ok((vec![], Some(mk_exp(ExpX::VarAt(state.get_var_unique_id(&x), VarAt::Pre)))))
        }
        ExprX::ConstVar(..) => panic!("ConstVar should already be removed"),
        ExprX::Loc(expr1) => {
            let (stms, e0) = expr_to_stm(ctx, state, expr1)?;
            Ok((stms, Some(mk_exp(ExpX::Loc(e0)))))
        }
        ExprX::Assign(expr1, expr2) => {
            let dest_x = match &expr1.x {
                ExprX::Var(x) => Ok(state.get_var_unique_id(&x)),
                _ => err_str(&expr1.span, "complex assignments not yet supported"),
            };
            match expr_must_be_call_stm(ctx, state, expr2)? {
                Some((mut stms2, func_path, typs, _, args)) => {
                    // make a Call
                    let dest = Dest { var: dest_x?.clone(), is_init: false };
                    stms2.push(stm_call(state, &expr.span, func_path, typs, args, Some(dest)));
                    Ok((stms2, None))
                }
                None => {
                    // make an Assign
                    let (mut stms2, e2) = expr_to_stm(ctx, state, expr2)?;
                    let assign = StmX::Assign { lhs: dest_x?, rhs: e2, is_init: false };
                    stms2.push(Spanned::new(expr.span.clone(), assign));
                    Ok((stms2, None))
                }
            }
        }
        ExprX::Call(CallTarget::FnSpec(e0), args) => {
            let e0 = expr_to_exp_state(ctx, state, e0)?;
            let args = Arc::new(vec_map_result(args, |e| expr_to_exp_state(ctx, state, e))?);
            let call = ExpX::CallLambda(expr.typ.clone(), e0, args);
            Ok((vec![], Some(mk_exp(call))))
        }
        ExprX::Call(CallTarget::Static(..), _) => {
            let (mut stms, x, typs, ret, args) = expr_get_call(ctx, state, expr)?.expect("Call");
            if function_can_be_exp(ctx, expr, &x)? {
                // ExpX::Call
                let args = Arc::new(vec_map(&args, |(a, _)| a.clone()));
                let call = ExpX::Call(x.clone(), typs.clone(), args);
                Ok((stms, Some(mk_exp(call))))
            } else if ret {
                let (temp, temp_var) = state.next_temp(&expr.span, &expr.typ);
                state.declare_new_var(&temp, &expr.typ, false, false);
                // tmp = StmX::Call;
                let dest = Dest { var: (temp.clone(), Some(0)), is_init: true };
                stms.push(stm_call(state, &expr.span, x.clone(), typs.clone(), args, Some(dest)));
                // tmp
                Ok((stms, Some(temp_var)))
            } else {
                // StmX::Call
                stms.push(stm_call(state, &expr.span, x.clone(), typs.clone(), args, None));
                Ok((stms, None))
            }
        }
        ExprX::Tuple(_) => {
            panic!("internal error: Tuple should have been simplified by ast_simplify")
        }
        ExprX::Ctor(p, i, binders, update) => {
            assert!(update.is_none()); // should be simplified by ast_simplify
            let mut stms: Vec<Stm> = Vec::new();
            let mut args: Vec<Binder<Exp>> = Vec::new();
            for binder in binders.iter() {
                let (mut stms1, e1) = expr_to_stm(ctx, state, &binder.a)?;
                stms.append(&mut stms1);
                let arg = BinderX { name: binder.name.clone(), a: e1 };
                args.push(Arc::new(arg));
            }
            let ctor = ExpX::Ctor(p.clone(), i.clone(), Arc::new(args));
            Ok((stms, Some(mk_exp(ctor))))
        }
        ExprX::Unary(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(mk_exp(ExpX::Unary(*op, exp)))))
        }
        ExprX::UnaryOpr(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(mk_exp(ExpX::UnaryOpr(op.clone(), exp)))))
        }
        ExprX::Binary(op, e1, e2) => {
            let short_circuit = match op {
                BinaryOp::And => Some((true, false)),
                BinaryOp::Implies => Some((true, true)),
                BinaryOp::Or => Some((false, true)),
                _ => None,
            };
            let (mut stms1, e1) = expr_to_stm(ctx, state, e1)?;
            let (mut stms2, e2) = expr_to_stm(ctx, state, e2)?;
            let bin = match (short_circuit, stms2.len()) {
                (Some((proceed_on, other)), n) if n > 0 => {
                    // and:
                    //   if e1 { stmts2; e2 } else { false }
                    // implies:
                    //   if e1 { stmts2; e2 } else { true }
                    // or:
                    //   if e1 { true } else { stmts2; e2 }
                    let bx = ExpX::Const(Constant::Bool(other));
                    let b = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), bx);
                    if proceed_on {
                        let temp_var =
                            if_to_stm(state, expr, &mut stms1, e1, stms2, &e2, vec![], &b);
                        temp_var
                    } else {
                        let temp_var =
                            if_to_stm(state, expr, &mut stms1, e1, vec![], &b, stms2, &e2);
                        temp_var
                    }
                }
                _ => {
                    stms1.append(&mut stms2);
                    mk_exp(ExpX::Binary(*op, e1, e2))
                }
            };
            Ok((stms1, Some(bin)))
        }
        ExprX::Quant(quant, binders, body) => {
            state.push_scope();
            state.declare_binders(binders);
            let exp = expr_to_exp_state(ctx, state, body)?;
            state.pop_scope();
            let mut vars: Vec<Ident> = Vec::new();
            for b in binders.iter() {
                match &*b.a {
                    TypX::TypeId => vars.push(crate::def::suffix_typ_param_id(&b.name)),
                    _ => vars.push(b.name.clone()),
                }
            }
            let trigs = crate::triggers::build_triggers(ctx, &expr.span, &vars, &exp)?;
            let bnd = Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs));
            Ok((vec![], Some(mk_exp(ExpX::Bind(bnd, exp)))))
        }
        ExprX::Closure(params, body) => {
            state.push_scope();
            state.declare_binders(params);
            let mut exp = expr_to_exp_state(ctx, state, body)?;
            state.pop_scope();

            // Parameters and return types must be boxed, so insert necessary box/unboxing
            match &*body.typ {
                TypX::TypParam(_) | TypX::Boxed(_) => {}
                _ => {
                    let boxed_typ = Arc::new(TypX::Boxed(body.typ.clone()));
                    let boxx = ExpX::UnaryOpr(UnaryOpr::Box(body.typ.clone()), exp);
                    exp = SpannedTyped::new(&body.span, &boxed_typ, boxx);
                }
            }
            let mut let_box_binds: Vec<Binder<Exp>> = Vec::new();
            let mut boxed_params: Vec<Binder<Typ>> = Vec::new();
            for p in params.iter() {
                match &*p.a {
                    TypX::TypParam(_) | TypX::Boxed(_) => {
                        boxed_params.push(p.clone());
                    }
                    _ => {
                        let boxed_typ = Arc::new(TypX::Boxed(p.a.clone()));
                        boxed_params.push(p.new_a(boxed_typ.clone()));
                        let varx = ExpX::Var((p.name.clone(), None));
                        let var = SpannedTyped::new(&expr.span, &boxed_typ, varx);
                        let unboxx = ExpX::UnaryOpr(UnaryOpr::Unbox(p.a.clone()), var);
                        let unbox = SpannedTyped::new(&expr.span, &p.a, unboxx);
                        let_box_binds.push(p.new_a(unbox));
                    }
                };
            }
            if let_box_binds.len() != 0 {
                let bnd = Spanned::new(body.span.clone(), BndX::Let(Arc::new(let_box_binds)));
                exp = SpannedTyped::new(&body.span, &exp.typ, ExpX::Bind(bnd, exp.clone()));
            }

            let bnd = Spanned::new(body.span.clone(), BndX::Lambda(Arc::new(boxed_params)));
            Ok((vec![], Some(mk_exp(ExpX::Bind(bnd, exp)))))
        }
        ExprX::Choose { params, cond, body } => {
            state.push_scope();
            state.declare_binders(&params);
            let cond_exp = expr_to_exp_state(ctx, state, cond)?;
            let body_exp = expr_to_exp_state(ctx, state, body)?;
            state.pop_scope();
            let vars = vec_map(params, |p| p.name.clone());
            let trigs = crate::triggers::build_triggers(ctx, &expr.span, &vars, &cond_exp)?;
            let bnd =
                Spanned::new(body.span.clone(), BndX::Choose(params.clone(), trigs, cond_exp));
            Ok((vec![], Some(mk_exp(ExpX::Bind(bnd, body_exp)))))
        }
        ExprX::Fuel(x, fuel) => {
            let stm = Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel));
            Ok((vec![stm], None))
        }
        ExprX::Header(_) => {
            return err_str(&expr.span, "header expression not allowed here");
        }
        ExprX::Admit => {
            let expx = ExpX::Const(Constant::Bool(false));
            let exp = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), expx);
            let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
            Ok((vec![stm], None))
        }
        ExprX::Forall { vars, require, ensure, proof } => {
            // deadend {
            //   assume(require)
            //   proof
            //   assert(ensure);
            // }
            // assume(forall vars. require ==> ensure)
            let mut stms: Vec<Stm> = Vec::new();

            // Translate proof into a dead-end ending with an assert
            state.push_scope();
            let mut body: Vec<Stm> = Vec::new();
            for var in vars.iter() {
                let x = state.declare_new_var(&var.name, &var.a, false, true);
                let xvarx = ExpX::Var(x);
                let xvar = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), xvarx);
                let has_typx = ExpX::UnaryOpr(UnaryOpr::HasType(var.a.clone()), xvar);
                let has_typ = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), has_typx);
                let assume = Spanned::new(require.span.clone(), StmX::Assume(has_typ));
                body.push(assume);
            }
            let (mut proof_stms, e) = expr_to_stm_opt(ctx, state, proof)?;
            if let Some(_) = e {
                return err_str(&expr.span, "forall/assert-by cannot end with an expression");
            }
            let require_exp = expr_to_exp_state(ctx, state, &require)?;
            let assume = Spanned::new(require.span.clone(), StmX::Assume(require_exp));
            body.push(assume);
            body.append(&mut proof_stms);
            let ensure_exp = expr_to_exp_state(ctx, state, &ensure)?;
            let assert = Spanned::new(ensure.span.clone(), StmX::Assert(None, ensure_exp));
            body.push(assert);
            let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(body)));
            let deadend = Spanned::new(expr.span.clone(), StmX::DeadEnd(block));
            stms.push(deadend);
            state.pop_scope();

            // Translate ensure into an assume
            let implyx = ExprX::Binary(BinaryOp::Implies, require.clone(), ensure.clone());
            let imply = SpannedTyped::new(&ensure.span, &Arc::new(TypX::Bool), implyx);
            let forallx = ExprX::Quant(Quant::Forall, vars.clone(), imply);
            let forall = SpannedTyped::new(&ensure.span, &Arc::new(TypX::Bool), forallx);
            let forall_exp = expr_to_exp_state(ctx, state, &forall)?;
            let assume = Spanned::new(ensure.span.clone(), StmX::Assume(forall_exp));
            stms.push(assume);
            Ok((stms, None))
        }
        ExprX::AssertBV(e) => {
            let expr = expr_to_exp_state(ctx, state, &e)?;
            let assert = Spanned::new(e.span.clone(), StmX::AssertBV(expr));
            Ok((vec![assert], None))
        }
        ExprX::If(e0, e1, None) => {
            let (mut stms0, e0) = expr_to_stm(ctx, state, e0)?;
            let stms1 = expr_to_one_stm(ctx, state, e1)?;
            stms0.push(Spanned::new(expr.span.clone(), StmX::If(e0, stms1, None)));
            Ok((stms0, None))
        }
        ExprX::If(expr0, expr1, Some(expr2)) => {
            let (mut stms0, e0) = expr_to_stm(ctx, state, expr0)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, expr1)?;
            let (stms2, e2) = expr_to_stm_opt(ctx, state, expr2)?;
            match (e1, e2) {
                (Some(e1), Some(e2)) if stms1.len() == 0 && stms2.len() == 0 => {
                    // If expression
                    Ok((stms0, Some(mk_exp(ExpX::If(e0, e1, e2)))))
                }
                (Some(e1), Some(e2)) => {
                    // If statement, put results from e1/e2 in a temp variable, return temp variable
                    let temp_var = if_to_stm(state, expr, &mut stms0, e0, stms1, &e1, stms2, &e2);
                    Ok((stms0, Some(temp_var)))
                }
                (None, None) => {
                    // If statement, let expression be None
                    let stm1 = stms_to_one_stm(&expr1.span, stms1);
                    let stm2 = stms_to_one_stm(&expr2.span, stms2);
                    stms0.push(Spanned::new(expr.span.clone(), StmX::If(e0, stm1, Some(stm2))));
                    Ok((stms0, None))
                }
                _ => err_str(
                    &expr.span,
                    "if any if/match arm returns a value, all arms must return a value",
                ),
            }
        }
        ExprX::Match(..) => {
            panic!("internal error: Match should have been simplified by ast_simplify")
        }
        ExprX::While { cond, body, invs } => {
            let (stms0, e0) = expr_to_stm(ctx, state, cond)?;
            let (stms1, e1) = expr_to_stm_opt(ctx, state, body)?;
            check_no_exp(&e1)?;
            let invs = Arc::new(vec_map_result(invs, |e| expr_to_exp_state(ctx, state, e))?);
            let while_stm = Spanned::new(
                expr.span.clone(),
                StmX::While {
                    cond_stms: Arc::new(stms0),
                    cond_exp: e0,
                    body: stms_to_one_stm(&body.span, stms1),
                    invs,
                    typ_inv_vars: Arc::new(vec![]),
                    modified_vars: Arc::new(vec![]),
                },
            );
            Ok((vec![while_stm], None))
        }
        ExprX::OpenInvariant(inv, binder, body) => {
            // Evaluate `inv`
            let (mut stms0, big_inv_exp) = expr_to_stm(ctx, state, inv)?;

            // Assign it to a constant temp variable to ensure it is constant
            // across the entire block.
            let (temp, temp_var) = state.next_temp(&big_inv_exp.span, &inv.typ);
            let temp_id = state.declare_new_var(&temp, &inv.typ, false, false);
            stms0.push(init_var(&big_inv_exp.span, &temp_id, &big_inv_exp));

            // Process the body

            state.push_scope();
            let ident = state.declare_new_var(
                &binder.name,
                &binder.a,
                /* mutable */ true,
                /* maybe_need_rename */ true,
            );
            let body_stm = expr_to_one_stm(ctx, state, body)?;
            state.pop_scope();

            stms0.push(Spanned::new(
                expr.span.clone(),
                StmX::OpenInvariant(temp_var, ident, binder.a.clone(), body_stm),
            ));

            return Ok((stms0, None));
        }
        ExprX::Return(e1) => {
            if let Some((ret_dest, enss)) = state.ret_post.clone() {
                let mut stms: Vec<Stm> = Vec::new();
                match (ret_dest, e1) {
                    (None, None) => {}
                    (None, Some(e)) => return err_str(&e.span, "return value not allowed here"),
                    (_, None) => panic!("internal error: return value expected"),
                    (Some(dest), Some(e1)) => {
                        let (mut ret_stms, exp) = expr_to_stm(ctx, state, e1)?;
                        stms.append(&mut ret_stms);
                        stms.push(init_var(&expr.span, &dest, &exp));
                    }
                }
                for ens in enss.iter() {
                    let error = error_with_label(
                        "postcondition not satisfied".to_string(),
                        &expr.span,
                        "at this exit".to_string(),
                    )
                    .secondary_label(&ens.span, "failed this postcondition".to_string());
                    stms.push(Spanned::new(
                        expr.span.clone(),
                        StmX::Assert(Some(error), ens.clone()),
                    ));
                }
                let expx = ExpX::Const(Constant::Bool(false));
                let exp = SpannedTyped::new(&expr.span, &Arc::new(TypX::Bool), expx);
                stms.push(Spanned::new(expr.span.clone(), StmX::Assume(exp)));
                Ok((stms, None))
            } else {
                err_str(&expr.span, "return expression not allowed here")
            }
        }
        ExprX::Block(stmts, body_opt) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut local_decls: Vec<LocalDecl> = Vec::new();
            let mut binds: Vec<Bnd> = Vec::new();
            let mut is_pure_exp = true;
            for stmt in stmts.iter() {
                let (mut stms0, e0, decl_bnd_opt) = stmt_to_stm(ctx, state, stmt)?;
                match decl_bnd_opt {
                    Some((decl, bnd)) => {
                        state.push_scope();
                        local_decls.push(decl.clone());
                        state.insert_unique_var(&decl.ident);
                        match bnd {
                            None => {
                                is_pure_exp = false;
                            }
                            Some(bnd) => {
                                binds.push(bnd);
                            }
                        }
                    }
                    _ => {
                        is_pure_exp = false;
                    }
                }
                check_no_exp(&e0)?;
                stms.append(&mut stms0);
            }
            let exp = if let Some(expr) = body_opt {
                let (mut stms1, exp) = expr_to_stm_opt(ctx, state, expr)?;
                if stms1.len() > 0 {
                    is_pure_exp = false;
                }
                stms.append(&mut stms1);
                exp
            } else {
                None
            };
            for _ in local_decls.iter() {
                state.pop_scope();
            }
            match exp {
                Some(mut exp) if is_pure_exp => {
                    // Pure expression: fold decls into Let bindings and return a single expression
                    for bnd in binds.iter().rev() {
                        exp = SpannedTyped::new(
                            &expr.span,
                            &exp.typ,
                            ExpX::Bind(bnd.clone(), exp.clone()),
                        );
                    }
                    // We don't generate a LocalDecl, so we don't want to rename the variables
                    for decl in local_decls {
                        state.dont_rename.insert(decl.ident.clone());
                    }
                    return Ok((vec![], Some(exp)));
                }
                _ => {
                    // Not pure: return statements
                    for decl in local_decls {
                        state.local_decls.push(decl);
                    }
                    let block = Spanned::new(expr.span.clone(), StmX::Block(Arc::new(stms)));
                    Ok((vec![block], exp))
                }
            }
        }
    }
}

pub(crate) fn stmt_to_stm(
    ctx: &Ctx,
    state: &mut State,
    stmt: &Stmt,
) -> Result<(Vec<Stm>, Option<Exp>, Option<(LocalDecl, Option<Bnd>)>), VirErr> {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let (stms, exp) = expr_to_stm_opt(ctx, state, expr)?;
            Ok((stms, exp, None))
        }
        StmtX::Decl { pattern, mode: _, init } => {
            let (name, mutable) = match &pattern.x {
                PatternX::Var { name, mutable } => (name, mutable),
                _ => panic!("internal error: Decl should have been simplified by ast_simplify"),
            };

            let ident = state.alloc_unique_var(&name);
            let typ = pattern.typ.clone();
            let decl = Arc::new(LocalDeclX { ident, typ, mutable: *mutable });

            if let Some(init) = init {
                match expr_must_be_call_stm(ctx, state, init)? {
                    Some((mut stms, func_name, typs, _, args)) => {
                        // Special case: convert to a Call
                        let dest = Dest { var: decl.ident.clone(), is_init: true };
                        stms.push(stm_call(state, &init.span, func_name, typs, args, Some(dest)));
                        return Ok((stms, None, Some((decl, None))));
                    }
                    None => {}
                }
            }

            let (mut stms, exp) = match init {
                None => (vec![], None),
                Some(init) => expr_to_stm_opt(ctx, state, init)?,
            };

            // For a pure expression, return a binder
            let bnd = match &exp {
                Some(exp) if stms.len() == 0 => {
                    let binder = BinderX { name: name.clone(), a: exp.clone() };
                    let bnd = BndX::Let(Arc::new(vec![Arc::new(binder)]));
                    Some(Spanned::new(stmt.span.clone(), bnd))
                }
                _ => None,
            };

            match (*mutable, &exp) {
                (false, None) => {
                    // We don't yet support Assign to non-mutable
                    return err_str(&stmt.span, "non-mut variable must have an initializer");
                }
                (true, None) => {}
                (_, Some(exp)) => {
                    stms.push(init_var(&stmt.span, &decl.ident, exp));
                }
            }

            Ok((stms, None, Some((decl, bnd))))
        }
    }
}
