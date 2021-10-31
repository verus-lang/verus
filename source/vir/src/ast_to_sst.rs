use crate::ast::{
    BinaryOp, Constant, Expr, ExprX, Function, Ident, Mode, Params, Path, Stmt, StmtX, Typ, Typs,
    UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Dest, Exp, ExpX, LocalDecl, LocalDeclX, Stm, StmX, UniqueIdent};
use crate::sst_visitor::{map_exp_visitor, map_stm_exp_visitor};
use crate::util::{vec_map, vec_map_result};
use air::ast::{Binder, BinderX, Binders, Span};
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
        }
    }

    fn next_temp(&mut self, span: &Span) -> (Ident, Exp) {
        self.next_var += 1;
        let x = crate::def::prefix_temp_var(self.next_var);
        (x.clone(), Spanned::new(span.clone(), ExpX::Var((x.clone(), Some(0)))))
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
    ) -> UniqueIdent {
        let unique_ident = (ident.clone(), Some(0));
        let decl = LocalDeclX { ident: unique_ident.clone(), typ: typ.clone(), mutable };
        self.new_statement_var(&ident);
        self.local_decls.push(Arc::new(decl));
        unique_ident
    }

    // Erase unused unique ids from Vars
    pub(crate) fn finalize_exp(&self, exp: &Exp) -> Exp {
        map_exp_visitor(exp, &mut |exp| match &exp.x {
            ExpX::Var(x) if self.dont_rename.contains(&x) => {
                Spanned::new(exp.span.clone(), ExpX::Var((x.0.clone(), None)))
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

fn get_function(ctx: &Ctx, expr: &Expr, name: &Path) -> Result<Function, VirErr> {
    match ctx.func_map.get(name) {
        None => err_string(&expr.span, format!("could not find function {:?}", &name)),
        Some(func) => Ok(func.clone()),
    }
}

fn function_can_be_exp(ctx: &Ctx, expr: &Expr, path: &Path) -> Result<bool, VirErr> {
    match get_function(ctx, expr, path)?.x.mode {
        Mode::Spec => Ok(true),
        Mode::Proof | Mode::Exec => Ok(false),
    }
}

fn expr_get_call(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, typs, args) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut exps: Vec<Arg> = Vec::new();
            for arg in args.iter() {
                let (mut stms0, e0) = expr_to_stm(ctx, state, arg)?;
                stms.append(&mut stms0);
                exps.push((e0, arg.typ.clone()));
            }
            let has_ret = !get_function(ctx, expr, x)?.x.ret.is_none();
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
) -> Result<Option<(Vec<Stm>, Path, Typs, bool, Args)>, VirErr> {
    match &expr.x {
        ExprX::Call(x, _, _) if !function_can_be_exp(ctx, expr, x)? => {
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
    params: &Params,
    expr: &Expr,
) -> Result<(Vec<LocalDecl>, Exp), VirErr> {
    let mut state = State::new();
    for param in params.iter() {
        state.declare_new_var(&param.x.name, &param.x.typ, false);
    }
    let exp = expr_to_exp_state(ctx, &mut state, expr)?;
    let exp = state.finalize_exp(&exp);
    state.finalize();
    Ok((state.local_decls, exp))
}

pub(crate) fn expr_to_exp(ctx: &Ctx, params: &Params, expr: &Expr) -> Result<Exp, VirErr> {
    Ok(expr_to_decls_exp(ctx, params, expr)?.1)
}

pub(crate) fn expr_to_stm(
    ctx: &Ctx,
    state: &mut State,
    expr: &Expr,
) -> Result<(Vec<Stm>, Exp), VirErr> {
    let (stms, exp_opt) = expr_to_stm_opt(ctx, state, expr)?;
    Ok((stms, exp_opt.expect("expr_to_stm")))
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
        (Some(_), None) => {
            panic!("internal error: missing return value")
        }
        (Some(dest), Some(exp)) => {
            stms.push(init_var(&expr.span, &dest, &exp));
        }
    }
    Ok(stms_to_one_stm(&expr.span, stms))
}

fn is_small_exp(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(..) => true,
        ExpX::Old(..) => true,
        ExpX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_exp(e),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_exp(e),
        _ => false,
    }
}

fn stm_call(
    state: &mut State,
    span: &Span,
    path: Path,
    typs: Typs,
    args: Args,
    dest: Option<Dest>,
) -> Stm {
    let mut small_args: Vec<Exp> = Vec::new();
    let mut stms: Vec<Stm> = Vec::new();
    for arg in args.iter() {
        if is_small_exp(&arg.0) {
            small_args.push(arg.0.clone());
        } else {
            // To avoid copying arg in preconditions and postconditions,
            // put arg into a temporary variable
            let (temp, temp_var) = state.next_temp(&arg.0.span);
            small_args.push(temp_var);
            let temp_id = state.declare_new_var(&temp, &arg.1, false);
            stms.push(init_var(&arg.0.span, &temp_id, &arg.0));
        }
    }
    let call = StmX::Call(path, typs, Arc::new(small_args), dest);
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
    let (temp, temp_var) = state.next_temp(&expr.span);
    let temp_id = state.declare_new_var(&temp, &expr.typ, false);
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
    match &expr.x {
        ExprX::Const(c) => {
            Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Const(c.clone())))))
        }
        ExprX::Var(x) => {
            let unique_id = state.get_var_unique_id(&x);
            Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Var(unique_id)))))
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
        ExprX::Call(_, _, _) => {
            let (mut stms, x, typs, ret, args) = expr_get_call(ctx, state, expr)?.expect("Call");
            if function_can_be_exp(ctx, expr, &x)? {
                // ExpX::Call
                let args = Arc::new(vec_map(&args, |(a, _)| a.clone()));
                let call = ExpX::Call(x.clone(), typs.clone(), args);
                Ok((stms, Some(Spanned::new(expr.span.clone(), call))))
            } else if ret {
                let (temp, temp_var) = state.next_temp(&expr.span);
                state.declare_new_var(&temp, &expr.typ, false);
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
        ExprX::Ctor(p, i, binders) => {
            let mut stms: Vec<Stm> = Vec::new();
            let mut args: Vec<Binder<Exp>> = Vec::new();
            for binder in binders.iter() {
                let (mut stms1, e1) = expr_to_stm(ctx, state, &binder.a)?;
                stms.append(&mut stms1);
                let arg = BinderX { name: binder.name.clone(), a: e1 };
                args.push(Arc::new(arg));
            }
            let ctor = ExpX::Ctor(p.clone(), i.clone(), Arc::new(args));
            Ok((stms, Some(Spanned::new(expr.span.clone(), ctor))))
        }
        ExprX::Unary(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::Unary(*op, exp)))))
        }
        ExprX::UnaryOpr(op, expr) => {
            let (stms, exp) = expr_to_stm(ctx, state, expr)?;
            Ok((stms, Some(Spanned::new(expr.span.clone(), ExpX::UnaryOpr(op.clone(), exp)))))
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
                    let b = Spanned::new(expr.span.clone(), bx);
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
                    Spanned::new(expr.span.clone(), ExpX::Binary(*op, e1, e2))
                }
            };
            Ok((stms1, Some(bin)))
        }
        ExprX::Quant(quant, binders, body) => {
            state.push_scope();
            state.declare_binders(binders);
            let exp = expr_to_exp_state(ctx, state, body)?;
            state.pop_scope();
            let vars: Vec<Ident> = binders.iter().map(|b| b.name.clone()).collect();
            let trigs = crate::triggers::build_triggers(ctx, &expr.span, &vars, &exp)?;
            let bnd = Spanned::new(body.span.clone(), BndX::Quant(*quant, binders.clone(), trigs));
            Ok((vec![], Some(Spanned::new(expr.span.clone(), ExpX::Bind(bnd, exp)))))
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
                    Ok((stms0, Some(Spanned::new(expr.span.clone(), ExpX::If(e0, e1, e2)))))
                }
                (Some(e1), Some(e2)) => {
                    // If statement, put results from e1/e2 in a temp variable, return temp variable
                    let temp_var = if_to_stm(state, expr, &mut stms0, e0, stms1, &e1, stms2, &e2);
                    Ok((stms0, Some(temp_var)))
                }
                _ => {
                    // If statement, let expression be None
                    let stm1 = stms_to_one_stm(&expr1.span, stms1);
                    let stm2 = stms_to_one_stm(&expr2.span, stms2);
                    stms0.push(Spanned::new(expr.span.clone(), StmX::If(e0, stm1, Some(stm2))));
                    Ok((stms0, None))
                }
            }
        }
        ExprX::Match(..) => {
            panic!("internal error: Match should have been simplified by ast_simplify")
        }
        ExprX::While { cond, body, invs } => {
            let (stms0, e0) = expr_to_stm(ctx, state, cond)?;
            if stms0.len() != 0 {
                // TODO:
                return err_str(&cond.span, "not yet implemented: complex while loop conditions");
            }
            let (stms1, e1) = expr_to_stm_opt(ctx, state, body)?;
            check_no_exp(&e1)?;
            let invs = Arc::new(vec_map_result(invs, |e| expr_to_exp_state(ctx, state, e))?);
            let while_stm = Spanned::new(
                expr.span.clone(),
                StmX::While {
                    cond: e0,
                    body: stms_to_one_stm(&body.span, stms1),
                    invs,
                    typ_inv_vars: Arc::new(vec![]),
                    modified_vars: Arc::new(vec![]),
                },
            );
            Ok((vec![while_stm], None))
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
                        exp = Spanned::new(expr.span.clone(), ExpX::Bind(bnd.clone(), exp));
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
        ExprX::Fuel(x, fuel) => {
            let stm = Spanned::new(expr.span.clone(), StmX::Fuel(x.clone(), *fuel));
            Ok((vec![stm], None))
        }
        ExprX::Admit => {
            let exp = Spanned::new(expr.span.clone(), ExpX::Const(Constant::Bool(false)));
            let stm = Spanned::new(expr.span.clone(), StmX::Assume(exp));
            Ok((vec![stm], None))
        }
        _ => {
            todo!("{}", expr.span.as_string)
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
        StmtX::Decl { param, mutable, init } => {
            let ident = state.alloc_unique_var(&param.x.name.clone());
            let typ = param.x.typ.clone();
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
                    let binder = BinderX { name: param.x.name.clone(), a: exp.clone() };
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
