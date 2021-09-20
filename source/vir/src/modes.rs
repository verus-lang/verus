use crate::ast::{Datatype, Expr, ExprX, Function, Ident, Krate, Mode, Path, Stmt, StmtX, VirErr};
use crate::ast_util::{err_str, err_string};
use air::ast::Span;
use air::scope_map::ScopeMap;
use std::collections::HashMap;

// Exec <= Proof <= Spec
pub fn mode_le(m1: Mode, m2: Mode) -> bool {
    match (m1, m2) {
        (_, Mode::Spec) => true,
        (Mode::Exec, _) => true,
        _ if m1 == m2 => true,
        _ => false,
    }
}

// least upper bound
pub fn mode_join(m1: Mode, m2: Mode) -> Mode {
    match (m1, m2) {
        (_, Mode::Spec) => Mode::Spec,
        (Mode::Spec, _) => Mode::Spec,
        (Mode::Exec, m) => m,
        (m, Mode::Exec) => m,
        (Mode::Proof, Mode::Proof) => Mode::Proof,
    }
}

#[derive(Clone)]
pub struct ErasureModes {
    // Modes of conditions in If
    pub condition_modes: Vec<(Span, Mode)>,
    // Modes of variables in Var, Assign, Decl
    pub var_modes: Vec<(Span, Mode)>,
}

struct Typing {
    pub(crate) funs: HashMap<Path, Function>,
    pub(crate) datatypes: HashMap<Path, Datatype>,
    pub(crate) vars: ScopeMap<Ident, Mode>,
    pub(crate) erasure_modes: ErasureModes,
}

impl Typing {
    fn get(&self, x: &Ident) -> Mode {
        *self.vars.get(x).expect("internal error: missing mode")
    }

    fn insert(&mut self, span: &Span, x: &Ident, mode: Mode) -> Result<(), VirErr> {
        match self.vars.insert(x.clone(), mode) {
            Ok(()) => Ok(()),
            Err(()) => err_str(span, "variable shadowing not yet supported"),
        }
    }
}

fn check_expr_has_mode(
    typing: &mut Typing,
    outer_mode: Mode,
    expr: &Expr,
    expected: Mode,
) -> Result<(), VirErr> {
    let mode = check_expr(typing, outer_mode, expr)?;
    if !mode_le(mode, expected) {
        err_string(&expr.span, format!("expression has mode {}, expected mode {}", mode, expected))
    } else {
        Ok(())
    }
}

fn check_expr(typing: &mut Typing, outer_mode: Mode, expr: &Expr) -> Result<Mode, VirErr> {
    match &expr.x {
        ExprX::Const(_) => Ok(outer_mode),
        ExprX::Var(x) => {
            let mode = mode_join(outer_mode, typing.get(x));
            typing.erasure_modes.var_modes.push((expr.span.clone(), mode));
            Ok(mode)
        }
        ExprX::Call(x, _, es) => {
            let function = &typing.funs[x].clone();
            if !mode_le(outer_mode, function.x.mode) {
                return err_string(
                    &expr.span,
                    format!("cannot call function with mode {}", function.x.mode),
                );
            }
            for (param, arg) in function.x.params.iter().zip(es.iter()) {
                check_expr_has_mode(
                    typing,
                    mode_join(outer_mode, param.x.mode),
                    arg,
                    param.x.mode,
                )?;
            }
            match function.x.ret {
                None => Ok(function.x.mode),
                Some((_, _, ret_mode)) => Ok(ret_mode),
            }
        }
        ExprX::Ctor(_path, _ident, binders) => {
            let binder_modes = binders
                .iter()
                .map(|b| check_expr(typing, outer_mode, &b.a))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(binder_modes.into_iter().fold(outer_mode, mode_join))
        }
        ExprX::Field { lhs, datatype: datatype_path, field_name } => {
            let lhs_mode = check_expr(typing, outer_mode, lhs)?;
            let datatype = &typing.datatypes[datatype_path].clone();
            let variants = &datatype.x.variants;
            assert_eq!(variants.len(), 1);
            let fields = &variants[0].a;
            match fields.iter().find(|field| field.name == *field_name) {
                Some(field) => Ok(mode_join(lhs_mode, field.a.1)),
                None => panic!("internal error: missing field {}", &field_name),
            }
        }
        ExprX::Unary(_, e1) => check_expr(typing, outer_mode, e1),
        ExprX::UnaryOpr(_, e1) => check_expr(typing, outer_mode, e1),
        ExprX::Binary(_, e1, e2) => {
            let mode1 = check_expr(typing, outer_mode, e1)?;
            let mode2 = check_expr(typing, outer_mode, e2)?;
            Ok(mode_join(mode1, mode2))
        }
        ExprX::Quant(_, binders, e1) => {
            typing.vars.push_scope(false);
            for binder in binders.iter() {
                typing.insert(&expr.span, &binder.name, Mode::Spec)?;
            }
            check_expr_has_mode(typing, Mode::Spec, e1, Mode::Spec)?;
            typing.vars.pop_scope();
            Ok(Mode::Spec)
        }
        ExprX::Assign(lhs, rhs) => match &lhs.x {
            ExprX::Var(x) => {
                let x_mode = typing.get(x);
                typing.erasure_modes.var_modes.push((lhs.span.clone(), x_mode));
                check_expr_has_mode(typing, outer_mode, rhs, x_mode)?;
                Ok(x_mode)
            }
            _ => panic!("expected var, found {:?}", &lhs),
        },
        ExprX::Fuel(_, _) => Ok(outer_mode),
        ExprX::Header(_) => panic!("internal error: Header shouldn't exist here"),
        ExprX::Admit => Ok(outer_mode),
        ExprX::If(e1, e2, e3) => {
            let mode1 = check_expr(typing, outer_mode, e1)?;
            typing.erasure_modes.condition_modes.push((expr.span.clone(), mode1));
            let mode_branch = match (outer_mode, mode1) {
                (Mode::Exec, Mode::Spec) => Mode::Proof,
                _ => outer_mode,
            };
            let mode2 = check_expr(typing, mode_branch, e2)?;
            match e3 {
                None => Ok(mode2),
                Some(e3) => {
                    let mode3 = check_expr(typing, mode_branch, e3)?;
                    Ok(mode_join(mode2, mode3))
                }
            }
        }
        ExprX::While { cond, body, invs } => {
            // We could also allow this for proof, if we check it for termination
            check_expr_has_mode(typing, outer_mode, cond, Mode::Exec)?;
            check_expr_has_mode(typing, outer_mode, body, Mode::Exec)?;
            for inv in invs.iter() {
                check_expr_has_mode(typing, Mode::Spec, inv, Mode::Spec)?;
            }
            Ok(Mode::Exec)
        }
        ExprX::Block(ss, e1) => {
            typing.vars.push_scope(false);
            for stmt in ss.iter() {
                check_stmt(typing, outer_mode, stmt)?;
            }
            let mode = match e1 {
                None => outer_mode,
                Some(expr) => check_expr(typing, outer_mode, expr)?,
            };
            typing.vars.pop_scope();
            Ok(mode)
        }
    }
}

fn check_stmt(typing: &mut Typing, outer_mode: Mode, stmt: &Stmt) -> Result<(), VirErr> {
    match &stmt.x {
        StmtX::Expr(e) => {
            let _ = check_expr(typing, outer_mode, e)?;
            Ok(())
        }
        StmtX::Decl { param, mutable: _, init } => {
            if !mode_le(outer_mode, param.x.mode) {
                return err_string(
                    &stmt.span,
                    format!("variable {} cannot have mode {}", param.x.name, param.x.mode),
                );
            }
            typing.erasure_modes.var_modes.push((param.span.clone(), param.x.mode));
            typing.insert(&stmt.span, &param.x.name, param.x.mode)?;
            match init.as_ref() {
                None => {}
                Some(expr) => {
                    check_expr_has_mode(typing, outer_mode, expr, param.x.mode)?;
                }
            }
            Ok(())
        }
    }
}

fn check_function(typing: &mut Typing, function: &Function) -> Result<(), VirErr> {
    typing.vars.push_scope(false);
    for param in function.x.params.iter() {
        if !mode_le(function.x.mode, param.x.mode) {
            return err_string(
                &function.span,
                format!("parameter {} cannot have mode {}", param.x.name, param.x.mode),
            );
        }
        typing.insert(&function.span, &param.x.name, param.x.mode)?;
    }
    if let Some((_, _, ret_mode)) = function.x.ret {
        if !mode_le(function.x.mode, ret_mode) {
            return err_string(
                &function.span,
                format!("return type cannot have mode {}", ret_mode),
            );
        }
    }
    if let Some(body) = &function.x.body {
        check_expr(typing, function.x.mode, body)?;
    }
    typing.vars.pop_scope();
    assert_eq!(typing.vars.num_scopes(), 0);
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<ErasureModes, VirErr> {
    let mut funs: HashMap<Path, Function> = HashMap::new();
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    for function in krate.functions.iter() {
        funs.insert(function.x.path.clone(), function.clone());
    }
    for datatype in krate.datatypes.iter() {
        datatypes.insert(datatype.x.path.clone(), datatype.clone());
    }
    let erasure_modes = ErasureModes { condition_modes: vec![], var_modes: vec![] };
    let mut typing = Typing { funs, datatypes, vars: ScopeMap::new(), erasure_modes };
    for function in krate.functions.iter() {
        check_function(&mut typing, function)?;
    }
    Ok(typing.erasure_modes)
}
