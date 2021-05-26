use crate::ast::{Datatype, Expr, ExprX, Function, Ident, Krate, Mode, Stmt, StmtX, VirErr};
use crate::ast_util::err_string;
use crate::sst_to_air::path_to_air_ident;
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

struct Typing {
    pub(crate) funs: HashMap<Ident, Function>,
    pub(crate) datatypes: HashMap<Ident, Datatype>,
    pub(crate) vars: HashMap<Ident, Mode>,
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
        ExprX::Var(x) => Ok(mode_join(outer_mode, typing.vars[x])),
        ExprX::Call(x, _, es) => {
            let function = &typing.funs[x].clone();
            if !mode_le(outer_mode, function.x.mode) {
                return err_string(
                    &expr.span,
                    format!("cannot call function with mode {}", function.x.mode),
                );
            }
            for (param, arg) in function.x.params.iter().zip(es.iter()) {
                check_expr_has_mode(typing, outer_mode, arg, param.x.mode)?;
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
        ExprX::Field { lhs, datatype_name, field_name } => {
            let lhs_mode = check_expr(typing, outer_mode, lhs)?;
            let datatype = &typing.datatypes[datatype_name].clone();
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
        ExprX::Quant(_, _, e1) => {
            check_expr_has_mode(typing, Mode::Spec, e1, Mode::Spec)?;
            Ok(Mode::Spec)
        }
        ExprX::Assign(lhs, rhs) => match &lhs.x {
            ExprX::Var(x) => {
                let x_mode = typing.vars[x];
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
            let mut pushed_vars: Vec<(Ident, Option<Mode>)> = Vec::new();
            for stmt in ss.iter() {
                check_stmt(typing, &mut pushed_vars, outer_mode, stmt)?;
            }
            let mode = match e1 {
                None => outer_mode,
                Some(expr) => check_expr(typing, outer_mode, expr)?,
            };
            for (x, prev_mode) in pushed_vars {
                match prev_mode {
                    None => {
                        typing.vars.remove(&x);
                    }
                    Some(prev) => {
                        typing.vars.insert(x, prev);
                    }
                }
            }
            Ok(mode)
        }
    }
}

fn check_stmt(
    typing: &mut Typing,
    pushed_vars: &mut Vec<(Ident, Option<Mode>)>,
    outer_mode: Mode,
    stmt: &Stmt,
) -> Result<(), VirErr> {
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
            let prev = typing.vars.insert(param.x.name.clone(), param.x.mode);
            pushed_vars.push((param.x.name.clone(), prev));
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
    for param in function.x.params.iter() {
        if !mode_le(function.x.mode, param.x.mode) {
            return err_string(
                &function.span,
                format!("parameter {} cannot have mode {}", param.x.name, param.x.mode),
            );
        }
        typing.vars.insert(param.x.name.clone(), param.x.mode);
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
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(), VirErr> {
    let mut funs: HashMap<Ident, Function> = HashMap::new();
    let mut datatypes: HashMap<Ident, Datatype> = HashMap::new();
    for function in krate.functions.iter() {
        funs.insert(function.x.name.clone(), function.clone());
    }
    for datatype in krate.datatypes.iter() {
        datatypes.insert(path_to_air_ident(&datatype.x.path.clone()), datatype.clone());
    }
    let mut typing = Typing { funs, datatypes, vars: HashMap::new() };
    for function in krate.functions.iter() {
        check_function(&mut typing, function)?;
    }
    Ok(())
}
