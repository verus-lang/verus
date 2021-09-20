use crate::ast::{Datatype, Expr, ExprX, Function, Krate, Mode, Path, VirErr};
use crate::ast_util::err_string;
use crate::ast_visitor::map_expr_visitor;
use crate::datatype_to_air::is_datatype_transparent;
use std::collections::HashMap;

struct Ctxt {
    pub(crate) funs: HashMap<Path, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    if let Some(body) = &function.x.body {
        map_expr_visitor(body, &mut |expr: &Expr| {
            match &expr.x {
                ExprX::Call(x, _, _) => {
                    // Check that public, non-abstract spec function bodies don't refer to private items
                    if !function.x.is_abstract
                        && !function.x.visibility.is_private
                        && function.x.mode == Mode::Spec
                    {
                        let callee = &ctxt.funs[x];
                        if callee.x.visibility.is_private {
                            return err_string(
                                &expr.span,
                                format!(
                                    "public spec function cannot refer to private items, unless function is marked #[verifier(pub_abstract)]"
                                ),
                            );
                        }
                    }
                }
                ExprX::Ctor(path, _variant, _fields) => {
                    if let Some(dt) = ctxt.dts.get(path) {
                        if let Some(module) = &function.x.visibility.owning_module {
                            if !is_datatype_transparent(&module, dt) {
                                return err_string(
                                    &expr.span,
                                    format!("constructor of datatype with unencoded fields here"),
                                );
                            }
                        }
                    } else {
                        panic!("constructor of undefined datatype");
                    }
                }
                // TODO: disallow private fields, unless function is marked #[verified(pub_abstract)]
                ExprX::Field { datatype: path, .. } => {
                    if let Some(dt) = ctxt.dts.get(path) {
                        if let Some(module) = &function.x.visibility.owning_module {
                            if !is_datatype_transparent(&module, dt) {
                                return err_string(
                                    &expr.span,
                                    format!("field access of datatype with unencoded fields here"),
                                );
                            }
                        }
                    } else {
                        panic!("field access of undefined datatype");
                    }
                }
                _ => {}
            }
            Ok(expr.clone())
        })?;
    }
    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(), VirErr> {
    let funs = krate
        .functions
        .iter()
        .map(|function| (function.x.path.clone(), function.clone()))
        .collect();
    let dts = krate
        .datatypes
        .iter()
        .map(|datatype| (datatype.x.path.clone(), datatype.clone()))
        .collect();
    let ctxt = Ctxt { funs, dts };
    for function in krate.functions.iter() {
        check_function(&ctxt, function)?;
    }
    Ok(())
}
