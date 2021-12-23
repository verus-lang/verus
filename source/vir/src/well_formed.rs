use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, Fun, Function, Krate, Mode, Path, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::ast_visitor::map_expr_visitor;
use crate::datatype_to_air::is_datatype_transparent;
use std::collections::HashMap;

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    if function.x.attrs.export_as_global_forall {
        if function.x.mode != Mode::Proof {
            return err_str(
                &function.span,
                "export_as_global_forall function must be declared as proof",
            );
        }
        if function.x.has_return() {
            return err_str(
                &function.span,
                "export_as_global_forall function cannot have return type",
            );
        }
        for param in function.x.params.iter() {
            if param.x.mode != Mode::Spec {
                return err_str(
                    &function.span,
                    "export_as_global_forall function must have spec parameters",
                );
            }
        }
        if function.x.body.is_some() {
            return err_str(
                &function.span,
                "export_as_global_forall function must be declared as no_verify",
            );
        }
    }
    if function.x.attrs.bit_vector {
        // return error if function has a non-integer type, or function call (for our simple version)
    }
    if let Some(body) = &function.x.body {
        map_expr_visitor(body, &mut |expr: &Expr| {
            match &expr.x {
                ExprX::Call(CallTarget::Static(x, _), _) => {
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
                ExprX::Ctor(path, _variant, _fields, _update) => {
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
                // TODO: disallow private fields, unless function is marked #[verifier(pub_abstract)]
                ExprX::UnaryOpr(UnaryOpr::Field { datatype: path, .. }, _) => {
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
        .map(|function| (function.x.name.clone(), function.clone()))
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
    crate::recursive_types::check_recursive_types(krate)?;
    Ok(())
}
