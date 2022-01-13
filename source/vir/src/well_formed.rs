use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, Fun, FunX, Function, Krate, MaskSpec, Mode, Path, PathX,
    TypX, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string};
use crate::ast_visitor::map_expr_visitor;
use crate::datatype_to_air::is_datatype_transparent;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use std::collections::HashMap;
use std::sync::Arc;

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    match &function.x.mask_spec {
        MaskSpec::NoSpec => {}
        _ => {
            if function.x.mode == Mode::Spec {
                return err_str(&function.span, "invariants cannot be opened in spec functions");
            }
        }
    }
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
                "export_as_global_forall function must be declared as external_body",
            );
        }
    }
    if function.x.attrs.autoview {
        if function.x.mode == Mode::Spec {
            return err_str(&function.span, "autoview function cannot be declared spec");
        }
        let mut segments = (*function.x.name.path.segments).clone();
        *segments.last_mut().expect("autoview segments") = Arc::new("view".to_string());
        let segments = Arc::new(segments);
        let path = Arc::new(PathX { segments, ..(*function.x.name.path).clone() });
        let fun = Arc::new(FunX { path, ..(*function.x.name).clone() });
        if let Some(f) = ctxt.funs.get(&fun) {
            if f.x.params.len() != 1 {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must have 0 paramters",
                );
            }
            let typ_args = if let TypX::Datatype(_, args) = &*f.x.params[0].x.typ {
                args.clone()
            } else {
                panic!("autoview_typ must be Datatype")
            };
            assert!(typ_args.len() <= f.x.typ_bounds.len());
            if f.x.typ_bounds.len() != typ_args.len() {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must have 0 type paramters",
                );
            }
            if f.x.mode != Mode::Spec {
                return err_str(
                    &f.span,
                    "because of autoview, view() function must be declared spec",
                );
            }
        } else {
            return err_str(
                &function.span,
                "autoview function must have corresponding view() function",
            );
        }
    }
    for req in function.x.require.iter() {
        let mut scope_map = air::scope_map::ScopeMap::new();
        if let crate::ast_visitor::VisitorControlFlow::Stop((span, name)) =
            crate::ast_visitor::expr_visitor_dfs(req, &mut scope_map, &mut |_map, expr| {
                if let ExprX::Var(x) = &expr.x {
                    for param in function.x.params.iter().filter(|p| p.x.is_mut) {
                        if *x == param.x.name {
                            return crate::ast_visitor::VisitorControlFlow::Stop((
                                expr.span.clone(),
                                param.x.name.clone(),
                            ));
                        }
                    }
                }
                crate::ast_visitor::VisitorControlFlow::Continue
            })
        {
            return err_string(
                &span,
                format!(
                    "in requires, use `old({})` to refer to the pre-state of an &mut variable",
                    name
                ),
            );
        }
    }
    if let Some(body) = &function.x.body {
        map_expr_visitor(body, &mut |expr: &Expr| {
            match &expr.x {
                ExprX::Call(CallTarget::Static(x, _), args) => {
                    let f = &ctxt.funs[x];
                    for (_param, arg) in
                        f.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.is_mut)
                    {
                        match &arg.x {
                            ExprX::Var(_) => (),
                            _ => {
                                return err_str(
                                    &arg.span,
                                    "complex arguments to &mut parameters are currently unsupported",
                                );
                            }
                        }
                    }
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
                ExprX::OpenInvariant(_inv, _binder, body) => {
                    assert_no_early_exit_in_inv_block(&body.span, body)?;
                }
                _ => {}
            }
            Ok(expr.clone())
        })?;
    }
    Ok(())
}

fn check_datatype(dt: &Datatype) -> Result<(), VirErr> {
    let unforgeable = dt.x.unforgeable;
    let dt_mode = dt.x.mode;

    if unforgeable && dt_mode != Mode::Proof {
        return err_string(&dt.span, format!("An unforgeable datatype must be in #[proof] mode."));
    }

    // For an 'unforgeable' datatype, all fields must be #[spec]

    if unforgeable {
        for variant in dt.x.variants.iter() {
            for binder in variant.a.iter() {
                let (_typ, field_mode) = &binder.a;
                if *field_mode != Mode::Spec {
                    return err_string(
                        &dt.span,
                        format!("All fields of a unforgeable datatype must be marked #[spec]"),
                    );
                }
            }
        }
    }

    return Ok(());
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
    for dt in krate.datatypes.iter() {
        check_datatype(dt)?;
    }
    crate::recursive_types::check_recursive_types(krate)?;
    Ok(())
}
