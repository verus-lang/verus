use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, FunX, Function, FunctionKind, Krate,
    MaskSpec, Mode, Path, PathX, TypX, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string, error, referenced_vars_expr};
use crate::datatype_to_air::is_datatype_transparent;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

fn check_one_expr(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<&str>,
) -> Result<(), VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Static(x, _), args) => {
            let f = &ctxt.funs[x];
            if f.x.attrs.is_decrease_by {
                // a decreases_by function isn't a real function;
                // it's just a container for proof code that goes in the corresponding spec function
                return err_str(
                    &expr.span,
                    "cannot call a decreases_by/recommends_by function directly",
                );
            }
            for (_param, arg) in f.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.is_mut) {
                fn is_ok(e: &Expr) -> bool {
                    match &e.x {
                        ExprX::VarLoc(_) => true,
                        ExprX::UnaryOpr(UnaryOpr::Field { .. }, base) => is_ok(base),
                        _ => false,
                    }
                }
                let is_ok = match &arg.x {
                    ExprX::Loc(l) => is_ok(l),
                    _ => false,
                };
                if !is_ok {
                    return err_str(
                        &arg.span,
                        "complex arguments to &mut parameters are currently unsupported",
                    );
                }
            }
            if let Some(msg) = disallow_private_access {
                let callee = &ctxt.funs[x];
                if callee.x.visibility.is_private {
                    return err_str(&expr.span, msg);
                }
            }
        }
        ExprX::Ctor(path, _variant, _fields, _update) => {
            if let Some(dt) = ctxt.dts.get(path) {
                if let Some(module) = &function.x.visibility.owning_module {
                    if !is_datatype_transparent(&module, dt) {
                        return err_str(
                            &expr.span,
                            "constructor of datatype with unencoded fields here",
                        );
                    }
                }
            } else {
                panic!("constructor of undefined datatype");
            }
        }
        ExprX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype: path, variant, field }), _) => {
            if let Some(dt) = ctxt.dts.get(path) {
                if let Some(module) = &function.x.visibility.owning_module {
                    if !is_datatype_transparent(&module, dt) {
                        return err_str(
                            &expr.span,
                            "field access of datatype with unencoded fields here",
                        );
                    }
                }
                if let Some(msg) = disallow_private_access {
                    let variant = dt.x.get_variant(variant);
                    let (_, _, vis) = &crate::ast_util::get_field(&variant.a, &field).a;
                    if vis.is_private {
                        return err_str(&expr.span, msg);
                    }
                }
            } else {
                panic!("field access of undefined datatype");
            }
        }
        ExprX::OpenInvariant(_inv, _binder, body, _atomicity) => {
            assert_no_early_exit_in_inv_block(&body.span, body)?;
        }
        ExprX::AssertNonLinear { requires, ensure, proof } => {
            if function.x.attrs.nonlinear {
                return err_str(
                    &expr.span,
                    "assert_by_nonlinear not allowed in #[verifier(nonlinear)] functions",
                );
            }

            let mut referenced = HashSet::new();
            for r in requires.iter() {
                referenced.extend(referenced_vars_expr(r).into_iter());
            }
            referenced.extend(referenced_vars_expr(ensure).into_iter());

            crate::ast_visitor::expr_visitor_check(proof, &mut |e| match &e.x {
                ExprX::Var(x) | ExprX::VarLoc(x) if !referenced.contains(x) => Err(error(
                    format!("variable {} not mentioned in requires/ensures", x).as_str(),
                    &e.span,
                )),
                _ => Ok(()),
            })?;
        }
        _ => {}
    }
    Ok(())
}

fn check_expr(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<&str>,
) -> Result<(), VirErr> {
    crate::ast_visitor::expr_visitor_check(expr, &mut |expr| {
        check_one_expr(ctxt, function, expr, disallow_private_access)
    })
}

fn check_function(ctxt: &Ctxt, function: &Function) -> Result<(), VirErr> {
    if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
        if function.x.body.is_some() && function.x.mode != Mode::Exec {
            // REVIEW: If we allow default method implementations, we'll need to make sure
            // it doesn't introduce nontermination into proof/spec.
            return err_str(
                &function.span,
                "trait proof/spec method declaration cannot provide a default implementation",
            );
        }
        if !matches!(function.x.mask_spec, MaskSpec::NoSpec) {
            return err_str(
                &function.span,
                "not yet supported: trait method declarations that open invariants",
            );
        }
    }

    if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
        if function.x.require.len() + function.x.ensure.len() != 0 {
            return err_str(
                &function.span,
                "trait method implementation cannot declare requires/ensures; these can only be inherited from the trait declaration",
            );
        }
        if !matches!(function.x.mask_spec, MaskSpec::NoSpec) {
            return err_str(
                &function.span,
                "trait method implementation cannot open invariants; this can only be inherited from the trait declaration",
            );
        }
    }

    if function.x.attrs.is_decrease_by {
        match function.x.kind {
            FunctionKind::Static => {}
            FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. } => {
                return err_str(
                    &function.span,
                    "decreases_by/recommends_by function cannot be a trait method",
                );
            }
        }
        if function.x.mode != Mode::Proof {
            return err_str(
                &function.span,
                "decreases_by/recommends_by function must have mode proof",
            );
        }
        if function.x.decrease.len() != 0 {
            return err_str(
                &function.span,
                "decreases_by/recommends_by function cannot have its own decreases clause",
            );
        }
        if function.x.require.len() != 0 {
            return err_str(
                &function.span,
                "decreases_by/recommends_by function cannot have requires clauses (use decreases_when in the spec function instead)",
            );
        }
        if function.x.ensure.len() != 0 {
            return err_str(
                &function.span,
                "decreases_by/recommends_by function cannot have ensures clauses",
            );
        }
        if function.x.has_return() {
            return err_str(
                &function.span,
                "decreases_by/recommends_by function cannot have a return value",
            );
        }
    }

    if function.x.decrease_by.is_some() {
        if function.x.mode != Mode::Spec {
            return err_str(
                &function.span,
                "only spec functions can use decreases_by/recommends_by",
            );
        }
    }

    for p in function.x.params.iter() {
        if p.x.name == function.x.ret.x.name {
            return err_str(&p.span, "parameter name cannot be same as return value name");
        }
    }

    if function.x.attrs.atomic {
        if function.x.mode != Mode::Exec {
            return err_str(&function.span, "'atomic' only makes sense on an 'exec' function");
        }
    }
    match &function.x.mask_spec {
        MaskSpec::NoSpec => {}
        _ => {
            if function.x.mode == Mode::Spec {
                return err_str(&function.span, "invariants cannot be opened in spec functions");
            }
        }
    }
    if function.x.attrs.broadcast_forall {
        if function.x.mode != Mode::Proof {
            return err_str(&function.span, "broadcast_forall function must be declared as proof");
        }
        if function.x.has_return() {
            return err_str(&function.span, "broadcast_forall function cannot have return type");
        }
        for param in function.x.params.iter() {
            if param.x.mode != Mode::Spec {
                return err_str(
                    &function.span,
                    "broadcast_forall function must have spec parameters",
                );
            }
        }
        if function.x.body.is_some() {
            return err_str(
                &function.span,
                "broadcast_forall function must be declared as external_body",
            );
        }
    }

    if function.x.attrs.bit_vector {
        if function.x.mode != Mode::Proof {
            return err_str(&function.span, "bit-vector function mode must be declared as proof");
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return err_str(
                            &function.span,
                            "bit-vector function mode cannot have a body",
                        );
                    }
                }
                Ok(())
            })?;
        }
        for p in function.x.params.iter() {
            match *p.x.typ {
                TypX::Bool | TypX::Int(_) | TypX::Boxed(_) => {}
                _ => {
                    return err_str(
                        &p.span,
                        "bit-vector function mode cannot have a datatype other than Integer/Boolean",
                    );
                }
            }
        }
    }

    if function.x.attrs.nonlinear {
        if function.x.mode == Mode::Spec {
            return err_str(
                &function.span,
                "#[verifier(nonlinear) is only allowed on proof and exec functions",
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

    if function.x.publish.is_some() && function.x.mode != Mode::Spec {
        return err_str(
            &function.span,
            "function is marked #[verifier(publish)] but not marked #[spec]",
        );
    }

    if function.x.is_main() && function.x.mode != Mode::Exec {
        return err_str(&function.span, "`main` function should be #[exec]");
    }

    if function.x.publish.is_some() && function.x.visibility.is_private {
        return err_str(
            &function.span,
            "function is marked #[verifier(publish)] but not marked `pub`; for the body of a function to be visible, the function symbol must also be visible",
        );
    }

    for req in function.x.require.iter() {
        let disallow_private_access = if function.x.visibility.is_private {
            None
        } else {
            Some("public function requires cannot refer to private items")
        };
        check_expr(ctxt, function, req, disallow_private_access)?;
        crate::ast_visitor::expr_visitor_check(req, &mut |expr| {
            if let ExprX::Var(x) = &expr.x {
                for param in function.x.params.iter().filter(|p| p.x.is_mut) {
                    if *x == param.x.name {
                        return err_string(
                            &expr.span,
                            format!(
                                "in requires, use `old({})` to refer to the pre-state of an &mut variable",
                                param.x.name
                            ),
                        );
                    }
                }
            }
            Ok(())
        })?;
    }
    for ens in function.x.ensure.iter() {
        let disallow_private_access = if function.x.visibility.is_private {
            None
        } else {
            Some("public function ensures cannot refer to private items")
        };
        check_expr(ctxt, function, ens, disallow_private_access)?;
    }
    for expr in function.x.decrease.iter() {
        let disallow_private_access = if function.x.visibility.is_private {
            None
        } else {
            Some("public function decreases cannot refer to private items")
        };
        check_expr(ctxt, function, expr, disallow_private_access)?;
    }
    if let Some(expr) = &function.x.decrease_when {
        let disallow_private_access = if function.x.visibility.is_private {
            None
        } else {
            Some("public function decreases_when cannot refer to private items")
        };
        if function.x.mode != Mode::Spec {
            return err_str(
                &function.span,
                "only spec functions can use decreases_when (use requires for proof/exec functions)",
            );
        }
        if function.x.decrease.len() == 0 {
            return err_str(
                &function.span,
                "decreases_when can only be used when there is a decreases clause (use recommends(...) for nonrecursive functions)",
            );
        }
        check_expr(ctxt, function, expr, disallow_private_access)?;
    }

    if let Some(body) = &function.x.body {
        // Check that public, non-abstract spec function bodies don't refer to private items:
        let disallow_private_access = function.x.publish.is_some()
            && !function.x.visibility.is_private
            && function.x.mode == Mode::Spec;
        let disallow_private_access = if disallow_private_access {
            Some(
                "public spec function cannot refer to private items, if it is marked #[verifier(publish)]",
            )
        } else {
            None
        };

        check_expr(ctxt, function, body, disallow_private_access)?;
    }
    Ok(())
}

fn check_datatype(dt: &Datatype) -> Result<(), VirErr> {
    let unforgeable = dt.x.unforgeable;
    let dt_mode = dt.x.mode;

    if unforgeable && dt_mode != Mode::Proof {
        return err_string(&dt.span, format!("an unforgeable datatype must be in #[proof] mode"));
    }

    // For an 'unforgeable' datatype, all fields must be #[spec]

    if unforgeable {
        for variant in dt.x.variants.iter() {
            for binder in variant.a.iter() {
                let (_typ, field_mode, _vis) = &binder.a;
                if *field_mode != Mode::Spec {
                    return err_string(
                        &dt.span,
                        format!("all fields of a unforgeable datatype must be marked #[spec]"),
                    );
                }
            }
        }
    }

    Ok(())
}

pub fn check_crate(krate: &Krate) -> Result<(), VirErr> {
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    for function in krate.functions.iter() {
        if funs.contains_key(&function.x.name) {
            return Err(air::errors::error(
                "not supported: multiple definitions of same function",
                &function.span,
            )
            .secondary_span(&funs[&function.x.name].span));
        }
        funs.insert(function.x.name.clone(), function.clone());
    }
    let dts = krate
        .datatypes
        .iter()
        .map(|datatype| (datatype.x.path.clone(), datatype.clone()))
        .collect();

    // Check connections between decreases_by specs and proofs
    let mut decreases_by_proof_to_spec: HashMap<Fun, Fun> = HashMap::new();
    for function in krate.functions.iter() {
        if let Some(proof_fun) = &function.x.decrease_by {
            let proof_function = if let Some(proof_function) = funs.get(proof_fun) {
                proof_function
            } else {
                return err_str(
                    &function.span,
                    "cannot find function referred to in decreases_by/recommends_by",
                );
            };
            if !proof_function.x.attrs.is_decrease_by {
                return Err(air::errors::error(
                    "proof function must be marked #[verifier(decreases_by)] or #[verifier(recommends_by)] to be used as decreases_by/recommends_by",
                    &proof_function.span,
                )
                .secondary_span(&function.span));
            }
            if let Some(prev) = decreases_by_proof_to_spec.get(proof_fun) {
                return Err(air::errors::error(
                    "same proof function used for two different decreases_by/recommends_by",
                    &proof_function.span,
                )
                .secondary_span(&funs[prev].span)
                .secondary_span(&function.span));
            }
            decreases_by_proof_to_spec.insert(proof_fun.clone(), function.x.name.clone());
            if proof_function.x.typ_bounds.len() != function.x.typ_bounds.len() {
                return Err(air::errors::error(
                    "decreases_by/recommends_by function should have the same type bounds",
                    &proof_function.span,
                )
                .secondary_span(&function.span));
            }
            for ((px, pb), (fx, fb)) in
                proof_function.x.typ_bounds.iter().zip(function.x.typ_bounds.iter())
            {
                if px != fx || !crate::ast_util::generic_bounds_equal(&pb, &fb) {
                    return Err(air::errors::error(
                        "decreases_by/recommends_by function should have the same type bounds",
                        &proof_function.span,
                    )
                    .secondary_span(&function.span));
                }
            }
            if proof_function.x.params.len() != function.x.params.len() {
                return Err(air::errors::error(
                    "decreases_by/recommends_by function should have the same parameter types",
                    &proof_function.span,
                )
                .secondary_span(&function.span));
            }
            for (pp, fp) in proof_function.x.params.iter().zip(function.x.params.iter()) {
                if !crate::ast_util::params_equal(&pp, &fp) {
                    return Err(air::errors::error(
                        "decreases_by/recommends_by function should have the same parameter types",
                        &pp.span,
                    )
                    .secondary_span(&fp.span));
                }
            }
        }
    }
    for function in krate.functions.iter() {
        if function.x.attrs.is_decrease_by
            && !decreases_by_proof_to_spec.contains_key(&function.x.name)
        {
            return err_str(
                &function.span,
                "function cannot be marked #[verifier(decreases_by)] or #[verifier(recommends_by)] unless it used in some decreases_by//recommends_by",
            );
        }
    }

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
