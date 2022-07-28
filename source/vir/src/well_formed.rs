use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, FunX, Function, FunctionKind, Krate,
    MaskSpec, Mode, MultiOp, Path, PathX, TypX, UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_util::{err_str, err_string, error, path_as_rust_name, referenced_vars_expr};
use crate::datatype_to_air::is_datatype_transparent;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

struct Ctxt {
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

#[warn(unused_must_use)]
fn check_typ(
    _ctxt: &Ctxt,
    _function: &Function,
    typ: &Arc<TypX>,
    span: &air::ast::Span,
) -> Result<(), VirErr> {
    crate::ast_visitor::typ_visitor_check(typ, &mut |t| {
        if let crate::ast::TypX::Datatype(path, _) = &**t {
            let PathX { krate, segments: _ } = &**path;
            match krate {
                None => Ok(()),
                Some(krate_name)
                    if crate::def::SUPPORTED_CRATES.contains(&&krate_name.as_str()) =>
                {
                    Ok(())
                }
                Some(_) => err_str(
                    span,
                    "`{path:}` is not supported (note: currently Verus does not support definitions external to the crate, including most features in std)",
                ),
            }
        } else {
            Ok(())
        }
    })
}

fn check_one_expr(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<&str>,
) -> Result<(), VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Static(x, _), args) => {
            let f = match ctxt.funs.get(x) {
                Some(f) => f,
                None => {
                    let path = path_as_rust_name(&x.path);
                    return err_str(
                        &expr.span,
                        &format!(
                            "`{path:}` is not supported (note: currently Verus does not support definitions external to the crate, including most features in std)"
                        ),
                    );
                }
            };
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
                        ExprX::Unary(UnaryOp::CoerceMode { .. }, e1) => is_ok(e1),
                        ExprX::UnaryOpr(UnaryOpr::Field { .. }, base) => is_ok(base),
                        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => is_ok(e1),
                        ExprX::Ghost { alloc_wrapper: None, tracked: true, expr: e1 } => is_ok(e1),
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
                            "constructor of datatype with inaccessible fields here",
                        );
                    }
                }
                match (disallow_private_access, &dt.x.transparency, dt.x.visibility.is_private) {
                    (None, _, _) => {}
                    (_, crate::ast::DatatypeTransparency::Always, false) => {}
                    (Some(msg), _, _) => {
                        return err_str(&expr.span, msg);
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
                            "field access of datatype with inaccessible fields here",
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
        ExprX::Multi(MultiOp::Chained(ops), _) => {
            if ops.len() < 1 {
                return err_str(
                    &expr.span,
                    "chained inequalities must have at least one inequality",
                );
            }
        }
        ExprX::OpenInvariant(_inv, _binder, body, _atomicity) => {
            assert_no_early_exit_in_inv_block(&body.span, body)?;
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if function.x.attrs.nonlinear {
                return err_str(
                    &expr.span,
                    "assert_by_query not allowed in #[verifier(nonlinear)] functions",
                );
            }

            let mut referenced = HashSet::new();
            for r in requires.iter() {
                referenced.extend(referenced_vars_expr(r).into_iter());
            }
            for r in ensures.iter() {
                referenced.extend(referenced_vars_expr(r).into_iter());
            }

            use crate::visitor::VisitorControlFlow;

            match crate::ast_visitor::expr_visitor_dfs(
                proof,
                &mut crate::ast_visitor::VisitorScopeMap::new(),
                &mut |scope_map, e| match &e.x {
                    ExprX::Var(x) | ExprX::VarLoc(x)
                        if !scope_map.contains_key(&x) && !referenced.contains(x) =>
                    {
                        VisitorControlFlow::Stop(error(
                            format!("variable {} not mentioned in requires/ensures", x).as_str(),
                            &e.span,
                        ))
                    }
                    _ => VisitorControlFlow::Recurse,
                },
            ) {
                VisitorControlFlow::Recurse => Ok(()),
                VisitorControlFlow::Return => unreachable!(),
                VisitorControlFlow::Stop(e) => Err(e),
            }?;
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
        check_typ(ctxt, function, &p.x.typ, &p.span)?;
        if p.x.name == function.x.ret.x.name {
            return err_str(&p.span, "parameter name cannot be same as return value name");
        }
    }

    if function.x.attrs.inline {
        if function.x.mode != Mode::Spec {
            return err_str(&function.span, "'inline' is only allowed for 'spec' functions");
        }
        // make sure we don't leak private bodies by inlining
        if !function.x.visibility.is_private && function.x.publish != Some(true) {
            return err_str(
                &function.span,
                "'inline' is only allowed for private or 'open spec' functions",
            );
        }
        if function.x.decrease.len() != 0 {
            return err_str(&function.span, "'inline' functions cannot be recursive");
        }
        if function.x.body.is_none() {
            return err_str(&function.span, "'inline' functions must have a body");
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

    if (function.x.attrs.bit_vector
        && (function.x.attrs.nonlinear || function.x.attrs.integer_ring))
        || (!function.x.attrs.bit_vector
            && function.x.attrs.nonlinear
            && function.x.attrs.integer_ring)
    {
        return err_str(
            &function.span,
            "Select at most one verifier attribute: integer_ring, non_linear, bit_vector",
        );
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

    #[cfg(not(feature = "singular"))]
    if function.x.attrs.integer_ring {
        return err_str(
            &function.span,
            "Please cargo build with `--features singular` to use integer_ring attribute",
        );
    }

    #[cfg(feature = "singular")]
    if function.x.attrs.integer_ring {
        let _ = match std::env::var("VERUS_SINGULAR_PATH") {
            Ok(_) => {}
            Err(_) => {
                return err_str(
                    &function.span,
                    "Please provide VERUS_SINGULAR_PATH to use integer_ring attribute",
                );
            }
        };

        if function.x.mode != Mode::Proof {
            return err_str(&function.span, "integer_ring mode must be declared as proof");
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return err_str(&function.span, "integer_ring mode cannot have a body");
                    }
                }
                Ok(())
            })?;
        }
        for p in function.x.params.iter() {
            match *p.x.typ {
                TypX::Int(crate::ast::IntRange::Int) => {}
                TypX::Boxed(_) => {}
                _ => {
                    return err_str(
                        &p.span,
                        "integer_ring proof's parameters should all be int type",
                    );
                }
            }
        }
        if function.x.ensure.len() != 1 {
            return err_str(
                &function.span,
                "only a single ensures is allowed in integer_ring mode",
            );
        } else {
            let ens = function.x.ensure[0].clone();
            if let crate::ast::ExprX::Binary(crate::ast::BinaryOp::Eq(_), lhs, rhs) = &ens.x {
                if let crate::ast::ExprX::Binary(
                    crate::ast::BinaryOp::Arith(crate::ast::ArithOp::EuclideanMod, _),
                    _,
                    _,
                ) = &lhs.x
                {
                    match &rhs.x {
                        crate::ast::ExprX::Const(crate::ast::Constant::Nat(zero))
                            if "0" == (**zero).as_str() => {}
                        _ => {
                            return err_str(
                                &function.span,
                                "integer_ring mode ensures expression error: when the lhs is has % operator, the rhs should be zero. The ensures expression should be `Expr % m == 0` or `Expr == Expr` ",
                            );
                        }
                    }
                }
            } else {
                return err_str(
                    &function.span,
                    "In the integer_ring's ensures expression, the outermost operator should be equality operator. For example, inequality operator is not supported",
                );
            }
        }
        if function.x.has_return() {
            return err_str(
                &function.span,
                "integer_ring mode function cannot have a return value",
            );
        }
        for req in function.x.require.iter() {
            crate::ast_visitor::expr_visitor_check(req, &mut |expr| {
                match *expr.typ {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return err_str(
                            &req.span,
                            "integer_ring mode's expressions should be int/bool type",
                        );
                    }
                }
                Ok(())
            })?;
        }
        for ens in function.x.ensure.iter() {
            crate::ast_visitor::expr_visitor_check(ens, &mut |expr| {
                match *expr.typ {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return err_str(
                            &ens.span,
                            "integer_ring mode's expressions should be int/bool type",
                        );
                    }
                }
                Ok(())
            })?;
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

fn check_functions_match(
    msg: &str,
    check_names: bool,
    check_modes: bool,
    check_return: bool,
    f1: &Function,
    f2: &Function,
) -> Result<(), VirErr> {
    if f1.x.typ_bounds.len() != f2.x.typ_bounds.len() {
        return Err(air::errors::error(
            format!("{msg} function should have the same type bounds"),
            &f1.span,
        )
        .secondary_span(&f2.span));
    }
    for ((px, pb), (fx, fb)) in f1.x.typ_bounds.iter().zip(f2.x.typ_bounds.iter()) {
        if px != fx || !crate::ast_util::generic_bounds_equal(&pb, &fb) {
            return Err(air::errors::error(
                format!("{msg} function should have the same type bounds"),
                &f1.span,
            )
            .secondary_span(&f2.span));
        }
    }
    if f1.x.params.len() != f2.x.params.len() {
        return Err(air::errors::error(
            format!("{msg} function should have the same number of parameters"),
            &f1.span,
        )
        .secondary_span(&f2.span));
    }
    for (pp, fp) in f1.x.params.iter().zip(f2.x.params.iter()) {
        if !crate::ast_util::params_equal_opt(&pp, &fp, check_names, check_modes) {
            return Err(air::errors::error(
                format!("{msg} function should have the same parameter types"),
                &pp.span,
            )
            .secondary_span(&fp.span));
        }
    }
    if check_return {
        if !crate::ast_util::params_equal_opt(&f1.x.ret, &f2.x.ret, check_names, check_modes) {
            return Err(air::errors::error(
                format!("{msg} function should have the same return types"),
                &f1.x.ret.span,
            )
            .secondary_span(&f2.x.ret.span));
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
            check_functions_match(
                "decreases_by/recommends_by",
                true,
                true,
                false,
                &proof_function,
                &function,
            )?;
        }
        if let Some(spec_fun) = &function.x.attrs.autospec {
            let spec_function = if let Some(spec_function) = funs.get(spec_fun) {
                spec_function
            } else {
                return err_str(
                    &function.span,
                    "cannot find function referred to in when_used_as_spec",
                );
            };
            if function.x.mode != Mode::Exec || spec_function.x.mode != Mode::Spec {
                return Err(air::errors::error(
                    "when_used_as_spec must point from an exec function to a spec function",
                    &spec_function.span,
                )
                .secondary_span(&function.span));
            }
            check_functions_match(
                "when_used_as_spec",
                false,
                false,
                true,
                &spec_function,
                &function,
            )?;
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
