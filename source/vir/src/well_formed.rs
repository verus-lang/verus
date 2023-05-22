use crate::ast::{
    CallTarget, Datatype, Expr, ExprX, FieldOpr, Fun, Function, FunctionKind, Krate, MaskSpec,
    Mode, MultiOp, Path, PathX, TypX, UnaryOp, UnaryOpr, VirErr, VirErrAs,
};
use crate::ast_util::{
    error, is_visible_to_opt, msg_error, path_as_rust_name, referenced_vars_expr,
};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::user_local_name;
use crate::early_exit_cf::assert_no_early_exit_in_inv_block;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

struct Ctxt {
    pub(crate) crate_names: Vec<String>,
    pub(crate) funs: HashMap<Fun, Function>,
    pub(crate) dts: HashMap<Path, Datatype>,
}

#[warn(unused_must_use)]
fn check_typ(ctxt: &Ctxt, typ: &Arc<TypX>, span: &air::ast::Span) -> Result<(), VirErr> {
    crate::ast_visitor::typ_visitor_check(typ, &mut |t| {
        if let crate::ast::TypX::Datatype(path, _) = &**t {
            let PathX { krate, segments: _ } = &**path;
            match krate {
                None => Ok(()),
                Some(krate_name) if ctxt.crate_names.contains(&krate_name) => Ok(()),
                Some(_) => error(
                    span,
                    &format!(
                        "type `{:}` is not supported (note: currently Verus does not support definitions external to the crate, including most features in std)",
                        path_as_rust_name(path)
                    ),
                ),
            }
        } else {
            Ok(())
        }
    })
}

fn check_path_and_get_function<'a>(
    ctxt: &'a Ctxt,
    x: &Fun,
    disallow_private_access: Option<(&Option<Path>, &str)>,
    span: &air::ast::Span,
) -> Result<&'a Function, VirErr> {
    let f = match ctxt.funs.get(x) {
        Some(f) => f,
        None => {
            let path = path_as_rust_name(&x.path);
            return error(
                span,
                &format!(
                    "`{path:}` is not supported (note: currently Verus does not support definitions external to the crate, including most features in std)"
                ),
            );
        }
    };

    if let Some((source_module, msg)) = disallow_private_access {
        if !is_visible_to_opt(&f.x.visibility, source_module) {
            return error(&span, msg);
        }
    }

    Ok(f)
}

fn check_one_expr(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<(&Option<Path>, &str)>,
) -> Result<(), VirErr> {
    match &expr.x {
        ExprX::ConstVar(x) => {
            check_path_and_get_function(ctxt, x, disallow_private_access, &expr.span)?;
        }
        ExprX::Call(CallTarget::Static(x, _), args) => {
            let f = check_path_and_get_function(ctxt, x, disallow_private_access, &expr.span)?;
            if f.x.attrs.is_decrease_by {
                // a decreases_by function isn't a real function;
                // it's just a container for proof code that goes in the corresponding spec function
                return error(
                    &expr.span,
                    "cannot call a decreases_by/recommends_by function directly",
                );
            }
            if f.x.attrs.broadcast_forall && f.x.params.len() == 0 {
                // REVIEW: this is a rather arbitrary restriction due to ast_simplify's treatment of 0-argument functions.
                // When we generalize broadcast_forall, this restriction should be removed.
                return error(
                    &expr.span,
                    "cannot call a broadcast_forall function with 0 arguments directly",
                );
            }
            for (_param, arg) in f.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.is_mut) {
                fn is_ok(e: &Expr) -> bool {
                    match &e.x {
                        ExprX::VarLoc(_) => true,
                        ExprX::Unary(UnaryOp::CoerceMode { .. }, e1) => is_ok(e1),
                        ExprX::UnaryOpr(UnaryOpr::Field { .. }, base) => is_ok(base),
                        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => is_ok(e1),
                        ExprX::Ghost { alloc_wrapper: false, tracked: true, expr: e1 } => is_ok(e1),
                        _ => false,
                    }
                }
                let arg_x = match &arg.x {
                    // Tracked(&mut x) and Ghost(&mut x) arguments appear as
                    // Expr::Ghost { ... Expr::Loc ... }
                    ExprX::Ghost { alloc_wrapper: true, tracked: _, expr: e } => &e.x,
                    e => e,
                };
                let is_ok = match &arg_x {
                    ExprX::Loc(l) => is_ok(l),
                    _ => false,
                };
                if !is_ok {
                    return error(
                        &arg.span,
                        "complex arguments to &mut parameters are currently unsupported",
                    );
                }
            }
        }
        ExprX::Ctor(path, _variant, _fields, _update) => {
            if let Some(dt) = ctxt.dts.get(path) {
                if let Some(module) = &function.x.visibility.owning_module {
                    if !is_datatype_transparent(&module, dt) {
                        return Err(msg_error(
                            "constructor of datatype with inaccessible fields",
                            &expr.span,
                        ).secondary_label(
                            &dt.span,
                            "a datatype is treated as opaque whenever at least one field is not visible"
                        ));
                    }
                }
                use crate::ast::{DatatypeTransparency, Visibility};
                let field_vis = match dt.x.transparency {
                    DatatypeTransparency::Never => None,
                    DatatypeTransparency::WithinModule => {
                        let own = &dt.x.visibility.owning_module;
                        Some(Visibility { restricted_to: own.clone(), owning_module: own.clone() })
                    }
                    DatatypeTransparency::Always => Some(dt.x.visibility.clone()),
                };
                match (disallow_private_access, field_vis) {
                    (None, _) => {}
                    (Some((source_module, _)), Some(field_vis))
                        if is_visible_to_opt(&field_vis, source_module) => {}
                    (Some((_, msg)), _) => {
                        return error(&expr.span, msg);
                    }
                }
            } else {
                return error(
                    &expr.span,
                    &format!(
                        "`{:}` is not supported (note: currently Verus does not support definitions external to the crate, including most features in std)",
                        path_as_rust_name(path)
                    ),
                );
            }
        }
        ExprX::UnaryOpr(UnaryOpr::CustomErr(_), e) => {
            if !crate::ast_util::type_is_bool(&e.typ) {
                return error(
                    &expr.span,
                    "`custom_err` attribute only makes sense for bool expressions",
                );
            }
        }
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr { datatype: path, variant, field, get_variant: _ }),
            _,
        ) => {
            if let Some(dt) = ctxt.dts.get(path) {
                if let Some(module) = &function.x.visibility.owning_module {
                    if !is_datatype_transparent(&module, dt) {
                        return Err(msg_error(
                            "field access of datatype with inaccessible fields",
                            &expr.span,
                        ).secondary_label(
                            &dt.span,
                            "a datatype is treated as opaque whenever at least one field is not visible"
                        ));
                    }
                }
                if let Some((source_module, msg)) = disallow_private_access {
                    let variant = dt.x.get_variant(variant);
                    let (_, _, vis) = &crate::ast_util::get_field(&variant.a, &field).a;
                    if !is_visible_to_opt(vis, source_module) {
                        return error(&expr.span, msg);
                    }
                }
            } else {
                return error(&expr.span, "field access of datatype with inaccessible fields");
            }
        }
        ExprX::Multi(MultiOp::Chained(ops), _) => {
            if ops.len() < 1 {
                return error(&expr.span, "chained inequalities must have at least one inequality");
            }
        }
        ExprX::OpenInvariant(_inv, _binder, body, _atomicity) => {
            assert_no_early_exit_in_inv_block(&body.span, body)?;
        }
        ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
            if function.x.attrs.nonlinear {
                return error(
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
                        VisitorControlFlow::Stop(msg_error(
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
        ExprX::ExecClosure { .. } => {
            crate::closures::check_closure_well_formed(expr)?;
        }
        ExprX::Fuel(f, fuel) => {
            let f = check_path_and_get_function(ctxt, f, None, &expr.span)?;
            if f.x.mode != Mode::Spec {
                return error(
                    &expr.span,
                    &format!(
                        "reveal/fuel statements require a spec-mode function, got {:}-mode function",
                        f.x.mode
                    ),
                );
            }
            if f.x.decrease.is_empty() && *fuel > 1 {
                return error(
                    &expr.span,
                    "reveal_with_fuel statements require a function with a decreases clause",
                );
            }
        }
        _ => {}
    }
    Ok(())
}

fn check_expr(
    ctxt: &Ctxt,
    function: &Function,
    expr: &Expr,
    disallow_private_access: Option<(&Option<Path>, &str)>,
) -> Result<(), VirErr> {
    crate::ast_visitor::expr_visitor_check(expr, &mut |_scope_map, expr| {
        check_one_expr(ctxt, function, expr, disallow_private_access)
    })
}

fn check_function(
    ctxt: &Ctxt,
    function: &Function,
    diags: &mut Vec<VirErrAs>,
) -> Result<(), VirErr> {
    if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
        if function.x.body.is_some() && function.x.mode != Mode::Exec {
            // REVIEW: If we allow default method implementations, we'll need to make sure
            // it doesn't introduce nontermination into proof/spec.
            return error(
                &function.span,
                "trait proof/spec method declaration cannot provide a default implementation",
            );
        }
        if !matches!(function.x.mask_spec, MaskSpec::NoSpec) {
            return error(
                &function.span,
                "not yet supported: trait method declarations that open invariants",
            );
        }
    }

    if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
        if function.x.require.len() + function.x.ensure.len() != 0 {
            return error(
                &function.span,
                "trait method implementation cannot declare requires/ensures; these can only be inherited from the trait declaration",
            );
        }
        if !matches!(function.x.mask_spec, MaskSpec::NoSpec) {
            return error(
                &function.span,
                "trait method implementation cannot open invariants; this can only be inherited from the trait declaration",
            );
        }
    }

    if function.x.attrs.is_decrease_by {
        match function.x.kind {
            FunctionKind::Static => {}
            FunctionKind::TraitMethodDecl { .. } | FunctionKind::TraitMethodImpl { .. } => {
                return error(
                    &function.span,
                    "decreases_by/recommends_by function cannot be a trait method",
                );
            }
        }
        if function.x.mode != Mode::Proof {
            return error(
                &function.span,
                "decreases_by/recommends_by function must have mode proof",
            );
        }
        if function.x.decrease.len() != 0 {
            return error(
                &function.span,
                "decreases_by/recommends_by function cannot have its own decreases clause",
            );
        }
        if function.x.require.len() != 0 {
            return error(
                &function.span,
                "decreases_by/recommends_by function cannot have requires clauses (use decreases_when in the spec function instead)",
            );
        }
        if function.x.ensure.len() != 0 {
            return error(
                &function.span,
                "decreases_by/recommends_by function cannot have ensures clauses",
            );
        }
        if function.x.has_return() {
            return error(
                &function.span,
                "decreases_by/recommends_by function cannot have a return value",
            );
        }
    }

    if function.x.decrease_by.is_some() {
        if function.x.mode != Mode::Spec {
            return error(&function.span, "only spec functions can use decreases_by/recommends_by");
        }
    }

    let ret_name = user_local_name(&*function.x.ret.x.name);
    for p in function.x.params.iter() {
        check_typ(ctxt, &p.x.typ, &p.span)?;
        if user_local_name(&*p.x.name) == ret_name {
            return error(&p.span, "parameter name cannot be the same as the return value name");
        }
    }

    if function.x.attrs.inline {
        if function.x.mode != Mode::Spec {
            return error(&function.span, "'inline' is only allowed for 'spec' functions");
        }
        // make sure we don't leak private bodies by inlining
        if !function.x.visibility.is_private() && function.x.publish != Some(true) {
            return error(
                &function.span,
                "'inline' is only allowed for private or 'open spec' functions",
            );
        }
        if function.x.decrease.len() != 0 {
            return error(&function.span, "'inline' functions cannot be recursive");
        }
        if function.x.body.is_none() {
            return error(&function.span, "'inline' functions must have a body");
        }
    }

    if function.x.attrs.atomic {
        if function.x.mode != Mode::Exec {
            return error(&function.span, "'atomic' only makes sense on an 'exec' function");
        }
    }
    match &function.x.mask_spec {
        MaskSpec::NoSpec => {}
        _ => {
            if function.x.mode == Mode::Spec {
                return error(&function.span, "invariants cannot be opened in spec functions");
            }
        }
    }
    if function.x.attrs.broadcast_forall {
        if function.x.mode != Mode::Proof {
            return error(&function.span, "broadcast_forall function must be declared as proof");
        }
        if function.x.has_return() {
            return error(&function.span, "broadcast_forall function cannot have return type");
        }
        for param in function.x.params.iter() {
            if param.x.mode != Mode::Spec {
                return error(
                    &function.span,
                    "broadcast_forall function must have spec parameters",
                );
            }
        }
        if function.x.body.is_some() {
            return error(
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
        return error(
            &function.span,
            "Select at most one verifier attribute: integer_ring, non_linear, bit_vector",
        );
    }

    if function.x.attrs.bit_vector {
        if function.x.mode != Mode::Proof {
            return error(&function.span, "bit-vector function mode must be declared as proof");
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_scope_map, expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return error(
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
                    return error(
                        &p.span,
                        "bit-vector function mode cannot have a datatype other than Integer/Boolean",
                    );
                }
            }
        }
    }

    #[cfg(not(feature = "singular"))]
    if function.x.attrs.integer_ring {
        return error(
            &function.span,
            "Please cargo build with `--features singular` to use integer_ring attribute",
        );
    }

    #[cfg(feature = "singular")]
    if function.x.attrs.integer_ring {
        use crate::ast_util::undecorate_typ;
        let _ = match std::env::var("VERUS_SINGULAR_PATH") {
            Ok(_) => {}
            Err(_) => {
                return error(
                    &function.span,
                    "Please provide VERUS_SINGULAR_PATH to use integer_ring attribute",
                );
            }
        };

        if function.x.mode != Mode::Proof {
            return error(&function.span, "integer_ring mode must be declared as proof");
        }
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_scope_map, expr| {
                match &expr.x {
                    ExprX::Block(_, _) => {}
                    _ => {
                        return error(&function.span, "integer_ring mode cannot have a body");
                    }
                }
                Ok(())
            })?;
        }
        for p in function.x.params.iter() {
            match *undecorate_typ(&p.x.typ) {
                TypX::Int(crate::ast::IntRange::Int) => {}
                TypX::Boxed(_) => {}
                _ => {
                    return error(
                        &p.span,
                        "integer_ring proof's parameters should all be int type",
                    );
                }
            }
        }
        if function.x.ensure.len() != 1 {
            return error(&function.span, "only a single ensures is allowed in integer_ring mode");
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
                        crate::ast::ExprX::Const(crate::ast::Constant::Int(zero))
                            if "0" == zero.to_string() => {}
                        _ => {
                            return error(
                                &function.span,
                                "integer_ring mode ensures expression error: when the lhs is has % operator, the rhs should be zero. The ensures expression should be `Expr % m == 0` or `Expr == Expr` ",
                            );
                        }
                    }
                }
            } else {
                return error(
                    &function.span,
                    "In the integer_ring's ensures expression, the outermost operator should be equality operator. For example, inequality operator is not supported",
                );
            }
        }
        if function.x.has_return() {
            return error(&function.span, "integer_ring mode function cannot have a return value");
        }
        for req in function.x.require.iter() {
            crate::ast_visitor::expr_visitor_check(req, &mut |_scope_map, expr| {
                match *undecorate_typ(&expr.typ) {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return error(
                            &req.span,
                            "integer_ring mode's expressions should be int/bool type",
                        );
                    }
                }
                Ok(())
            })?;
        }
        for ens in function.x.ensure.iter() {
            crate::ast_visitor::expr_visitor_check(ens, &mut |_scope_map, expr| {
                match *undecorate_typ(&expr.typ) {
                    TypX::Int(crate::ast::IntRange::Int) => {}
                    TypX::Bool => {}
                    TypX::Boxed(_) => {}
                    _ => {
                        return error(
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
            return error(
                &function.span,
                "#[verifier(nonlinear) is only allowed on proof and exec functions",
            );
        }
    }

    if function.x.publish.is_some() && function.x.mode != Mode::Spec {
        return error(
            &function.span,
            "function is marked #[verifier(publish)] but not marked #[verifier::spec]",
        );
    }

    if function.x.is_main() && function.x.mode != Mode::Exec {
        return error(&function.span, "`main` function should be #[verifier::exec]");
    }

    if function.x.publish.is_some() && function.x.visibility.is_private() {
        return error(
            &function.span,
            "function is marked #[verifier(publish)] but not marked `pub`; for the body of a function to be visible, the function symbol must also be visible",
        );
    }

    for req in function.x.require.iter() {
        let msg = "public function requires cannot refer to private items";
        let disallow_private_access = Some((&function.x.visibility.restricted_to, msg));
        check_expr(ctxt, function, req, disallow_private_access)?;
        crate::ast_visitor::expr_visitor_check(req, &mut |_scope_map, expr| {
            if let ExprX::Var(x) = &expr.x {
                for param in function.x.params.iter().filter(|p| p.x.is_mut) {
                    if *x == param.x.name {
                        return error(
                            &expr.span,
                            format!(
                                "in requires, use `old({})` to refer to the pre-state of an &mut variable",
                                crate::def::user_local_name(&param.x.name)
                            ),
                        );
                    }
                }
            }
            Ok(())
        })?;
    }
    for ens in function.x.ensure.iter() {
        let msg = "public function ensures cannot refer to private items";
        let disallow_private_access = Some((&function.x.visibility.restricted_to, msg));
        check_expr(ctxt, function, ens, disallow_private_access)?;
    }
    for expr in function.x.decrease.iter() {
        let msg = "public function decreases cannot refer to private items";
        let disallow_private_access = Some((&function.x.visibility.restricted_to, msg));
        check_expr(ctxt, function, expr, disallow_private_access)?;
    }
    if let Some(expr) = &function.x.decrease_when {
        let msg = "public function decreases_when cannot refer to private items";
        let disallow_private_access = Some((&function.x.visibility.restricted_to, msg));
        if function.x.mode != Mode::Spec {
            return error(
                &function.span,
                "only spec functions can use decreases_when (use requires for proof/exec functions)",
            );
        }
        if function.x.decrease.len() == 0 {
            return error(
                &function.span,
                "decreases_when can only be used when there is a decreases clause (use recommends(...) for nonrecursive functions)",
            );
        }
        check_expr(ctxt, function, expr, disallow_private_access)?;
    }

    if function.x.mode == Mode::Exec
        && (function.x.decrease.len() > 0 || function.x.decrease_by.is_some())
    {
        diags.push(VirErrAs::Warning(
            msg_error("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers", &function.span),
        ));
    }

    if let Some(body) = &function.x.body {
        // Check that public, non-abstract spec function bodies don't refer to private items:
        let disallow_private_access = match (&function.x.publish, function.x.mode) {
            (Some(_), Mode::Spec) => {
                let msg = "public spec function cannot refer to private items, if it is marked #[verifier(publish)]";
                Some((&function.x.visibility.restricted_to, msg))
            }
            _ => None,
        };
        check_expr(ctxt, function, body, disallow_private_access)?;
    }
    Ok(())
}

fn check_datatype(ctxt: &Ctxt, dt: &Datatype) -> Result<(), VirErr> {
    for variant in dt.x.variants.iter() {
        for field in variant.a.iter() {
            let typ = &field.a.0;
            check_typ(ctxt, typ, &dt.span)?;
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
        return Err(air::messages::error(
            format!("{msg} function should have the same type bounds"),
            &f1.span,
        )
        .secondary_span(&f2.span));
    }
    for ((px, pb), (fx, fb)) in f1.x.typ_bounds.iter().zip(f2.x.typ_bounds.iter()) {
        if px != fx || !crate::ast_util::generic_bounds_equal(&pb, &fb) {
            return Err(air::messages::error(
                format!("{msg} function should have the same type bounds"),
                &f1.span,
            )
            .secondary_span(&f2.span));
        }
    }
    if f1.x.params.len() != f2.x.params.len() {
        return Err(air::messages::error(
            format!("{msg} function should have the same number of parameters"),
            &f1.span,
        )
        .secondary_span(&f2.span));
    }
    for (pp, fp) in f1.x.params.iter().zip(f2.x.params.iter()) {
        if !crate::ast_util::params_equal_opt(&pp, &fp, check_names, check_modes) {
            return Err(air::messages::error(
                format!("{msg} function should have the same parameters"),
                &pp.span,
            )
            .secondary_span(&fp.span));
        }
    }
    if check_return {
        if !crate::ast_util::params_equal_opt(&f1.x.ret, &f2.x.ret, check_names, check_modes) {
            return Err(air::messages::error(
                format!("{msg} function should have the same return types"),
                &f1.x.ret.span,
            )
            .secondary_span(&f2.x.ret.span));
        }
    }
    Ok(())
}

pub fn check_crate(
    krate: &Krate,
    mut crate_names: Vec<String>,
    diags: &mut Vec<VirErrAs>,
) -> Result<(), VirErr> {
    crate_names.push("builtin".to_string());
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    for function in krate.functions.iter() {
        if funs.contains_key(&function.x.name) {
            return Err(air::messages::error(
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
                return error(
                    &function.span,
                    "cannot find function referred to in decreases_by/recommends_by",
                );
            };
            if !proof_function.x.attrs.is_decrease_by {
                return Err(air::messages::error(
                    "proof function must be marked #[verifier(decreases_by)] or #[verifier(recommends_by)] to be used as decreases_by/recommends_by",
                    &proof_function.span,
                )
                .secondary_span(&function.span));
            }
            if let Some(prev) = decreases_by_proof_to_spec.get(proof_fun) {
                return Err(air::messages::error(
                    "same proof function used for two different decreases_by/recommends_by",
                    &proof_function.span,
                )
                .secondary_span(&funs[prev].span)
                .secondary_span(&function.span));
            }
            if proof_fun.path.pop_segment() != function.x.name.path.pop_segment() {
                return Err(air::messages::error(
                    "a decreases_by function must be in the same module as the function definition",
                    &proof_function.span,
                )
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
                return error(
                    &function.span,
                    "cannot find function referred to in when_used_as_spec",
                );
            };
            if function.x.mode != Mode::Exec || spec_function.x.mode != Mode::Spec {
                return Err(air::messages::error(
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
            return error(
                &function.span,
                "function cannot be marked #[verifier(decreases_by)] or #[verifier(recommends_by)] unless it is used in some decreases_by/recommends_by",
            );
        }
    }

    let ctxt = Ctxt { crate_names, funs, dts };
    for function in krate.functions.iter() {
        check_function(&ctxt, function, diags)?;
    }
    for dt in krate.datatypes.iter() {
        check_datatype(&ctxt, dt)?;
    }
    crate::recursive_types::check_recursive_types(krate)?;
    Ok(())
}
