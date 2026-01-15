use crate::attributes::{GhostBlockAttr, get_ghost_block_opt};
use crate::config::Vstd;
use crate::context::BodyCtxt;
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::resolve_traits::{ResolutionResult, ResolvedItem, resolve_trait_item};
use crate::reveal_hide::RevealHideResult;
use crate::rust_to_vir_base::{
    bitwidth_and_signedness_of_integer_type, is_smt_arith, is_type_std_rc_or_arc_or_ref,
    typ_of_node, typ_of_node_expect_mut_ref,
};
use crate::rust_to_vir_expr::{
    ExprModifier, check_lit_int, closure_param_typs, closure_to_vir, expr_to_vir,
    expr_to_vir_consume, extract_array, extract_tuple, get_fn_path, is_expr_typ_mut_ref,
    mk_ty_clip, pat_to_var,
};
use crate::util::{err_span, vec_map, vec_map_result, vir_err_span_str};
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, BuiltinFunctionItem, ChainedItem, CompilableOprItem,
    DirectiveItem, EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem,
    SpecGhostTrackedItem, SpecItem, SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use crate::{unsupported_err, unsupported_err_unless};
use air::ast_util::str_ident;
use rustc_ast::LitKind;
use rustc_hir::def::Res;
use rustc_hir::{Block, BlockCheckMode, Expr, ExprKind, Node, QPath, StmtKind};
use rustc_middle::ty::{GenericArg, GenericArgKind, TyKind, TypingEnv};
use rustc_mir_build_verus::verus::BodyErasure;
use rustc_span::Span;
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_trait_selection::infer::InferCtxtExt;
use std::sync::Arc;
use vir::ast::{
    ArithOp, ArrayKind, AssertQueryMode, AutospecUsage, BinaryOp, BitshiftBehavior, BitwiseOp,
    BoundsCheck, BuiltinSpecFun, CallTarget, ChainedOp, ComputeMode, Constant, Div0Behavior, ExprX,
    FieldOpr, FunX, HeaderExpr, HeaderExprX, InequalityOp, IntRange, IntegerTypeBoundKind, Mode,
    ModeCoercion, ModeWrapperMode, MultiOp, OverflowBehavior, Place, PlaceX, Quant, Typ,
    TypDecoration, TypX, UnaryOp, UnaryOpr, VarAt, VarBinder, VarBinderX, VarIdent, VariantCheck,
    VirErr,
};
use vir::ast_util::{
    const_int_from_string, mk_tuple_typ, mk_tuple_x, typ_to_diagnostic_str, types_equal,
    undecorate_typ, unit_typ, unpack_tuple,
};
use vir::def::field_ident_from_rust;

pub(crate) fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    _fn_span: Span,
    args: Vec<&'tcx Expr<'tcx>>,
    outer_modifier: ExprModifier,
    is_method: bool,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;

    let expr_typ = || typ_of_node(bctx, expr.span, &expr.hir_id, false);

    let rust_item = verus_items::get_rust_item(tcx, f);
    let verus_item = bctx.ctxt.get_verus_item(f);

    if bctx.external_body
        && !matches!(
            verus_item,
            Some(
                VerusItem::Spec(
                    SpecItem::Requires
                        | SpecItem::Recommends
                        | SpecItem::Ensures
                        | SpecItem::Returns
                        | SpecItem::OpensInvariantsNone
                        | SpecItem::OpensInvariantsAny
                        | SpecItem::OpensInvariants
                        | SpecItem::OpensInvariantsExcept
                        | SpecItem::NoUnwind
                        | SpecItem::NoUnwindWhen
                ) | VerusItem::Directive(DirectiveItem::ExtraDependency)
            )
        )
    {
        return Ok(bctx.spanned_typed_new(
            expr.span,
            &expr_typ()?,
            ExprX::Block(Arc::new(vec![]), None),
        ));
    }

    match rust_item {
        Some(RustItem::BoxNew) if bctx.in_ghost => {
            record_compilable_operator(bctx, expr, CompilableOperator::BoxNew);
            return mk_one_vir_arg(bctx, expr.span, &args);
        }
        Some(RustItem::RcNew) if bctx.in_ghost => {
            record_compilable_operator(bctx, expr, CompilableOperator::RcNew);
            return mk_one_vir_arg(bctx, expr.span, &args);
        }
        Some(RustItem::ArcNew) if bctx.in_ghost => {
            record_compilable_operator(bctx, expr, CompilableOperator::ArcNew);
            return mk_one_vir_arg(bctx, expr.span, &args);
        }
        Some(RustItem::Panic) => {
            return err_span(
                expr.span,
                format!(
                    "panic is not supported (if you used Rust's `assert!` macro, you may have meant to use Verus's `assert` function)"
                ),
            );
        }
        Some(RustItem::CloneClone) => {
            // Special case `clone` for standard Rc and Arc types
            // (Could also handle it for other types where cloning is the identity
            // operation in the SMT encoding.)
            let arg_typ = node_substs[0].expect_ty();

            if is_type_std_rc_or_arc_or_ref(bctx.ctxt.tcx, arg_typ) {
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                record_compilable_operator(
                    bctx,
                    expr,
                    CompilableOperator::SmartPtrClone { is_method },
                );
                return Ok(arg);
            }
        }
        Some(RustItem::CloneFrom) => {
            return err_span(expr.span, "Verus does not yet support `clone_from`");
        }
        _ => {}
    }

    if let Some(verus_item) = verus_item {
        match verus_item {
            VerusItem::Vstd(_, _)
            | VerusItem::Marker(_)
            | VerusItem::BuiltinType(_)
            | VerusItem::External(_)
            | VerusItem::BuiltinFunction(BuiltinFunctionItem::ConstrainType) => (),
            _ => {
                return verus_item_to_vir(
                    bctx,
                    expr,
                    expr_typ,
                    verus_item,
                    &args,
                    tcx,
                    node_substs,
                    f,
                    outer_modifier,
                );
            }
        }
    }

    let f_attrs = bctx.ctxt.tcx.get_all_attrs(f);
    if crate::attributes::is_get_field_many_variants(
        f_attrs,
        Some(&mut *bctx.ctxt.diagnostics.borrow_mut()),
    )? {
        return Err(vir::messages::error(
            &crate::spans::err_air_span(expr.span),
            format!("this field is present in multiple variants, cannot use -> syntax"),
        )
        .help("use `matches` instead"));
    }

    // Normal function call

    let path = bctx.ctxt.def_id_to_vir_path(f);
    let name = Arc::new(FunX { path: path.clone() });
    let autospec_usage = if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };

    // Compute the 'target_kind'.
    //
    // If the target is a "trait function" then we try to resolve it to a statically known
    // implementation of that function. The target_kind stores this information,
    // known or unknown.
    //
    // If the resolution is statically known, we record the resolved function for the
    // to be used by lifetime_generate.

    let node_substs = fix_node_substs(tcx, bctx.types, node_substs, rust_item, &args, expr);

    let mut record_name = name.clone();
    let target_kind = if tcx.trait_of_assoc(f).is_none() {
        vir::ast::CallTargetKind::Static
    } else {
        let typing_env = TypingEnv::non_body_analysis(tcx, bctx.fun_id);
        let res = resolve_trait_item(expr.span, tcx, typing_env, f, node_substs)?;
        match res {
            ResolutionResult::Resolved {
                impl_def_id: _,
                impl_args: _,
                impl_item_args: _,
                resolved_item: ResolvedItem::FromImpl(did, args),
            } => {
                let typs = mk_typ_args(bctx, args, did, expr.span)?;
                let impl_paths = get_impl_paths(bctx, did, args, None);

                let f = Arc::new(FunX { path: bctx.ctxt.def_id_to_vir_path(did) });
                record_name = f.clone();

                vir::ast::CallTargetKind::DynamicResolved {
                    resolved: f,
                    typs,
                    impl_paths,
                    is_trait_default: false,
                }
            }
            ResolutionResult::Resolved {
                impl_def_id: _,
                impl_args: _,
                impl_item_args: _,
                resolved_item: ResolvedItem::FromTrait(did, args),
            } => {
                // We resolved to the trait method itself, which means this must be
                // a default method implementation in the trait.
                // Redirect this to the appropriate per-instance copy of the default method.

                let typs = mk_typ_args(bctx, args, did, expr.span)?;

                let mut self_trait_impl_path = None;
                let trait_id = tcx.trait_of_assoc(did).unwrap();
                let remove_self_trait_bound = Some((trait_id, &mut self_trait_impl_path));
                let impl_paths = get_impl_paths(bctx, did, args, remove_self_trait_bound);

                let Some(vir::ast::ImplPath::TraitImplPath(impl_path)) = self_trait_impl_path
                else {
                    panic!("{} {:?}", "could not resolve call to trait default method", &expr.span);
                };

                let f = Arc::new(FunX { path: bctx.ctxt.def_id_to_vir_path(did) });
                record_name = f.clone();

                let f = vir::def::trait_inherit_default_name(&f, &impl_path);

                vir::ast::CallTargetKind::DynamicResolved {
                    resolved: f,
                    typs,
                    impl_paths,
                    is_trait_default: true,
                }
            }
            ResolutionResult::Builtin(
                rustc_trait_selection::traits::BuiltinImplSource::Object(_),
            ) => {
                // dyn T dispatch
                vir::ast::CallTargetKind::Dynamic
            }
            ResolutionResult::Builtin(b) => {
                unsupported_err!(expr.span, format!("built-in instance {:?}", b));
            }
            ResolutionResult::Unresolved => {
                // Method is generic
                vir::ast::CallTargetKind::Dynamic
            }
        }
    };

    record_call(bctx, expr, ResolvedCall::Call(name.clone(), record_name, bctx.in_ghost));

    let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;

    let typ_args = mk_typ_args(bctx, node_substs, f, expr.span)?;
    let impl_paths = get_impl_paths(bctx, f, node_substs, None);
    let target = CallTarget::Fun(target_kind, name, typ_args, impl_paths, autospec_usage);
    Ok(bctx.spanned_typed_new(
        expr.span,
        &expr_typ()?,
        ExprX::Call(target, Arc::new(vir_args), None),
    ))
}

pub(crate) fn deref_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    trait_fun_id: DefId,
    arg: vir::ast::Expr,
    expr_typ: Typ,
    arg_ty: rustc_middle::ty::Ty<'tcx>,
    span: Span,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let typing_env = TypingEnv::non_body_analysis(tcx, bctx.fun_id);
    // The `arg_ty`, if `&T`, should be Rust automatically adding the `&`
    // reference for calling `deref`. We strip it for trait resolution.
    //
    // Otherwise, it may be `deref` coercion. Leave it as-is.
    let arg_ty =
        if let TyKind::Ref(_, arg_ty, _) = arg_ty.kind() { arg_ty.clone() } else { arg_ty };
    let node_substs = tcx.mk_args(&[GenericArg::from(arg_ty)]);

    let trait_fun = Arc::new(FunX { path: bctx.ctxt.def_id_to_vir_path(trait_fun_id) });
    let mut record_trait_fun = trait_fun.clone();

    let res = resolve_trait_item(span, tcx, typing_env, trait_fun_id, node_substs)?;
    let target_kind = match res {
        ResolutionResult::Resolved { resolved_item: ResolvedItem::FromImpl(did, args), .. } => {
            let typs = mk_typ_args(bctx, args, did, span)?;
            let impl_paths = get_impl_paths(bctx, did, args, None);
            let resolved = Arc::new(FunX { path: bctx.ctxt.def_id_to_vir_path(did) });

            record_trait_fun = resolved.clone();

            vir::ast::CallTargetKind::DynamicResolved {
                resolved,
                typs,
                impl_paths,
                is_trait_default: false,
            }
        }
        ResolutionResult::Unresolved => vir::ast::CallTargetKind::Dynamic,
        _ => crate::internal_err!(span, "unexpected deref"),
    };

    let autospec_usage = if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };

    record_call(bctx, expr, ResolvedCall::Call(trait_fun.clone(), record_trait_fun, bctx.in_ghost));

    let typ_args = mk_typ_args(bctx, node_substs, trait_fun_id, span)?;
    let impl_paths = get_impl_paths(bctx, trait_fun_id, node_substs, None);
    let call_target = CallTarget::Fun(target_kind, trait_fun, typ_args, impl_paths, autospec_usage);
    let args = Arc::new(vec![arg.clone()]);
    let x = ExprX::Call(call_target, args, None);

    Ok(bctx.spanned_typed_new(span, &expr_typ, x))
}

fn verus_item_to_vir<'tcx, 'a>(
    bctx: &'a BodyCtxt<'tcx>,
    expr: &'a Expr<'tcx>,
    expr_typ: impl Fn() -> Result<Arc<TypX>, VirErr>,
    verus_item: &VerusItem,
    args: &'a Vec<&'tcx Expr<'tcx>>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    f: DefId,
    outer_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    // DO NOT use f_name to find items (i.e. do not use f_name == "core::cmp::Eq"),
    // use `crate::verus_item::get_rust_item` instead
    let f_name = tcx.def_path_str(f);
    let args_len = args.len();

    let mk_expr = |x: ExprX| Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, x));
    let mk_expr_span = |span: Span, x: ExprX| Ok(bctx.spanned_typed_new(span, &expr_typ()?, x));
    match verus_item {
        VerusItem::OpenInvariantBlock(_) => err_span(
            expr.span,
            format!(
                "{} should never be used except through open_atomic_invariant or open_local_invariant macro",
                f_name
            ),
        ),
        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Decimal)) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            unsupported_err_unless!(args_len == 1, expr.span, "expected spec_literal_*", &args);
            let arg = &args[0];
            let s = get_string_lit_arg(&args[0], &f_name)?;
            match &*expr_typ()? {
                TypX::Float(32) => {
                    let f: f32 = match s.to_string().parse() {
                        Ok(f) => f,
                        Err(err) => {
                            return err_span(arg.span, format!("float out of range {}", err));
                        }
                    };
                    mk_expr(ExprX::Const(Constant::Float32(f32::to_bits(f))))
                }
                TypX::Float(64) => {
                    let f: f64 = match s.to_string().parse() {
                        Ok(f) => f,
                        Err(err) => {
                            return err_span(arg.span, format!("float out of range {}", err));
                        }
                    };
                    mk_expr(ExprX::Const(Constant::Float64(f64::to_bits(f))))
                }
                TypX::Real => {
                    let is_valid_real = s.chars().all(|c| c.is_ascii_digit() || c == '.')
                        && s.chars().filter(|c| *c == '.').count() == 1
                        && !s.starts_with(".")
                        && !s.ends_with(".");
                    if !is_valid_real {
                        return err_span(
                            arg.span,
                            "real literal must be digits, followed by a decimal point, followed by digits",
                        );
                    }
                    mk_expr(ExprX::Const(Constant::Real(s.to_string())))
                }
                _ => {
                    return err_span(
                        expr.span,
                        format!(
                            "unexpected type for floating point or real literal: {}",
                            typ_to_diagnostic_str(&expr_typ()?),
                        ),
                    );
                }
            }
        }
        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(spec_literal_item)) => {
            record_spec_fn_allow_proof_args(bctx, expr);

            unsupported_err_unless!(args_len == 1, expr.span, "expected spec_literal_*", &args);
            let arg = &args[0];
            let s = get_string_lit_arg(&args[0], &f_name)?;
            let is_num = s.chars().count() > 0 && s.chars().all(|c| c.is_digit(10));
            if is_num {
                // TODO: negative literals for is_spec_literal_int and is_spec_literal_integer
                if spec_literal_item == &SpecLiteralItem::Integer {
                    // TODO: big integers for int, nat
                    let i: u128 = match s.to_string().parse() {
                        Ok(i) => i,
                        Err(err) => {
                            return err_span(arg.span, format!("integer out of range {}", err));
                        }
                    };
                    let in_negative_literal = false;
                    check_lit_int(&bctx.ctxt, expr.span, in_negative_literal, i, &expr_typ()?)?
                }
                mk_expr(ExprX::Const(const_int_from_string(s.to_string())))
            } else {
                err_span(arg.span, "spec_literal_* requires a string literal")
            }
        }
        VerusItem::Spec(spec_item) => match spec_item {
            SpecItem::NoMethodBody => {
                record_spec_fn_no_proof_args(bctx, expr);
                mk_expr(ExprX::Header(Arc::new(HeaderExprX::NoMethodBody)))
            }
            SpecItem::Requires
            | SpecItem::Recommends
            | SpecItem::OpensInvariants
            | SpecItem::Returns => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(
                    args_len == 1,
                    expr.span,
                    "expected requires/recommends",
                    &args
                );
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let subargs = extract_array(args[0]);

                let vir_args = vec_map_result(&subargs, |arg| {
                    expr_to_vir_consume(&bctx, arg, ExprModifier::REGULAR)
                })?;

                if matches!(spec_item, SpecItem::Returns) && subargs.len() != 1 {
                    return err_span(
                        expr.span,
                        "`returns` clause should have exactly 1 expression",
                    );
                }

                for (arg, vir_arg) in subargs.iter().zip(vir_args.iter()) {
                    let typ = vir::ast_util::undecorate_typ(&vir_arg.typ);
                    match spec_item {
                        SpecItem::Requires | SpecItem::Recommends => match &*typ {
                            TypX::Bool => {}
                            _ => {
                                return err_span(
                                    arg.span,
                                    "requires/recommends needs a bool expression",
                                );
                            }
                        },
                        SpecItem::OpensInvariants => match &*typ {
                            TypX::Int(_) => {}
                            _ => {
                                return err_span(
                                    arg.span,
                                    "opens_invariants needs an int expression",
                                );
                            }
                        },
                        SpecItem::Returns => {
                            // type is checked in well_formed.rs
                        }
                        _ => unreachable!(),
                    }
                }

                let header = match spec_item {
                    SpecItem::Requires => Arc::new(HeaderExprX::Requires(Arc::new(vir_args))),
                    SpecItem::Recommends => Arc::new(HeaderExprX::Recommends(Arc::new(vir_args))),
                    SpecItem::OpensInvariants => Arc::new(HeaderExprX::InvariantOpens(
                        bctx.ctxt.spans.to_air_span(expr.span.clone()),
                        Arc::new(vir_args),
                    )),
                    SpecItem::Returns => Arc::new(HeaderExprX::Returns(vir_args[0].clone())),
                    _ => unreachable!(),
                };
                mk_expr(ExprX::Header(header))
            }
            SpecItem::OpensInvariantsExcept => {
                record_spec_fn_no_proof_args(bctx, expr);
                err_span(
                    expr.span,
                    "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
                )
            }
            SpecItem::OpensInvariantsNone => {
                record_spec_fn_no_proof_args(bctx, expr);
                let header = Arc::new(HeaderExprX::InvariantOpens(
                    bctx.ctxt.spans.to_air_span(expr.span.clone()),
                    Arc::new(Vec::new()),
                ));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::OpensInvariantsAny => {
                record_spec_fn_no_proof_args(bctx, expr);
                let header = Arc::new(HeaderExprX::InvariantOpensExcept(
                    bctx.ctxt.spans.to_air_span(expr.span.clone()),
                    Arc::new(Vec::new()),
                ));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::OpensInvariantsSet => {
                record_spec_fn_no_proof_args(bctx, expr);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                let header = Arc::new(HeaderExprX::InvariantOpensSet(arg));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::Ensures => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected ensures", &args);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let header = extract_ensures(&bctx, args[0])?;
                // extract_ensures does most of the necessary work, so we can return at this point
                mk_expr_span(args[0].span, ExprX::Header(header))
            }
            SpecItem::Decreases => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected decreases", &args);
                let subargs = extract_tuple(args[0]);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args = vec_map_result(&subargs, |arg| {
                    expr_to_vir_consume(&bctx, arg, ExprModifier::REGULAR)
                })?;
                let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::InvariantExceptBreak | SpecItem::Invariant => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected invariant", &args);
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.expr_ty_adjusted(arg).kind(), TyKind::Bool) {
                        return err_span(arg.span, "invariant needs a bool expression");
                    }
                }
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args = vec_map_result(&subargs, |arg| {
                    expr_to_vir_consume(&bctx, arg, ExprModifier::REGULAR)
                })?;
                let header = match spec_item {
                    SpecItem::InvariantExceptBreak => {
                        Arc::new(HeaderExprX::InvariantExceptBreak(Arc::new(vir_args)))
                    }
                    SpecItem::Invariant => Arc::new(HeaderExprX::Invariant(Arc::new(vir_args))),
                    _ => unreachable!(),
                };
                mk_expr(ExprX::Header(header))
            }
            SpecItem::DecreasesBy | SpecItem::RecommendsBy => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected function", &args);
                let x = get_fn_path(bctx, &args[0])?;
                let header = Arc::new(HeaderExprX::DecreasesBy(x));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::DecreasesWhen => {
                record_spec_fn_no_proof_args(bctx, expr);
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                let header = Arc::new(HeaderExprX::DecreasesWhen(arg));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::NoUnwind => {
                record_spec_fn_no_proof_args(bctx, expr);
                let header = Arc::new(HeaderExprX::NoUnwind);
                mk_expr(ExprX::Header(header))
            }
            SpecItem::NoUnwindWhen => {
                record_spec_fn_no_proof_args(bctx, expr);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                let header = Arc::new(HeaderExprX::NoUnwindWhen(arg));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::Admit => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 0, expr.span, "expected admit", args);
                let f = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(false)),
                );
                mk_expr(ExprX::AssertAssume { is_assume: true, expr: f, msg: None })
            }
            SpecItem::Assume => {
                record_spec_fn_no_proof_args(bctx, expr);
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                mk_expr(ExprX::AssertAssume { is_assume: true, expr: arg, msg: None })
            }
        },
        VerusItem::Quant(quant_item) => {
            record_spec_fn_no_proof_args(bctx, expr);
            unsupported_err_unless!(args_len == 1, expr.span, "expected forall/exists", &args);
            let quant = match quant_item {
                QuantItem::Forall => air::ast::Quant::Forall,
                QuantItem::Exists => air::ast::Quant::Exists,
            };
            let quant = Quant { quant };
            extract_quant(bctx, expr.span, quant, args[0])
        }
        VerusItem::Directive(directive_item) => match directive_item {
            DirectiveItem::ExtraDependency => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(
                    args_len == 1,
                    expr.span,
                    "expected hide / extra dependency",
                    &args
                );
                let x = get_fn_path(bctx, &args[0])?;
                let header = Arc::new(HeaderExprX::ExtraDependency(x));
                mk_expr(ExprX::Header(header))
            }
            DirectiveItem::RevealHide => {
                // {
                //     ::verus_builtin::reveal_({
                //             #[verus::internal(reveal_fn)]
                //             fn __VERUS_REVEAL_INTERNAL__() {
                //                 ::verus_builtin::reveal_internal_path_(function::path)
                //             }
                //             ;
                //             __VERUS_REVEAL_INTERNAL__
                //         }, 1);
                // }

                record_spec_fn_no_proof_args(bctx, expr);
                let RevealHideResult::Expr(expr) = crate::reveal_hide::handle_reveal_hide(
                    &bctx.ctxt,
                    expr,
                    args_len,
                    args,
                    tcx,
                    Some(mk_expr),
                )?
                else {
                    panic!("handle_reveal_hide must return an Expr");
                };
                Ok(expr)
            }
            DirectiveItem::RevealHideInternalPath => {
                err_span(expr.span, "reveal_internal_path is only for internal verus use")
            }
            DirectiveItem::RevealStrlit => {
                record_spec_fn_no_proof_args(bctx, expr);
                if let Some(s) = if let ExprKind::Lit(lit0) = &args[0].kind {
                    if let rustc_ast::LitKind::Str(s, _) = lit0.node { Some(s) } else { None }
                } else {
                    None
                } {
                    mk_expr(ExprX::RevealString(Arc::new(s.to_string())))
                } else {
                    err_span(args[0].span, "string literal expected".to_string())
                }
            }
            DirectiveItem::InlineAirStmt => {
                if bctx.ctxt.cmd_line_args.allow_inline_air {
                    record_spec_fn_no_proof_args(bctx, expr);
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected air statement",
                        &args
                    );
                    let s = get_string_lit_arg(&args[0], &f_name)?;
                    mk_expr(ExprX::AirStmt(Arc::new(s)))
                } else {
                    err_span(
                        expr.span,
                        "inline AIR is only allowed with the relevant command line flag"
                            .to_string(),
                    )
                }
            }
        },
        VerusItem::Expr(expr_item) => match expr_item {
            ExprItem::Choose => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected choose", &args);
                extract_choose(bctx, expr.span, args[0], false, expr_typ()?)
            }
            ExprItem::ChooseTuple => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected choose", &args);
                extract_choose(bctx, expr.span, args[0], true, expr_typ()?)
            }
            ExprItem::Old => {
                record_spec_fn_no_proof_args(bctx, expr);
                if let ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: Res::Local(id), .. },
                )) = &args[0].kind
                {
                    if let Node::Pat(pat) = tcx.hir_node(*id) {
                        let typ = typ_of_node_expect_mut_ref(bctx, args[0].span, &expr.hir_id)?;
                        return Ok(bctx.spanned_typed_new(
                            expr.span,
                            &typ,
                            ExprX::VarAt(pat_to_var(pat)?, VarAt::Pre),
                        ));
                    }
                }
                err_span(expr.span, "only a variable binding is allowed as the argument to old")
            }
            ExprItem::ArrayIndex => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) if args.len() == 2 => {
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR).expect(
                            "invalid parameter for verus_builtin::array_index at arg0, arg0 must be self",
                        );
                        let arg1 = &args[1];
                        let arg1 = expr_to_vir_consume(bctx, arg1, ExprModifier::REGULAR)
                            .expect("invalid parameter for verus_builtin::array_index at arg1; arg1 must be an integer");
                        mk_expr(ExprX::Binary(
                            BinaryOp::Index(ArrayKind::Array, BoundsCheck::Allow),
                            arg0,
                            arg1,
                        ))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::array_index with two argument but did not receive it"
                    ),
                }
            }
            ExprItem::F32ToBits => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::FloatToBits, arg0))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::f32_to_bits with one argument but did not receive it"
                    ),
                }
            }
            ExprItem::F64ToBits => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::FloatToBits, arg0))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::f64_to_bits with one argument but did not receive it"
                    ),
                }
            }
            ExprItem::StrSliceLen => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrLen, arg0))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::strslice_len with one argument but did not receive it"
                    ),
                }
            }
            ExprItem::StrSliceGetChar => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) if args.len() == 2 => {
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR).expect(
                            "invalid parameter for verus_builtin::strslice_get_char at arg0, arg0 must be self",
                        );
                        let arg1 = &args[1];
                        let arg1 = expr_to_vir_consume(bctx, arg1, ExprModifier::REGULAR)
                            .expect("invalid parameter for verus_builtin::strslice_get_char at arg1, arg1 must be an integer");
                        mk_expr(ExprX::Binary(BinaryOp::StrGetChar, arg0, arg1))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::strslice_get_char with two argument but did not receive it"
                    ),
                }
            }
            ExprItem::StrSliceIsAscii => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir_consume(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrIsAscii, arg0))
                    }
                    _ => panic!(
                        "Expected a call for verus_builtin::strslice_is_ascii with one argument but did not receive it"
                    ),
                }
            }
            ExprItem::ArchWordBits => {
                record_spec_fn_no_proof_args(bctx, expr);
                assert!(args.len() == 0);
                let arg = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Int(IntRange::Int)),
                    ExprX::Const(vir::ast_util::const_int_from_u128(0)),
                );

                let kind = IntegerTypeBoundKind::ArchWordBits;

                mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg))
            }
            ExprItem::ClosureToFnSpec | ExprItem::ClosureToFnProof => {
                unsupported_err_unless!(args_len == 1, expr.span, "expected closure_to_fn", &args);
                if !bctx.in_ghost {
                    if matches!(expr_item, ExprItem::ClosureToFnSpec) {
                        return err_span(args[0].span, "cannot use spec_fn closure in 'exec' mode");
                    } else {
                        return err_span(
                            args[0].span,
                            "cannot use proof_fn closure in 'exec' mode",
                        );
                    }
                }
                if let ExprKind::Closure(..) = &args[0].kind {
                    let is_spec_fn = matches!(expr_item, ExprItem::ClosureToFnSpec);

                    let proof_fn_modes = if matches!(expr_item, ExprItem::ClosureToFnProof) {
                        let ty = bctx.types.node_type(expr.hir_id);
                        if let Some((arg_modes, ret_mode)) =
                            crate::rust_to_vir_base::try_get_proof_fn_modes(
                                &bctx.ctxt, expr.span, &ty,
                            )?
                        {
                            let op = CompilableOperator::ClosureToFnProof(ret_mode);
                            record_call(bctx, expr, ResolvedCall::CompilableOperator(op));
                            Some((Arc::new(arg_modes), ret_mode))
                        } else {
                            panic!("unexpected closure_to_proof_fn type")
                        }
                    } else {
                        record_spec_fn_no_proof_args(bctx, expr);
                        None
                    };
                    closure_to_vir(
                        bctx,
                        &args[0],
                        expr_typ()?,
                        is_spec_fn,
                        proof_fn_modes,
                        ExprModifier::REGULAR,
                    )
                } else {
                    err_span(args[0].span, "the argument to `closure_to_fn` must be a closure")
                }
            }
            ExprItem::SignedMin | ExprItem::SignedMax | ExprItem::UnsignedMax => {
                record_spec_fn_no_proof_args(bctx, expr);
                assert!(args.len() == 1);
                let arg = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                let kind = match expr_item {
                    ExprItem::SignedMin => IntegerTypeBoundKind::SignedMin,
                    ExprItem::SignedMax => IntegerTypeBoundKind::SignedMax,
                    ExprItem::UnsignedMax => IntegerTypeBoundKind::UnsignedMax,
                    _ => unreachable!(),
                };
                mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg))
            }
            ExprItem::IsSmallerThan
            | ExprItem::IsSmallerThanLexicographic
            | ExprItem::IsSmallerThanRecursiveFunctionField => {
                record_spec_fn_no_proof_args(bctx, expr);
                assert!(args.len() == 2);
                let (args0, args1) = if expr_item == &ExprItem::IsSmallerThanLexicographic {
                    match (&args[0].kind, &args[1].kind) {
                        (ExprKind::Tup(_), ExprKind::Tup(_)) => {
                            (extract_tuple(args[0]), extract_tuple(args[1]))
                        }
                        _ => unsupported_err!(
                            expr.span,
                            "is_smaller_than_lexicographic requires tuple arguments"
                        ),
                    }
                } else {
                    (vec![args[0]], vec![args[1]])
                };
                mk_is_smaller_than(
                    bctx,
                    expr.span,
                    args0,
                    args1,
                    expr_item == &ExprItem::IsSmallerThanRecursiveFunctionField,
                )
            }
            ExprItem::DefaultEnsures => {
                return err_span(expr.span, "default_ensures not allowed here");
            }
            ExprItem::InferSpecForLoopIter => {
                record_spec_fn_no_proof_args(bctx, expr);
                assert!(args.len() == 3);
                let arg = if bctx.loop_isolation {
                    expr_to_vir_consume(bctx, &args[1], ExprModifier::REGULAR)?
                } else {
                    expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?
                };
                let print_hint = matches!(
                    &args[2],
                    Expr { kind: ExprKind::Lit(Spanned { node: LitKind::Bool(true), .. }), .. }
                );
                mk_expr(ExprX::Unary(UnaryOp::InferSpecForLoopIter { print_hint }, arg))
            }
            ExprItem::IsVariant => {
                record_spec_fn_allow_proof_args(bctx, expr);
                assert!(args.len() == 2);
                let adt_arg = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                let variant_name = get_string_lit_arg(&args[1], &f_name)?;

                let (adt_path, _) =
                    check_variant_field(bctx, expr.span, args[0], &variant_name, None)?;

                mk_expr(ExprX::UnaryOpr(
                    UnaryOpr::IsVariant { datatype: adt_path, variant: str_ident(&variant_name) },
                    adt_arg,
                ))
            }
            ExprItem::GetVariantField => {
                record_spec_fn_allow_proof_args(bctx, expr);
                assert!(args.len() == 3);
                let adt_arg = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                let variant_name = get_string_lit_arg(&args[1], &f_name)?;
                let field_name = get_string_lit_arg(&args[2], &f_name)?;

                let (adt_path, variant_field) = check_variant_field(
                    bctx,
                    expr.span,
                    args[0],
                    &variant_name,
                    Some((field_name, &bctx.types.expr_ty(expr))),
                )?;

                mk_expr(ExprX::UnaryOpr(
                    UnaryOpr::Field(FieldOpr {
                        datatype: adt_path,
                        variant: str_ident(&variant_name),
                        field: variant_field.unwrap(),
                        get_variant: true,
                        check: VariantCheck::None,
                    }),
                    adt_arg,
                ))
            }
            ExprItem::GetUnionField => {
                record_spec_fn_allow_proof_args(bctx, expr);
                assert!(args.len() == 2);
                let adt_arg = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                let field_name = get_string_lit_arg(&args[1], &f_name)?;

                let adt_path = check_union_field(
                    bctx,
                    expr.span,
                    args[0],
                    &field_name,
                    &bctx.types.expr_ty(expr),
                )?;

                let field_ident = str_ident(&field_name);
                mk_expr(ExprX::UnaryOpr(
                    UnaryOpr::Field(FieldOpr {
                        datatype: adt_path,
                        variant: field_ident.clone(),
                        field: field_ident_from_rust(&field_ident),
                        get_variant: true,
                        check: VariantCheck::None,
                    }),
                    adt_arg,
                ))
            }
        },
        VerusItem::CompilableOpr(
            compilable_opr @ (CompilableOprItem::GhostExec | CompilableOprItem::TrackedExec),
        ) => {
            record_compilable_operator(
                bctx,
                expr,
                match compilable_opr {
                    CompilableOprItem::GhostExec => CompilableOperator::GhostExec,
                    CompilableOprItem::TrackedExec => CompilableOperator::TrackedExec,
                    _ => unreachable!(),
                },
            );

            unsupported_err_unless!(args_len == 1, expr.span, "expected Ghost/Tracked", &args);
            let arg = &args[0];
            if get_ghost_block_opt(bctx.ctxt.tcx.hir_attrs(expr.hir_id))
                == Some(GhostBlockAttr::Wrapper)
            {
                let bctx = &BodyCtxt { in_ghost: true, ..bctx.clone() };
                let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
                let vir_arg = vir_args[0].clone();
                match (compilable_opr, get_ghost_block_opt(bctx.ctxt.tcx.hir_attrs(arg.hir_id))) {
                    (CompilableOprItem::GhostExec, Some(GhostBlockAttr::GhostWrapped)) => {
                        let exprx = ExprX::Ghost {
                            alloc_wrapper: true,
                            tracked: false,
                            expr: vir_arg.clone(),
                        };
                        Ok(bctx.spanned_typed_new(arg.span, &vir_arg.typ.clone(), exprx))
                    }
                    (CompilableOprItem::TrackedExec, Some(GhostBlockAttr::TrackedWrapped)) => {
                        let exprx = ExprX::Ghost {
                            alloc_wrapper: true,
                            tracked: true,
                            expr: vir_arg.clone(),
                        };
                        Ok(bctx.spanned_typed_new(arg.span, &vir_arg.typ.clone(), exprx))
                    }
                    (_, attr) => {
                        err_span(expr.span, format!("unexpected ghost block attribute {:?}", attr))
                    }
                }
            } else {
                let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
                let vir_arg = vir_args[0].clone();
                if matches!(verus_item, VerusItem::CompilableOpr(CompilableOprItem::GhostExec)) {
                    let op = UnaryOp::CoerceMode {
                        op_mode: Mode::Exec,
                        from_mode: Mode::Spec,
                        to_mode: Mode::Exec,
                        kind: ModeCoercion::Other,
                    };
                    mk_expr(ExprX::Unary(op, vir_arg))
                } else {
                    // TrackedExec
                    let op = UnaryOp::CoerceMode {
                        op_mode: Mode::Exec,
                        from_mode: Mode::Proof,
                        to_mode: Mode::Exec,
                        kind: ModeCoercion::Other,
                    };
                    mk_expr(ExprX::Unary(op, vir_arg))
                }
            }
        }
        VerusItem::Assert(assert_item) => {
            record_spec_fn_no_proof_args(bctx, expr);
            match assert_item {
                AssertItem::Assert => {
                    unsupported_err_unless!(args_len == 1, expr.span, "expected assert", &args);
                    let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertAssume { is_assume: false, expr: exp, msg: None })
                }
                AssertItem::AssertBy => {
                    unsupported_err_unless!(args_len == 2, expr.span, "expected assert_by", &args);
                    let vars = Arc::new(vec![]);
                    let require = bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Bool),
                        ExprX::Const(Constant::Bool(true)),
                    );
                    let ensure = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    let proof = expr_to_vir_consume(bctx, &args[1], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertBy { vars, require, ensure, proof })
                }
                AssertItem::AssertByCompute => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_by_compute",
                        &args
                    );
                    let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertCompute(exp, ComputeMode::Z3))
                }
                AssertItem::AssertByComputeOnly => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_by_compute_only",
                        &args
                    );
                    let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertCompute(exp, ComputeMode::ComputeOnly))
                }
                AssertItem::AssertNonlinearBy | AssertItem::AssertBitvectorBy => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_nonlinear_by/assert_bitvector_by with one argument",
                        &args
                    );
                    let mut vir_expr = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    use vir::headers::{HeaderAllow, HeaderAllows};
                    let header = vir::headers::read_header(
                        &mut vir_expr,
                        &HeaderAllows::Some(vec![HeaderAllow::Require, HeaderAllow::Ensure]),
                    )?;
                    let requires = if header.require.len() >= 1 {
                        header.require
                    } else {
                        Arc::new(vec![bctx.spanned_typed_new(
                            expr.span,
                            &Arc::new(TypX::Bool),
                            ExprX::Const(Constant::Bool(true)),
                        )])
                    };
                    if header.ensure.0.len() == 0 {
                        return err_span(
                            expr.span,
                            "assert_nonlinear_by/assert_bitvector_by must have at least one ensures",
                        );
                    }
                    assert!(header.ensure.1.len() == 0);
                    let ensures = header.ensure.0;
                    let proof = vir_expr;

                    let expr_attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
                    let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
                    if expr_vattrs.spinoff_prover {
                        return err_span(
                            expr.span,
                            "#[verifier::spinoff_prover] is implied for assert by nonlinear_arith and assert by bit_vector",
                        );
                    }
                    mk_expr(ExprX::AssertQuery {
                        requires,
                        ensures,
                        proof,
                        mode: match assert_item {
                            AssertItem::AssertNonlinearBy => AssertQueryMode::NonLinear,
                            AssertItem::AssertBitvectorBy => AssertQueryMode::BitVector,
                            _ => unreachable!(),
                        },
                    })
                }
                AssertItem::AssertForallBy => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_forall_by",
                        &args
                    );
                    extract_assert_forall_by(bctx, expr.span, args[0])
                }
                // internally translate this into `assert_bitvector_by`. REVIEW: consider deprecating this at all
                AssertItem::AssertBitVector => {
                    let vir_expr = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
                    let requires = Arc::new(vec![bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Bool),
                        ExprX::Const(Constant::Bool(true)),
                    )]);
                    let ensures = Arc::new(vec![vir_expr]);
                    let proof = bctx.spanned_typed_new(
                        expr.span,
                        &unit_typ(),
                        ExprX::Block(Arc::new(vec![]), None),
                    );
                    mk_expr(ExprX::AssertQuery {
                        requires,
                        ensures,
                        proof,
                        mode: AssertQueryMode::BitVector,
                    })
                }
            }
        }
        VerusItem::UseTypeInvariant => {
            record_compilable_operator(bctx, expr, CompilableOperator::UseTypeInvariant);
            unsupported_err_unless!(args_len == 1, expr.span, "expected use_type_invariant", &args);
            if !bctx.in_ghost {
                return err_span(expr.span, "use_type_invariant must be in a 'proof' block");
            }
            let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;

            // We need to check there's no 'Ghost' decoration.
            let arg_typ = bctx.types.expr_ty_adjusted(&args[0]);
            let t = bctx.mid_ty_to_vir(expr.span, &arg_typ, false)?;
            vir::user_defined_type_invariants::check_typ_ok_for_use_typ_invariant(&exp.span, &t)?;

            // The correct fun is filled in later, in the pass that elaborates these conditions
            mk_expr(ExprX::AssertAssumeUserDefinedTypeInvariant {
                is_assume: true,
                expr: exp,
                fun: vir::fun!("" => "use_type_invariant_fake_placeholder_fun"),
            })
        }
        VerusItem::WithTriggers => {
            record_spec_fn_no_proof_args(bctx, expr);
            unsupported_err_unless!(args_len == 2, expr.span, "expected with_triggers", &args);
            let modifier = ExprModifier::REGULAR;
            let triggers_tuples = expr_to_vir_consume(bctx, args[0], modifier)?;
            let body = expr_to_vir_consume(bctx, args[1], modifier)?;
            let mut trigs: Vec<vir::ast::Exprs> = Vec::new();
            if let Some(triggers) = unpack_tuple(&triggers_tuples) {
                for trigger_tuple in triggers.iter() {
                    if let Some(terms) = unpack_tuple(trigger_tuple) {
                        trigs.push(Arc::new(terms));
                    } else {
                        return err_span(expr.span, "expected tuple arguments to with_triggers");
                    }
                }
            } else {
                return err_span(expr.span, "expected tuple arguments to with_triggers");
            }
            let triggers = Arc::new(trigs);
            mk_expr(ExprX::WithTriggers { triggers, body })
        }
        VerusItem::UnaryOp(UnaryOpItem::SpecCastReal) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            unsupported_err_unless!(args.len() == 1, expr.span, "expected 1 argument", &args);
            let source_vir0 = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
            let source_vir = source_vir0.consume(bctx, bctx.types.expr_ty_adjusted(&args[0]));
            let source_ty = undecorate_typ(&source_vir.typ);
            match &*source_ty {
                TypX::Int(_) => mk_expr(ExprX::Unary(UnaryOp::IntToReal, source_vir)),
                _ => err_span(expr.span, "Only integer types can be cast to real"),
            }
        }
        VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            let to_ty = undecorate_typ(&expr_typ()?);

            unsupported_err_unless!(args.len() == 1, expr.span, "expected 1 argument", &args);
            let source_vir0 = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
            let source_vir = source_vir0.consume(bctx, bctx.types.expr_ty_adjusted(&args[0]));
            let source_ty = undecorate_typ(&source_vir.typ);

            if let Some(expr) =
                crate::rust_to_vir_expr::maybe_do_ptr_cast(bctx, expr, &args[0], &source_vir)?
            {
                return Ok(expr);
            }

            let source_is_integer = {
                let integer_trait_def_id = bctx.ctxt.verus_items.name_to_id
                    [&VerusItem::BuiltinTrait(verus_items::BuiltinTraitItem::Integer)];
                let ty = bctx.types.node_type(args[0].hir_id);
                let infcx = rustc_infer::infer::TyCtxtInferExt::infer_ctxt(tcx)
                    .build(rustc_type_ir::TypingMode::PostAnalysis);
                matches!(&*source_vir.typ, TypX::TypParam(_))
                    && infcx
                        .type_implements_trait(
                            integer_trait_def_id,
                            vec![ty],
                            tcx.param_env(bctx.fun_id),
                        )
                        .must_apply_modulo_regions()
            };
            match ((&*source_ty, source_is_integer), &*to_ty) {
                ((TypX::Int(IntRange::U(_)), _), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                ((TypX::Int(IntRange::USize), _), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                ((TypX::Int(IntRange::Nat), _), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                ((TypX::Int(IntRange::Int), _), TypX::Int(IntRange::Nat)) => {
                    Ok(mk_ty_clip(&to_ty, &source_vir, true))
                }
                ((TypX::Int(_), _), TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
                    let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
                    Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate))
                }
                ((TypX::Bool, _), TypX::Int(_)) => {
                    let zero = mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(0)))?;
                    let one = mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(1)))?;
                    mk_expr(ExprX::If(source_vir, one, Some(zero)))
                }
                ((_, true), TypX::Int(IntRange::Int)) => {
                    mk_expr(ExprX::Unary(UnaryOp::CastToInteger, source_vir))
                }
                ((_, true), TypX::Int(IntRange::Nat)) => {
                    let cast_to_integer =
                        mk_expr(ExprX::Unary(UnaryOp::CastToInteger, source_vir))?;
                    let expr_attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
                    let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
                    Ok(mk_ty_clip(&to_ty, &cast_to_integer, expr_vattrs.truncate))
                }
                ((_, false), TypX::Int(_)) if bctx.types.node_type(args[0].hir_id).is_enum() => {
                    let cast_to = crate::rust_to_vir_expr::expr_cast_enum_int_to_vir(
                        bctx,
                        args[0],
                        source_vir0.to_place(),
                        mk_expr,
                    )?;
                    let expr_attrs = bctx.ctxt.tcx.hir_attrs(expr.hir_id);
                    let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
                    Ok(mk_ty_clip(&to_ty, &cast_to, expr_vattrs.truncate))
                }
                _ => err_span(
                    expr.span,
                    "Verus currently only supports casts from integer types, bool, enum (unit-only or field-less), `char`, and pointer types to integer types",
                ),
            }
        }
        VerusItem::UnaryOp(UnaryOpItem::SpecNeg) => {
            record_spec_fn_allow_proof_args(bctx, expr);

            match *undecorate_typ(&typ_of_node(bctx, args[0].span, &args[0].hir_id, false)?) {
                TypX::Int(_) => {}
                _ => {
                    return err_span(expr.span, "spec_neg expected int type");
                }
            }

            let varg = mk_one_vir_arg(bctx, expr.span, &args)?;
            let zero_const = vir::ast_util::const_int_from_u128(0);
            let zero = mk_expr(ExprX::Const(zero_const))?;
            mk_expr(ExprX::Binary(
                BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow)),
                zero,
                varg,
            ))
        }
        VerusItem::Chained(chained_item) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            let vir_args = mk_vir_args_auto_skip_mut_refs(bctx, node_substs, f, &args)?;
            match chained_item {
                ChainedItem::Value => {
                    unsupported_err_unless!(args_len == 1, expr.span, "spec_chained_value", &args);
                    unsupported_err_unless!(
                        matches!(*undecorate_typ(&vir_args[0].typ), TypX::Int(_)),
                        expr.span,
                        "chained inequalities for non-integer types",
                        &args
                    );
                    let exprx = ExprX::Multi(
                        MultiOp::Chained(Arc::new(vec![])),
                        Arc::new(vec![vir_args[0].clone()]),
                    );
                    Ok(bctx.spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
                }
                ChainedItem::Cmp => {
                    unsupported_err_unless!(args_len == 1, expr.span, "spec_chained_cmp", args);
                    Ok(vir_args[0].clone())
                }
                ChainedItem::Le
                | ChainedItem::Lt
                | ChainedItem::Ge
                | ChainedItem::Gt
                | ChainedItem::Eq => {
                    unsupported_err_unless!(args_len == 2, expr.span, "chained inequality", &args);
                    unsupported_err_unless!(
                        matches!(&vir_args[0].x, ExprX::Multi(MultiOp::Chained(_), _)),
                        expr.span,
                        "chained inequalities for non-integer types",
                        &args
                    );
                    unsupported_err_unless!(
                        matches!(*undecorate_typ(&vir_args[1].typ), TypX::Int(_)),
                        expr.span,
                        "chained inequalities for non-integer types",
                        &args
                    );
                    let op = match chained_item {
                        ChainedItem::Le => ChainedOp::Inequality(InequalityOp::Le),
                        ChainedItem::Lt => ChainedOp::Inequality(InequalityOp::Lt),
                        ChainedItem::Ge => ChainedOp::Inequality(InequalityOp::Ge),
                        ChainedItem::Gt => ChainedOp::Inequality(InequalityOp::Gt),
                        ChainedItem::Eq => ChainedOp::MultiEq,
                        ChainedItem::Value | ChainedItem::Cmp => unreachable!(),
                    };
                    if let ExprX::Multi(MultiOp::Chained(ops), es) = &vir_args[0].x {
                        let mut ops = (**ops).clone();
                        let mut es = (**es).clone();
                        ops.push(op);
                        es.push(vir_args[1].clone());
                        let exprx = ExprX::Multi(MultiOp::Chained(Arc::new(ops)), Arc::new(es));
                        Ok(bctx.spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
                    } else {
                        panic!("is_chained_ineq")
                    }
                }
            }
        }
        VerusItem::CompilableOpr(CompilableOprItem::GhostNew)
        | VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
            SpecGhostTrackedItem::GhostView
            | SpecGhostTrackedItem::GhostBorrow
            | SpecGhostTrackedItem::TrackedView,
        )) => {
            if matches!(verus_item, VerusItem::CompilableOpr(CompilableOprItem::GhostNew)) {
                record_compilable_operator(bctx, expr, CompilableOperator::GhostExec);
            } else {
                record_spec_fn_no_proof_args(bctx, expr);
            }

            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
            assert!(vir_args.len() == 1);
            let is_ghost_new = verus_item == &VerusItem::CompilableOpr(CompilableOprItem::GhostNew);
            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Spec,
                from_mode: Mode::Spec,
                to_mode: if is_ghost_new { Mode::Proof } else { Mode::Spec },
                kind: ModeCoercion::Other,
            };
            mk_expr(ExprX::Unary(op, vir_args[0].clone()))
        }
        VerusItem::CompilableOpr(CompilableOprItem::TrackedNew) => {
            record_compilable_operator(bctx, expr, CompilableOperator::TrackedNew);
            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
            assert!(vir_args.len() == 1);
            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Proof,
                from_mode: Mode::Proof,
                to_mode: Mode::Proof,
                kind: ModeCoercion::Other,
            };
            mk_expr(ExprX::Unary(op, vir_args[0].clone()))
        }
        VerusItem::CompilableOpr(CompilableOprItem::TrackedExecBorrow) => {
            record_compilable_operator(bctx, expr, CompilableOperator::TrackedExecBorrow);
            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
            assert!(vir_args.len() == 1);
            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Exec,
                from_mode: Mode::Proof,
                to_mode: Mode::Exec,
                kind: ModeCoercion::Other,
            };
            mk_expr(ExprX::Unary(op, vir_args[0].clone()))
        }
        VerusItem::CompilableOpr(
            opr @ (CompilableOprItem::TrackedGet | CompilableOprItem::TrackedBorrow),
        ) => {
            record_compilable_operator(
                bctx,
                expr,
                match opr {
                    CompilableOprItem::TrackedGet => CompilableOperator::TrackedGet,
                    CompilableOprItem::TrackedBorrow => CompilableOperator::TrackedBorrow,
                    _ => unreachable!(),
                },
            );

            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
            assert!(vir_args.len() == 1);
            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Proof,
                from_mode: Mode::Proof,
                to_mode: Mode::Proof,
                kind: ModeCoercion::Other,
            };
            mk_expr(ExprX::Unary(op, vir_args[0].clone()))
        }

        VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut))
        | VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut)
            if bctx.new_mut_ref =>
        {
            let tracked_mode =
                matches!(verus_item, VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut));

            if tracked_mode {
                record_compilable_operator(bctx, expr, CompilableOperator::TrackedBorrowMut);
            } else {
                record_spec_fn_no_proof_args(bctx, expr);
            }
            let mwm = if tracked_mode { ModeWrapperMode::Proof } else { ModeWrapperMode::Spec };

            assert!(args.len() == 1);

            let vir_arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?.to_place();

            // x.borrow_mut() takes &mut Tracked<T> and returns &mut T
            // so this is equivalent to `&mut (*x).unwrap`
            // where `unwrap` is the ModeUnwrap projection.
            // (i.e., the projection that maps a Tracked<T> to the Ghost<T> to the place
            // "inside" the Tracked or Ghost)
            // The ModeUnwrap projection can't exist on its own in Verus source,
            // though the &mut and * will often cancel out with adjacent code.
            // So we may end up with a nested Place expression where the ModeUnwrap projection
            // is in the middle.
            //
            // Note: (at this time) the outer &mut HAS to cancel out with something,
            // or else we will error later on account of trying to take a mut borrow
            // on a non-exec-mode place. So writing this is ok:
            //    *x.borrow_mut() = foo
            // but this is not:
            //    let y = x.borrow_mut()

            let p = crate::rust_to_vir_expr::deref_mut_allow_cancelling_two_phase(
                bctx, expr.span, &vir_arg,
            );
            let typ = match &*p.typ {
                TypX::Decorate(TypDecoration::Ghost | TypDecoration::Tracked, None, t) => t.clone(),
                _ => p.typ.clone(),
            };
            let p = bctx.spanned_typed_new(expr.span, &typ, PlaceX::ModeUnwrap(p, mwm));
            // This can't be two-phase since this is an opaque function call from
            // Rust's perspective.
            let e = crate::rust_to_vir_expr::borrow_mut_vir(
                bctx,
                expr.span,
                &p,
                rustc_middle::ty::adjustment::AllowTwoPhase::No,
            );

            Ok(e)
        }

        VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut)) => {
            record_spec_fn_no_proof_args(bctx, expr);

            assert!(args.len() == 1);
            let modif = is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(&args[0]), outer_modifier)?;
            let vir_arg = expr_to_vir_consume(bctx, &args[0], modif)?;

            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Proof,
                from_mode: Mode::Proof,
                to_mode: Mode::Spec,
                kind: ModeCoercion::BorrowMut,
            };
            let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
            Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_arg)))
        }
        VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut) => {
            record_compilable_operator(bctx, expr, CompilableOperator::TrackedBorrowMut);

            assert!(args.len() == 1);
            let modif = is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(&args[0]), outer_modifier)?;
            let vir_arg = expr_to_vir_consume(bctx, &args[0], modif)?;

            let op = UnaryOp::CoerceMode {
                op_mode: Mode::Proof,
                from_mode: Mode::Proof,
                to_mode: Mode::Proof,
                kind: ModeCoercion::BorrowMut,
            };
            let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
            Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_arg)))
        }
        VerusItem::BinaryOp(BinaryOpItem::Equality(equ_item)) => {
            record_spec_fn_allow_proof_args(bctx, expr);

            if matches!(equ_item, EqualityItem::SpecEq) {
                let t1 = typ_of_node(bctx, args[0].span, &args[0].hir_id, true)?;
                let t2 = typ_of_node(bctx, args[1].span, &args[1].hir_id, true)?;
                // REVIEW: there's some code that (harmlessly) uses == on types that are
                // different in decoration; Rust would reject this, but we currently allow it:
                let t1 = undecorate_typ(&t1);
                let t2 = undecorate_typ(&t2);
                if !(types_equal(&t1, &t2)
                    || is_smt_arith(
                        bctx,
                        args[0].span,
                        args[1].span,
                        &args[0].hir_id,
                        &args[1].hir_id,
                    )?)
                {
                    return Err(vir_err_span_str(expr.span, "mismatched types; types must be compatible to use == or !=")
                        .secondary_label(&crate::spans::err_air_span(args[0].span), format!("this is `{}`", typ_to_diagnostic_str(&t1)))
                        .secondary_label(&crate::spans::err_air_span(args[1].span), format!("this is `{}`", typ_to_diagnostic_str(&t2)))
                        .help("decorations (like &,Ghost,Tracked,Box,Rc,...) are transparent for == or != in spec code"));
                }
            }

            if !bctx.ctxt.cmd_line_args.new_mut_ref {
                let check = &|ty: rustc_middle::ty::Ty, span| match ty.kind() {
                    TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => {
                        let mut diagnostics = bctx.ctxt.diagnostics.borrow_mut();
                        diagnostics.push(vir::ast::VirErrAs::Warning(crate::util::err_span_bare(
                                span,
                                format!("Dereference this mutable reference to compare the value via Verus spec equality. In the future, this will be a hard error or not work as expected."),
                            )));
                    }
                    _ => {}
                };
                let ty = bctx.types.expr_ty_adjusted(&args[0]);
                check(ty, args[0].span);
                let ty = bctx.types.expr_ty_adjusted(&args[1]);
                check(ty, args[1].span);
            }

            let vir_args = mk_vir_args_auto_skip_mut_refs(bctx, node_substs, f, &args)?;
            let lhs = vir_args[0].clone();
            let rhs = vir_args[1].clone();

            if matches!(equ_item, EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep) {
                assert!(node_substs.len() == 1);
                let t = match node_substs[0].as_type() {
                    Some(ty) => bctx.mid_ty_to_vir(expr.span, &ty, false)?,
                    _ => panic!("unexpected ext_equal type argument"),
                };
                let vop = vir::ast::BinaryOpr::ExtEq(equ_item == &EqualityItem::ExtEqualDeep, t);
                mk_expr(ExprX::BinaryOpr(vop, lhs, rhs))
            } else {
                let vop = BinaryOp::Eq(Mode::Spec);
                mk_expr(ExprX::Binary(vop, lhs, rhs))
            }
        }
        VerusItem::CompilableOpr(CompilableOprItem::Implies) => {
            // REVIEW: should this really be a 'compilable operator'?
            // Imply is marked as unimplemented! in verus_builtin.
            record_compilable_operator(bctx, expr, CompilableOperator::Implies);

            let (lhs, rhs) = mk_two_vir_args(bctx, expr.span, &args)?;
            let vop = BinaryOp::Implies;
            mk_expr(ExprX::Binary(vop, lhs, rhs))
        }
        VerusItem::BinaryOp(
            BinaryOpItem::Arith(_)
            | BinaryOpItem::SpecArith(_)
            | BinaryOpItem::SpecBitwise(_)
            | BinaryOpItem::SpecOrd(_),
        ) => {
            record_spec_fn_allow_proof_args(bctx, expr);

            if !is_smt_arith(bctx, args[0].span, args[1].span, &args[0].hir_id, &args[1].hir_id)? {
                let t1 = bctx.types.expr_ty_adjusted(&args[0]);
                let t2 = bctx.types.expr_ty_adjusted(&args[1]);
                return err_span(
                    expr.span,
                    format!(
                        "types are not compatible with this operator (got {:?} and {:?})",
                        t1, t2
                    ),
                );
            }

            let (lhs, rhs) = mk_two_vir_args(bctx, expr.span, &args)?;

            let vop = match verus_item {
                VerusItem::BinaryOp(BinaryOpItem::SpecOrd(spec_ord_item)) => match spec_ord_item {
                    SpecOrdItem::Le => BinaryOp::Inequality(InequalityOp::Le),
                    SpecOrdItem::Ge => BinaryOp::Inequality(InequalityOp::Ge),
                    SpecOrdItem::Lt => BinaryOp::Inequality(InequalityOp::Lt),
                    SpecOrdItem::Gt => BinaryOp::Inequality(InequalityOp::Gt),
                },
                VerusItem::BinaryOp(BinaryOpItem::Arith(arith_item)) => {
                    let range = crate::rust_to_vir_base::get_range(&expr_typ()?);
                    let ob = if bctx.in_ghost {
                        OverflowBehavior::Truncate(range)
                    } else {
                        OverflowBehavior::Error(range)
                    };
                    match arith_item {
                        ArithItem::BuiltinAdd => BinaryOp::Arith(ArithOp::Add(ob)),
                        ArithItem::BuiltinSub => BinaryOp::Arith(ArithOp::Sub(ob)),
                        ArithItem::BuiltinMul => BinaryOp::Arith(ArithOp::Mul(ob)),
                    }
                }
                VerusItem::BinaryOp(BinaryOpItem::SpecArith(spec_arith_item))
                    if matches!(&*undecorate_typ(&expr_typ()?), TypX::Real) =>
                {
                    use vir::ast::RealArithOp;
                    match spec_arith_item {
                        SpecArithItem::Add => BinaryOp::RealArith(RealArithOp::Add),
                        SpecArithItem::Sub => BinaryOp::RealArith(RealArithOp::Sub),
                        SpecArithItem::Mul => BinaryOp::RealArith(RealArithOp::Mul),
                        SpecArithItem::EuclideanOrRealDiv => BinaryOp::RealArith(RealArithOp::Div),
                        SpecArithItem::EuclideanMod => {
                            unreachable!("spec mod operation cannot have type real")
                        }
                    }
                }
                VerusItem::BinaryOp(BinaryOpItem::SpecArith(spec_arith_item)) => {
                    let range = crate::rust_to_vir_base::get_range(&expr_typ()?);
                    match spec_arith_item {
                        SpecArithItem::Add => {
                            BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Truncate(range)))
                        }
                        SpecArithItem::Sub => {
                            BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Truncate(range)))
                        }
                        SpecArithItem::Mul => {
                            BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Truncate(range)))
                        }
                        SpecArithItem::EuclideanOrRealDiv => {
                            BinaryOp::Arith(ArithOp::EuclideanDiv(Div0Behavior::Allow))
                        }
                        SpecArithItem::EuclideanMod => {
                            BinaryOp::Arith(ArithOp::EuclideanMod(Div0Behavior::Allow))
                        }
                    }
                }
                VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(spec_bitwise)) => {
                    match spec_bitwise {
                        verus_items::SpecBitwiseItem::BitAnd => {
                            BinaryOp::Bitwise(BitwiseOp::BitAnd, BitshiftBehavior::Allow)
                        }
                        verus_items::SpecBitwiseItem::BitOr => {
                            BinaryOp::Bitwise(BitwiseOp::BitOr, BitshiftBehavior::Allow)
                        }
                        verus_items::SpecBitwiseItem::BitXor => {
                            if matches!(*lhs.typ, TypX::Bool) {
                                BinaryOp::Xor
                            } else {
                                BinaryOp::Bitwise(BitwiseOp::BitXor, BitshiftBehavior::Allow)
                            }
                        }
                        verus_items::SpecBitwiseItem::Shl => {
                            let (Some(w), s) = bitwidth_and_signedness_of_integer_type(
                                &bctx.ctxt.verus_items,
                                bctx.types.expr_ty(expr),
                            ) else {
                                return err_span(expr.span, "expected finite integer width");
                            };
                            BinaryOp::Bitwise(BitwiseOp::Shl(w, s), BitshiftBehavior::Allow)
                        }
                        verus_items::SpecBitwiseItem::Shr => {
                            let (Some(w), _s) = bitwidth_and_signedness_of_integer_type(
                                &bctx.ctxt.verus_items,
                                bctx.types.expr_ty(expr),
                            ) else {
                                return err_span(expr.span, "expected finite integer width");
                            };
                            BinaryOp::Bitwise(BitwiseOp::Shr(w), BitshiftBehavior::Allow)
                        }
                    }
                }
                _ => {
                    crate::internal_err!(expr.span, "unexpected verus item")
                }
            };

            mk_expr(ExprX::Binary(vop, lhs, rhs))
        }
        VerusItem::BuiltinFunction(
            re @ (BuiltinFunctionItem::CallRequires | BuiltinFunctionItem::CallEnsures),
        ) => {
            record_spec_fn_no_proof_args(bctx, expr);

            let bsf = match re {
                BuiltinFunctionItem::CallRequires => {
                    assert!(args.len() == 2);
                    BuiltinSpecFun::ClosureReq
                }
                BuiltinFunctionItem::CallEnsures => {
                    assert!(args.len() == 3);
                    BuiltinSpecFun::ClosureEns
                }
                BuiltinFunctionItem::ConstrainType => unreachable!(),
            };

            let vir_args = args
                .iter()
                .map(|arg| expr_to_vir_consume(bctx, &arg, ExprModifier::REGULAR))
                .collect::<Result<Vec<_>, _>>()?;

            let typ_args = mk_typ_args(bctx, node_substs, f, expr.span)?;
            let mut typ_args = (*typ_args).clone();
            // Put the args in the order [function type, args type]
            typ_args.swap(0, 1);
            let typ_args = Arc::new(typ_args);

            let impl_paths = get_impl_paths(bctx, f, node_substs, None);

            return mk_expr(ExprX::Call(
                CallTarget::BuiltinSpecFun(bsf, typ_args, impl_paths),
                Arc::new(vir_args),
                None,
            ));
        }
        VerusItem::ErasedGhostValue | VerusItem::DummyCapture(_) => {
            return err_span(
                expr.span,
                format!("this builtin item should not appear in user code",),
            );
        }
        item @ (VerusItem::HasResolved | VerusItem::HasResolvedUnsized) => {
            if !bctx.new_mut_ref
                && !matches!(bctx.ctxt.cmd_line_args.vstd, Vstd::IsVstd | Vstd::IsCore)
            {
                unsupported_err!(expr.span, "resolve/has_resolved without '-V new-mut-ref'", &args);
            }
            record_spec_fn_no_proof_args(bctx, expr);
            if !bctx.in_ghost {
                return err_span(expr.span, "has_resolved must be in a 'proof' block");
            }
            let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
            let arg_typ = bctx.types.expr_ty_adjusted(&args[0]);
            let arg_typ = match item {
                VerusItem::HasResolved => arg_typ,
                VerusItem::HasResolvedUnsized => match arg_typ.kind() {
                    TyKind::Ref(_, t, rustc_middle::ty::Mutability::Not) => *t,
                    _ => {
                        return err_span(expr.span, "has_resolved_unsized expects shared ref");
                    }
                },
                _ => unreachable!(),
            };
            let t = bctx.mid_ty_to_vir(expr.span, &arg_typ, false)?;
            mk_expr(ExprX::UnaryOpr(UnaryOpr::HasResolved(t), exp))
        }
        VerusItem::MutRefCurrent | VerusItem::MutRefFuture | VerusItem::Final => {
            if !bctx.new_mut_ref {
                unsupported_err!(expr.span, "mut_ref spec funs without '-V new-mut-ref'", &args);
            }
            record_spec_fn_no_proof_args(bctx, expr);
            if !bctx.in_ghost {
                return err_span(
                    expr.span,
                    "mut_ref_current/mut_ref_future must be in a 'proof' block",
                );
            }
            let exp = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
            let op = match verus_item {
                VerusItem::MutRefCurrent => UnaryOp::MutRefCurrent,
                VerusItem::MutRefFuture => {
                    UnaryOp::MutRefFuture(vir::ast::MutRefFutureSourceName::MutRefFuture)
                }
                VerusItem::Final => UnaryOp::MutRefFinal,
                _ => unreachable!(),
            };
            mk_expr(ExprX::Unary(op, exp))
        }
        VerusItem::AfterBorrow => {
            if !bctx.new_mut_ref {
                unsupported_err!(expr.span, "mut_ref spec funs without '-V new-mut-ref'", &args);
            }
            record_spec_fn_no_proof_args(bctx, expr);
            if !bctx.in_ghost {
                return err_span(expr.span, "`after_borrow` must be in a 'proof' block");
            }
            let p = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?.to_place();
            if !is_place_ok_for_spec_after_borrow(&p) {
                return err_span(
                    expr.span,
                    "`after_borrow` expects a local variable, possibly with dereferences or field accesses",
                );
            }

            let rk = vir::ast::ReadKind::SpecAfterBorrow;
            let rk = vir::ast::UnfinalizedReadKind {
                preliminary_kind: rk,
                id: bctx.ctxt.unique_read_kind_id(),
            };
            mk_expr(ExprX::ReadPlace(p, rk))
        }
        VerusItem::Vstd(_, _)
        | VerusItem::Marker(_)
        | VerusItem::BuiltinType(_)
        | VerusItem::BuiltinTrait(_)
        | VerusItem::External(_)
        | VerusItem::Global(_)
        | VerusItem::BuiltinFunction(BuiltinFunctionItem::ConstrainType) => unreachable!(),
    }
}

fn is_place_ok_for_spec_after_borrow(place: &Place) -> bool {
    match &place.x {
        PlaceX::Local(_) => true,
        PlaceX::DerefMut(p) => is_place_ok_for_spec_after_borrow(p),
        PlaceX::Field(opr, p) => {
            matches!(opr.check, VariantCheck::None) && is_place_ok_for_spec_after_borrow(p)
        }
        PlaceX::Temporary(_) => false,
        PlaceX::ModeUnwrap(p, _) => is_place_ok_for_spec_after_borrow(p),
        PlaceX::WithExpr(..) => false,
        PlaceX::Index(..) => false,
    }
}

fn get_impl_paths<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    remove_self_trait_bound: Option<(DefId, &mut Option<vir::ast::ImplPath>)>,
) -> vir::ast::ImplPaths {
    if let rustc_middle::ty::FnDef(fid, _fsubsts) = bctx.ctxt.tcx.type_of(f).skip_binder().kind() {
        crate::rust_to_vir_base::get_impl_paths(
            bctx.ctxt.tcx,
            &bctx.ctxt.verus_items,
            bctx.fun_id,
            *fid,
            node_substs,
            remove_self_trait_bound,
        )
    } else {
        panic!("unexpected function {:?}", f)
    }
}

fn check_is_builtin_constrain_typ<'tcx>(bctx: &BodyCtxt<'tcx>, e: &'tcx Expr<'tcx>) -> bool {
    if let ExprKind::Call(fun, ..) = e.kind {
        if let ExprKind::Path(QPath::Resolved(_, path)) = fun.kind {
            if let Some(def_id) = path.res.opt_def_id() {
                if bctx.ctxt.get_verus_item(def_id)
                    == Some(&VerusItem::BuiltinFunction(BuiltinFunctionItem::ConstrainType))
                {
                    return false;
                }
            }
        }
    }
    true
}

fn extract_ensures<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<HeaderExpr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    use vir::ast::Exprs;
    let get_args = |body_value: &'tcx Expr<'tcx>| -> Result<(Exprs, Exprs), VirErr> {
        let args = vec_map_result(
            &extract_array(body_value)
                .iter()
                .filter(|e| check_is_builtin_constrain_typ(bctx, **e))
                .map(|x: &&_| (*x).clone())
                .collect(),
            |e| get_ensures_arg(bctx, e),
        )?;
        let args0 =
            args.iter().filter_map(|(b, e)| if !*b { Some(e.clone()) } else { None }).collect();
        let args1 =
            args.iter().filter_map(|(b, e)| if *b { Some(e.clone()) } else { None }).collect();
        Ok((Arc::new(args0), Arc::new(args1)))
    };
    match &expr.kind {
        ExprKind::Closure(closure) => {
            bctx.ctxt.push_body_erasure(
                closure.def_id,
                BodyErasure { erase_body: true, ret_spec: true },
            );

            let typs: Vec<Typ> = closure_param_typs(bctx, expr)?;
            let body = tcx.hir_body(closure.body);
            let mut xs: Vec<VarIdent> = Vec::new();
            for param in body.params.iter() {
                xs.push(pat_to_var(param.pat)?);
            }
            let expr = &body.value;
            let args = get_args(expr)?;
            if typs.len() == 0 && xs.len() == 1 {
                let id_typ = Some((xs[0].clone(), None));
                Ok(Arc::new(HeaderExprX::Ensures(id_typ, args)))
            } else if typs.len() == 1 && xs.len() == 1 {
                let id_typ = Some((xs[0].clone(), Some(typs[0].clone())));
                Ok(Arc::new(HeaderExprX::Ensures(id_typ, args)))
            } else if xs.len() == 0 {
                Ok(Arc::new(HeaderExprX::Ensures(None, args)))
            } else {
                err_span(expr.span, "expected at most 1 parameter in closure")
            }
        }
        _ => {
            let args = get_args(expr)?;
            Ok(Arc::new(HeaderExprX::Ensures(None, args)))
        }
    }
}

fn extract_quant<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    quant: Quant,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(closure) => {
            bctx.ctxt.push_body_erasure(
                closure.def_id,
                BodyErasure { erase_body: true, ret_spec: true },
            );

            let body = tcx.hir_body(closure.body);
            let typs = closure_param_typs(bctx, expr)?;
            assert!(typs.len() == body.params.len());
            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for (x, t) in body.params.iter().zip(typs) {
                binders.push(Arc::new(VarBinderX { name: pat_to_var(x.pat)?, a: t }));
            }
            let expr = &body.value;
            let mut vir_expr = expr_to_vir_consume(bctx, expr, ExprModifier::REGULAR)?;
            let _ = vir::headers::read_header(
                &mut vir_expr,
                &vir::headers::HeaderAllows::Some(vec![]),
            )?;
            let typ = Arc::new(TypX::Bool);
            if !matches!(bctx.types.expr_ty_adjusted(expr).kind(), TyKind::Bool) {
                return err_span(expr.span, "forall/ensures needs a bool expression");
            }
            Ok(bctx.spanned_typed_new(span, &typ, ExprX::Quant(quant, Arc::new(binders), vir_expr)))
        }
        _ => err_span(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn get_ensures_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    mut expr: &Expr<'tcx>,
) -> Result<(bool, vir::ast::Expr), VirErr> {
    if matches!(bctx.types.expr_ty_adjusted(expr).kind(), TyKind::Bool) {
        let mut default_ensures = false;
        if let ExprKind::Call(fun, args) = &expr.kind {
            if let ExprKind::Path(qpath) = &fun.kind {
                let def = bctx.types.qpath_res(&qpath, fun.hir_id);
                if let rustc_hir::def::Res::Def(_, def_id) = def {
                    let verus_item = bctx.ctxt.verus_items.id_to_name.get(&def_id);
                    if verus_item == Some(&VerusItem::Expr(ExprItem::DefaultEnsures)) {
                        assert!(args.len() == 1);
                        default_ensures = true;
                        expr = &args[0];
                    }
                }
            }
        }
        Ok((default_ensures, expr_to_vir_consume(bctx, expr, ExprModifier::REGULAR)?))
    } else {
        err_span(expr.span, "ensures needs a bool expression")
    }
}

fn extract_assert_forall_by<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(closure) => {
            bctx.ctxt.push_body_erasure(
                closure.def_id,
                BodyErasure { erase_body: true, ret_spec: true },
            );

            let body = tcx.hir_body(closure.body);
            let typs = closure_param_typs(bctx, expr)?;
            assert!(body.params.len() == typs.len());
            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for (x, t) in body.params.iter().zip(typs) {
                binders.push(Arc::new(VarBinderX { name: pat_to_var(x.pat)?, a: t }));
            }
            let expr = &body.value;
            let mut vir_expr = expr_to_vir_consume(bctx, expr, ExprModifier::REGULAR)?;
            use vir::headers::{HeaderAllow, HeaderAllows};
            let header = vir::headers::read_header(
                &mut vir_expr,
                &HeaderAllows::Some(vec![HeaderAllow::Require, HeaderAllow::Ensure]),
            )?;
            assert!(header.ensure.1.len() == 0);
            if header.require.len() > 1 {
                return err_span(expr.span, "assert_forall_by can have at most one requires");
            }
            if header.ensure.0.len() != 1 {
                return err_span(expr.span, "assert_forall_by must have exactly one ensures");
            }
            if header.ensure_id_typ.is_some() {
                return err_span(expr.span, "ensures clause must be a bool");
            }
            let typ = unit_typ();
            let vars = Arc::new(binders);
            let require = if header.require.len() == 1 {
                header.require[0].clone()
            } else {
                bctx.spanned_typed_new(
                    span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(true)),
                )
            };
            let ensure = header.ensure.0[0].clone();
            let forallx = ExprX::AssertBy { vars, require, ensure, proof: vir_expr };
            Ok(bctx.spanned_typed_new(span, &typ, forallx))
        }
        _ => err_span(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn extract_choose<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
    tuple: bool,
    expr_typ: Typ,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(closure) => {
            bctx.ctxt.push_body_erasure(
                closure.def_id,
                BodyErasure { erase_body: true, ret_spec: true },
            );

            let closure_body = tcx.hir_body(closure.body);
            let mut params: Vec<VarBinder<Typ>> = Vec::new();
            let mut vars: Vec<vir::ast::Expr> = Vec::new();
            let typs = closure_param_typs(bctx, expr)?;
            assert!(closure_body.params.len() == typs.len());
            for (x, typ) in closure_body.params.iter().zip(typs) {
                let name = pat_to_var(x.pat)?;
                let vir_expr = bctx.spanned_typed_new(x.span, &typ, ExprX::Var(name.clone()));
                let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                erasure_info.hir_vir_ids.push((x.pat.hir_id, vir_expr.span.id));
                vars.push(vir_expr);
                params.push(Arc::new(VarBinderX { name, a: typ }));
            }
            let typs = vec_map(&params, |p| p.a.clone());
            let cond_expr = &closure_body.value;
            let cond = expr_to_vir_consume(bctx, cond_expr, ExprModifier::REGULAR)?;
            let body = if tuple {
                let typ = mk_tuple_typ(&Arc::new(typs));
                if !vir::ast_util::types_equal(&typ, &expr_typ) {
                    return err_span(
                        expr.span,
                        format!(
                            "expected choose_tuple to have type {:?}, found type {:?}",
                            typ, expr_typ
                        ),
                    );
                }
                bctx.spanned_typed_new(span, &typ, mk_tuple_x(&Arc::new(vars)))
            } else {
                if params.len() != 1 {
                    return err_span(
                        expr.span,
                        "choose expects exactly one parameter (use choose_tuple for multiple parameters)",
                    );
                }
                vars[0].clone()
            };
            let params = Arc::new(params);
            Ok(bctx.spanned_typed_new(
                span,
                &body.clone().typ,
                ExprX::Choose { params, cond, body },
            ))
        }
        _ => {
            dbg!(&expr);
            err_span(expr.span, "argument to choose must be a closure")
        }
    }
}

/// If `expr` is of the form `closure_to_spec_fn(e)` then return `e`.
/// Otherwise, return `expr`.
///
/// This is needed because the syntax macro can often create expressions that look like:
/// forall(closure_to_fn_spec(|x| { ... }))

fn skip_closure_coercion<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    match &expr.kind {
        ExprKind::Call(fun, args_slice) => match &fun.kind {
            ExprKind::Path(qpath) => {
                let def = bctx.types.qpath_res(&qpath, fun.hir_id);
                match def {
                    rustc_hir::def::Res::Def(_, def_id) => {
                        let verus_item = bctx.ctxt.verus_items.id_to_name.get(&def_id);
                        if verus_item == Some(&VerusItem::Expr(ExprItem::ClosureToFnSpec)) {
                            return skip_closure_coercion(bctx, &args_slice[0]);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        },
        ExprKind::Block(
            Block {
                stmts,
                expr: Some(e),
                hir_id: _,
                rules: BlockCheckMode::DefaultBlock,
                span: _,
                targeted_by_break: false,
            },
            None,
        ) => {
            if stmts.len() == 1 {
                match &stmts[0].kind {
                    StmtKind::Let(rustc_hir::LetStmt { init: Some(init), .. }) => {
                        if crate::rust_to_vir_expr::is_ignorable_dummy_capture_operation(bctx, init)
                        {
                            return skip_closure_coercion(bctx, e);
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }

    expr
}

fn mk_is_smaller_than<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    args0: Vec<&'tcx Expr>,
    args1: Vec<&'tcx Expr>,
    recursive_function_field: bool,
) -> Result<vir::ast::Expr, VirErr> {
    // convert is_smaller_than((x0, y0, z0), (x1, y1, z1)) into
    // x0 < x1 || (x0 == x1 && (y0 < y1 || (y0 == y1 && z0 < z1)))
    // see also check_decrease in recursion.rs
    let tbool = Arc::new(TypX::Bool);
    let tint = Arc::new(TypX::Int(IntRange::Int));
    let when_equalx = ExprX::Const(Constant::Bool(args1.len() < args0.len()));
    let when_equal = bctx.spanned_typed_new(span, &tbool, when_equalx);
    let mut dec_exp: vir::ast::Expr = when_equal;
    for (i, (exp0, exp1)) in args0.iter().zip(args1.iter()).rev().enumerate() {
        let mk_bop = |op: BinaryOp, e1: vir::ast::Expr, e2: vir::ast::Expr| {
            bctx.spanned_typed_new(span, &tbool, ExprX::Binary(op, e1, e2))
        };
        let mk_cmp = |lt: bool| -> Result<vir::ast::Expr, VirErr> {
            let e0 = expr_to_vir_consume(bctx, exp0, ExprModifier::REGULAR)?;
            let e1 = expr_to_vir_consume(bctx, exp1, ExprModifier::REGULAR)?;
            if vir::recursion::height_is_int(&e0.typ) && vir::recursion::height_is_int(&e1.typ) {
                if lt {
                    // 0 <= x < y
                    let zerox = ExprX::Const(vir::ast_util::const_int_from_u128(0));
                    let zero = bctx.spanned_typed_new(span, &tint, zerox);
                    let op0 = BinaryOp::Inequality(InequalityOp::Le);
                    let cmp0 = mk_bop(op0, zero, e0);
                    let op1 = BinaryOp::Inequality(InequalityOp::Lt);
                    let e0 = expr_to_vir_consume(bctx, exp0, ExprModifier::REGULAR)?;
                    let cmp1 = mk_bop(op1, e0, e1);
                    Ok(mk_bop(BinaryOp::And, cmp0, cmp1))
                } else {
                    Ok(mk_bop(BinaryOp::Eq(Mode::Spec), e0, e1))
                }
            } else {
                let cmp = BinaryOp::HeightCompare { strictly_lt: lt, recursive_function_field };
                Ok(mk_bop(cmp, e0, e1))
            }
        };
        if i == 0 {
            // i == 0 means last shared exp0/exp1, which we visit first
            if args1.len() < args0.len() {
                // if z0 == z1, we can ignore the extra args0:
                // z0 < z1 || z0 == z1
                dec_exp = mk_bop(BinaryOp::Or, mk_cmp(true)?, mk_cmp(false)?);
            } else {
                // z0 < z1
                dec_exp = mk_cmp(true)?;
            }
        } else {
            // x0 < x1 || (x0 == x1 && dec_exp)
            let and = mk_bop(BinaryOp::And, mk_cmp(false)?, dec_exp);
            dec_exp = mk_bop(BinaryOp::Or, mk_cmp(true)?, and);
        }
    }
    return Ok(dec_exp);
}

pub(crate) fn fix_node_substs<'tcx, 'a>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    types: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    rust_item: Option<RustItem>,
    args: &'a [&'tcx Expr<'tcx>],
    expr: &'a Expr<'tcx>,
) -> &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>> {
    match rust_item {
        Some(RustItem::TryTraitBranch) => {
            // I don't understand why, but in this case, node_substs is empty instead
            // of having the type argument. Let's fix it here.
            // `branch` has type `fn branch(self) -> ...`
            // so we can get the Self argument from the first argument.
            let generic_arg = GenericArg::from(types.expr_ty_adjusted(&args[0]));
            tcx.mk_args(&[generic_arg])
        }
        Some(RustItem::ResidualTraitFromResidual) => {
            // `fn from_residual(residual: R) -> Self;`
            let generic_arg0 = GenericArg::from(types.expr_ty(expr));
            let generic_arg1 = GenericArg::from(types.expr_ty_adjusted(&args[0]));
            tcx.mk_args(&[generic_arg0, generic_arg1])
        }
        _ => node_substs,
    }
}

fn mk_typ_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    _f: DefId,
    span: Span,
) -> Result<vir::ast::Typs, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let mut typ_args: Vec<Typ> = Vec::new();
    for typ_arg in substs {
        match typ_arg.kind() {
            GenericArgKind::Type(ty) => {
                typ_args.push(bctx.mid_ty_to_vir(span, &ty, false)?);
            }
            GenericArgKind::Lifetime(_) => {}
            GenericArgKind::Const(cnst) => {
                typ_args.push(crate::rust_to_vir_base::mid_ty_const_to_vir(
                    tcx,
                    Some(span),
                    &cnst,
                )?);
            }
        }
    }
    Ok(Arc::new(typ_args))
}

fn mk_vir_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    node_substs: &rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    f: DefId,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<Vec<vir::ast::Expr>, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let raw_inputs = bctx.ctxt.tcx.fn_sig(f).instantiate(tcx, node_substs).skip_binder().inputs();
    assert!(raw_inputs.len() == args.len());
    args.iter()
        .zip(raw_inputs)
        .map(|(arg, raw_param)| {
            let is_mut_ref_param = !bctx.new_mut_ref
                && match raw_param.kind() {
                    TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => true,
                    _ => false,
                };
            if is_mut_ref_param {
                let expr =
                    expr_to_vir(bctx, arg, ExprModifier { deref_mut: true, addr_of_mut: true })?;
                let expr = crate::rust_to_vir_expr::place_to_loc(&expr.to_place())?;
                Ok(bctx.spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else {
                expr_to_vir_consume(
                    bctx,
                    arg,
                    is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(arg), ExprModifier::REGULAR)?,
                )
            }
        })
        .collect::<Result<Vec<_>, _>>()
}

fn mk_vir_args_auto_skip_mut_refs<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    node_substs: &rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    f: DefId,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<Vec<vir::ast::Expr>, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let raw_inputs = bctx.ctxt.tcx.fn_sig(f).instantiate(tcx, node_substs).skip_binder().inputs();
    assert!(raw_inputs.len() == args.len());
    args.iter()
        .zip(raw_inputs)
        .map(|(arg, raw_param)| {
            let is_mut_ref_param = !bctx.new_mut_ref
                && match raw_param.kind() {
                    TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => true,
                    _ => false,
                };
            let modifier = if is_mut_ref_param {
                ExprModifier { deref_mut: true, addr_of_mut: false }
            } else {
                ExprModifier::REGULAR
            };
            expr_to_vir_consume(
                bctx,
                arg,
                is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(arg), modifier)?,
            )
        })
        .collect::<Result<Vec<_>, _>>()
}

fn mk_one_vir_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<vir::ast::Expr, VirErr> {
    unsupported_err_unless!(args.len() == 1, span, "expected 1 argument", &args);
    expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)
}

fn mk_two_vir_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<(vir::ast::Expr, vir::ast::Expr), VirErr> {
    unsupported_err_unless!(args.len() == 2, span, "expected 2 arguments", &args);
    let e0 = expr_to_vir_consume(bctx, &args[0], ExprModifier::REGULAR)?;
    let e1 = expr_to_vir_consume(bctx, &args[1], ExprModifier::REGULAR)?;
    Ok((e0, e1))
}

fn get_string_lit_arg<'tcx>(
    arg: &'tcx Expr<'tcx>,
    fn_name_for_error_msg: &str,
) -> Result<String, VirErr> {
    match arg {
        Expr { kind: ExprKind::Lit(Spanned { node: LitKind::Str(s, _), .. }), .. } => {
            Ok(s.to_string())
        }
        _ => err_span(
            arg.span,
            format!("Verus verus_builtin `{fn_name_for_error_msg:}` requires a string literal"),
        ),
    }
}

pub(crate) fn check_variant_field<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    adt_arg: &'tcx Expr<'tcx>,
    variant_name: &String,
    field_name_typ: Option<(String, &rustc_middle::ty::Ty<'tcx>)>,
) -> Result<(vir::ast::Dt, Option<vir::ast::Ident>), VirErr> {
    let tcx = bctx.ctxt.tcx;

    let ty = bctx.types.expr_ty_adjusted(adt_arg);
    let ty = match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, t, rustc_ast::Mutability::Not) => t,
        _ => &ty,
    };
    let (adt, substs) = match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt, substs) => (adt, substs),
        _ => {
            return err_span(span, format!("expected type to be datatype"));
        }
    };

    let vir_adt_ty = bctx.mid_ty_to_vir(span, &ty, false)?;
    let adt_path = match &*vir_adt_ty {
        TypX::Datatype(path, _, _) => path.clone(),
        _ => {
            return err_span(span, format!("expected type to be datatype"));
        }
    };

    if adt.is_union() {
        if field_name_typ.is_some() {
            // Don't use get_variant_field with unions
            return err_span(
                span,
                format!("this datatype is a union; consider `get_union_field` instead"),
            );
        }
        let variant = adt.non_enum_variant();
        let field_opt = variant.fields.iter().find(|f| f.ident(tcx).as_str() == variant_name);
        if field_opt.is_none() {
            return err_span(span, format!("no field `{variant_name:}` for this union"));
        }

        return Ok((adt_path, None));
    }

    // Enum case:

    let variant_opt = adt.variants().iter().find(|v| v.ident(tcx).as_str() == variant_name);
    let Some(variant) = variant_opt else {
        return err_span(span, format!("no variant `{variant_name:}` for this datatype"));
    };

    match field_name_typ {
        None => Ok((adt_path, None)),
        Some((field_name, expected_field_typ)) => {
            // The 'get_variant_field' case
            let field_opt = variant.fields.iter().find(|f| f.ident(tcx).as_str() == field_name);
            let Some(field) = field_opt else {
                return err_span(span, format!("no field `{field_name:}` for this variant"));
            };

            let field_ty = field.ty(tcx, substs);
            let vir_field_ty = bctx.mid_ty_to_vir(span, &field_ty, false)?;
            let vir_expected_field_ty = bctx.mid_ty_to_vir(span, &expected_field_typ, false)?;
            if !types_equal(&vir_field_ty, &vir_expected_field_ty) {
                return err_span(span, "field has the wrong type");
            }

            let field_ident = field_ident_from_rust(&field_name);

            Ok((adt_path, Some(field_ident)))
        }
    }
}

fn check_union_field<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    adt_arg: &'tcx Expr<'tcx>,
    field_name: &String,
    expected_field_typ: &rustc_middle::ty::Ty<'tcx>,
) -> Result<vir::ast::Dt, VirErr> {
    let tcx = bctx.ctxt.tcx;

    let ty = bctx.types.expr_ty_adjusted(adt_arg);
    let ty = match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, t, rustc_ast::Mutability::Not) => t,
        _ => &ty,
    };
    let (adt, substs) = match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt, substs) => (adt, substs),
        _ => {
            return err_span(span, format!("expected type to be datatype"));
        }
    };

    if !adt.is_union() {
        return err_span(span, format!("get_union_field expects a union type"));
    }

    let variant = adt.non_enum_variant();

    let field_opt = variant.fields.iter().find(|f| f.ident(tcx).as_str() == field_name);
    let Some(field) = field_opt else {
        return err_span(span, format!("no field `{field_name:}` for this union"));
    };

    let field_ty = field.ty(tcx, substs);
    let vir_field_ty = bctx.mid_ty_to_vir(span, &field_ty, false)?;
    let vir_expected_field_ty = bctx.mid_ty_to_vir(span, &expected_field_typ, false)?;
    if !types_equal(&vir_field_ty, &vir_expected_field_ty) {
        return err_span(span, "field has the wrong type");
    }

    let vir_adt_ty = bctx.mid_ty_to_vir(span, &ty, false)?;
    let adt_path = match &*vir_adt_ty {
        TypX::Datatype(path, _, _) => path.clone(),
        _ => {
            return err_span(span, format!("expected type to be datatype"));
        }
    };

    Ok(adt_path)
}

fn record_compilable_operator<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr, op: CompilableOperator) {
    record_call(bctx, expr, ResolvedCall::CompilableOperator(op));
}

fn record_spec_fn_allow_proof_args<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr) {
    record_call(bctx, expr, ResolvedCall::SpecAllowProofArgs);
}

fn record_spec_fn_no_proof_args<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr) {
    record_call(bctx, expr, ResolvedCall::Spec)
}

fn record_call<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr, resolved_call: ResolvedCall) {
    let resolved_call = match (resolved_call, &bctx.external_trait_from_to) {
        (ResolvedCall::Call(ufun, rfun, in_ghost), Some(paths)) if paths.2.is_some() => {
            let (from_path, _to_path, to_spec_path) = &**paths;
            use vir::traits::rewrite_fun;
            let ufun = rewrite_fun(from_path, to_spec_path.as_ref().unwrap(), &ufun);
            let rfun = rewrite_fun(from_path, to_spec_path.as_ref().unwrap(), &rfun);
            ResolvedCall::Call(ufun, rfun, in_ghost)
        }
        (resolved_call, _) => resolved_call,
    };
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
}
