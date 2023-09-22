use crate::attributes::{get_ghost_block_opt, get_verifier_attrs, GhostBlockAttr};
use crate::context::BodyCtxt;
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, is_smt_arith, is_type_std_rc_or_arc_or_ref, mid_ty_to_vir, typ_of_node,
    typ_of_node_expect_mut_ref,
};
use crate::rust_to_vir_expr::{
    check_lit_int, closure_param_typs, closure_to_vir, expr_to_vir, extract_array, extract_tuple,
    get_fn_path, is_expr_typ_mut_ref, mk_ty_clip, pat_to_var, ExprModifier,
};
use crate::util::{err_span, unsupported_err_span, vec_map, vec_map_result, vir_err_span_str};
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, BuiltinFunctionItem, ChainedItem, CompilableOprItem,
    DirectiveItem, EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem,
    SpecGhostTrackedItem, SpecItem, SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use crate::{unsupported_err, unsupported_err_unless};
use air::ast::{Binder, BinderX};
use air::ast_util::str_ident;
use rustc_ast::LitKind;
use rustc_hir::def::Res;
use rustc_hir::{Expr, ExprKind, Node, QPath};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::TyKind;
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArithOp, AssertQueryMode, AutospecUsage, BinaryOp, BitwiseOp, BuiltinSpecFun, CallTarget,
    ChainedOp, ComputeMode, Constant, ExprX, FieldOpr, FunX, HeaderExpr, HeaderExprX, InequalityOp,
    IntRange, IntegerTypeBoundKind, Mode, ModeCoercion, MultiOp, Quant, Typ, TypX, UnaryOp,
    UnaryOpr, VarAt, VirErr,
};
use vir::ast_util::{const_int_from_string, typ_to_diagnostic_str, types_equal, undecorate_typ};
use vir::def::positional_field_ident;

pub(crate) fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
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
                        | SpecItem::OpensInvariantsNone
                        | SpecItem::OpensInvariantsAny
                        | SpecItem::OpensInvariants
                        | SpecItem::OpensInvariantsExcept
                ) | VerusItem::Directive(DirectiveItem::ExtraDependency)
            )
        )
    {
        return Ok(bctx.spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Block(Arc::new(vec![]), None),
        ));
    }

    match rust_item {
        Some(RustItem::BoxNew) => {
            record_compilable_operator(bctx, expr, CompilableOperator::BoxNew);
            return mk_one_vir_arg(bctx, expr.span, &args);
        }
        Some(RustItem::RcNew) => {
            record_compilable_operator(bctx, expr, CompilableOperator::RcNew);
            return mk_one_vir_arg(bctx, expr.span, &args);
        }
        Some(RustItem::ArcNew) => {
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
        Some(RustItem::TryTraitBranch) => {
            return err_span(expr.span, "Verus does not yet support the ? operator");
        }
        Some(RustItem::IntoIterFn) => {
            return err_span(
                expr.span,
                "Verus does not yet support IntoIterator::into_iter and for loops, use a while loop instead",
            );
        }
        Some(RustItem::Clone) => {
            // Special case `clone` for standard Rc and Arc types
            // (Could also handle it for other types where cloning is the identity
            // operation in the SMT encoding.)
            let arg_typ = match node_substs[0].unpack() {
                GenericArgKind::Type(ty) => ty,
                _ => {
                    panic!("clone expected type argument");
                }
            };

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
        _ => {}
    }

    if let Some(verus_item) = verus_item {
        match verus_item {
            VerusItem::Pervasive(_, _)
            | VerusItem::Marker(_)
            | VerusItem::BuiltinType(_)
            | VerusItem::BuiltinTrait(_) => (),
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

    // Normal function call

    unsupported_err_unless!(
        bctx.ctxt
            .tcx
            .impl_of_method(f)
            .and_then(|method_def_id| bctx.ctxt.tcx.trait_id_of_impl(method_def_id))
            .is_none(),
        expr.span,
        "call of trait impl"
    );

    let path = def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, f);
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

    let target_kind = if tcx.trait_of_item(f).is_none() {
        vir::ast::CallTargetKind::Static
    } else {
        let mut resolved = None;
        let param_env = tcx.param_env(bctx.fun_id);
        let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);
        let inst = rustc_middle::ty::Instance::resolve(tcx, param_env, f, normalized_substs);
        if let Ok(Some(inst)) = inst {
            if let rustc_middle::ty::InstanceDef::Item(did) = inst.def {
                let typs = mk_typ_args(bctx, &inst.substs, expr.span)?;
                let f =
                    Arc::new(FunX { path: def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, did) });
                let impl_paths = get_impl_paths(bctx, did, &inst.substs);
                resolved = Some((f, typs, impl_paths));
            }
        }
        vir::ast::CallTargetKind::Method(resolved)
    };

    let record_name = match &target_kind {
        vir::ast::CallTargetKind::Method(Some((fun, _, _))) => fun.clone(),
        _ => name.clone(),
    };

    record_call(bctx, expr, ResolvedCall::Call(record_name, autospec_usage));

    let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;

    let typ_args = mk_typ_args(bctx, node_substs, expr.span)?;
    let impl_paths = get_impl_paths(bctx, f, node_substs);
    let target = CallTarget::Fun(target_kind, name, typ_args, impl_paths, autospec_usage);
    Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, ExprX::Call(target, Arc::new(vir_args))))
}

fn verus_item_to_vir<'tcx, 'a>(
    bctx: &'a BodyCtxt<'tcx>,
    expr: &'a Expr<'tcx>,
    expr_typ: impl Fn() -> Result<Arc<TypX>, VirErr>,
    verus_item: &VerusItem,
    args: &'a Vec<&'tcx Expr<'tcx>>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    node_substs: &rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
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
            SpecItem::Requires | SpecItem::Recommends => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(
                    args_len == 1,
                    expr.span,
                    "expected requires/recommends",
                    &args
                );
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.expr_ty_adjusted(arg).kind(), TyKind::Bool) {
                        return err_span(arg.span, "requires/recommends needs a bool expression");
                    }
                }
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = match spec_item {
                    SpecItem::Requires => Arc::new(HeaderExprX::Requires(Arc::new(vir_args))),
                    SpecItem::Recommends => Arc::new(HeaderExprX::Recommends(Arc::new(vir_args))),
                    _ => unreachable!(),
                };
                mk_expr(ExprX::Header(header))
            }
            SpecItem::OpensInvariants | SpecItem::OpensInvariantsExcept => {
                record_spec_fn_no_proof_args(bctx, expr);
                err_span(
                    expr.span,
                    "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
                )
            }
            SpecItem::OpensInvariantsNone => {
                record_spec_fn_no_proof_args(bctx, expr);
                let header = Arc::new(HeaderExprX::InvariantOpens(Arc::new(Vec::new())));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::OpensInvariantsAny => {
                record_spec_fn_no_proof_args(bctx, expr);
                let header = Arc::new(HeaderExprX::InvariantOpensExcept(Arc::new(Vec::new())));
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
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
                mk_expr(ExprX::Header(header))
            }
            SpecItem::Invariant | SpecItem::InvariantEnsures => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 1, expr.span, "expected invariant", &args);
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.expr_ty_adjusted(arg).kind(), TyKind::Bool) {
                        return err_span(arg.span, "invariant needs a bool expression");
                    }
                }
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = match spec_item {
                    SpecItem::Invariant => Arc::new(HeaderExprX::Invariant(Arc::new(vir_args))),
                    SpecItem::InvariantEnsures => {
                        Arc::new(HeaderExprX::InvariantEnsures(Arc::new(vir_args)))
                    }
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
            SpecItem::Admit => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 0, expr.span, "expected admit", args);
                let f = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(false)),
                );
                mk_expr(ExprX::AssertAssume { is_assume: true, expr: f })
            }
            SpecItem::Assume => {
                record_spec_fn_no_proof_args(bctx, expr);
                let arg = mk_one_vir_arg(bctx, expr.span, &args)?;
                mk_expr(ExprX::AssertAssume { is_assume: true, expr: arg })
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
                //     ::builtin::reveal_({
                //             #[verus::internal(reveal_fn)]
                //             fn __VERUS_REVEAL_INTERNAL__() {
                //                 ::builtin::reveal_internal_path_(function::path)
                //             }
                //             ;
                //             __VERUS_REVEAL_INTERNAL__
                //         }, 1);
                // }

                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(args_len == 2, expr.span, "expected reveal", &args);
                let ExprKind::Block(block, None) = args[0].kind else {
                    unsupported_err!(expr.span, "invalid reveal", &args);
                };
                if block.stmts.len() != 1
                    || !matches!(block.stmts[0].kind, rustc_hir::StmtKind::Item(_))
                {
                    unsupported_err!(expr.span, "invalid reveal", &args);
                }
                let Some(ExprKind::Path(QPath::Resolved(None, path))) = block.expr.as_ref().map(|x| &x.kind) else {
                    unsupported_err!(expr.span, "invalid reveal", &args);
                };
                let id = {
                    let Some(path_map) = &*crate::verifier::BODY_HIR_ID_TO_REVEAL_PATH_RES.read().expect("lock failed") else {
                        unsupported_err!(expr.span, "invalid reveal", &args);
                    };
                    let (ty_res, res) = &path_map[&path.res.def_id()];
                    if let Some(ty_res) = ty_res {
                        match res {
                            crate::hir_hide_reveal_rewrite::ResOrSymbol::Res(res) => {
                                // `res` has the def_id of the trait function
                                // `ty_res` has the def_id of the type
                                // we need to find the impl that contains the non-blanket
                                // implementation of the function for the type
                                let trait_ = tcx.trait_of_item(res.def_id()).expect("TODO");
                                let ty_ = tcx.type_of(ty_res.def_id());
                                *tcx.non_blanket_impls_for_ty(trait_, ty_.skip_binder())
                                    .find_map(|impl_| {
                                        let implementor_ids = &tcx.impl_item_implementor_ids(impl_);
                                        implementor_ids.get(&res.def_id())
                                    })
                                    .expect("TODO")
                            }
                            crate::hir_hide_reveal_rewrite::ResOrSymbol::Symbol(sym) => {
                                let matching_impls: Vec<_> = tcx
                                    .inherent_impls(ty_res.def_id())
                                    .iter()
                                    .filter_map(|impl_def_id| {
                                        let ident =
                                            rustc_span::symbol::Ident::from_str(sym.as_str());
                                        let found = tcx
                                            .associated_items(impl_def_id)
                                            .find_by_name_and_namespace(
                                                tcx,
                                                ident,
                                                rustc_hir::def::Namespace::ValueNS,
                                                *impl_def_id,
                                            );
                                        found.map(|f| f.def_id)
                                    })
                                    .collect();
                                if matching_impls.len() > 1 {
                                    return err_span(
                                        expr.span,
                                        format!(
                                            "{} is ambiguous, use the universal function call syntax to disambiguate (`<Type as Trait>::function`)",
                                            sym.as_str()
                                        ),
                                    );
                                } else if matching_impls.len() == 0 {
                                    return err_span(
                                        expr.span,
                                        format!("`{}` not found", sym.as_str()),
                                    );
                                } else {
                                    matching_impls.into_iter().next().unwrap()
                                }
                            }
                        }
                    } else {
                        match res {
                            crate::hir_hide_reveal_rewrite::ResOrSymbol::Res(res) => res.def_id(),
                            crate::hir_hide_reveal_rewrite::ResOrSymbol::Symbol(_) => {
                                unsupported_err!(expr.span, "unexpected reveal", &args);
                            }
                        }
                    }
                };
                let path = def_id_to_vir_path(bctx.ctxt.tcx, &bctx.ctxt.verus_items, id);

                // let fun = get_fn_path(bctx, &args[0])?;
                let ExprX::Const(Constant::Int(i)) = &expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?.x else {
                    panic!("internal error: is_reveal_fuel");
                };
                let n = vir::ast_util::fuel_const_int_to_u32(
                    &bctx.ctxt.spans.to_air_span(expr.span),
                    i,
                )?;
                let fun = Arc::new(FunX { path });
                if n == 0 {
                    let header = Arc::new(HeaderExprX::Hide(fun));
                    mk_expr(ExprX::Header(header))
                } else {
                    mk_expr(ExprX::Fuel(fun, n))
                }
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
                    if let Node::Pat(pat) = tcx.hir().get(*id) {
                        let typ = typ_of_node_expect_mut_ref(bctx, args[0].span, &expr.hir_id)?;
                        return Ok(bctx.spanned_typed_new(
                            expr.span,
                            &typ,
                            ExprX::VarAt(Arc::new(pat_to_var(pat)?), VarAt::Pre),
                        ));
                    }
                }
                err_span(expr.span, "only a variable binding is allowed as the argument to old")
            }
            ExprItem::StrSliceLen => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrLen, arg0))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_len with one argument but did not receive it"
                    ),
                }
            }
            ExprItem::StrSliceGetChar => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) if args.len() == 2 => {
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR).expect(
                            "invalid parameter for builtin::strslice_get_char at arg0, arg0 must be self",
                        );
                        let arg1 = &args[1];
                        let arg1 = expr_to_vir(bctx, arg1, ExprModifier::REGULAR)
                            .expect("invalid parameter for builtin::strslice_get_char at arg1, arg1 must be an integer");
                        mk_expr(ExprX::Binary(BinaryOp::StrGetChar, arg0, arg1))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_get_char with two argument but did not receive it"
                    ),
                }
            }
            ExprItem::StrSliceIsAscii => {
                record_spec_fn_no_proof_args(bctx, expr);
                match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrIsAscii, arg0))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_is_ascii with one argument but did not receive it"
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
            ExprItem::ClosureToFnSpec => {
                record_spec_fn_no_proof_args(bctx, expr);
                unsupported_err_unless!(
                    args_len == 1,
                    expr.span,
                    "expected closure_to_spec_fn",
                    &args
                );
                if let ExprKind::Closure(..) = &args[0].kind {
                    closure_to_vir(bctx, &args[0], expr_typ()?, true, ExprModifier::REGULAR)
                } else {
                    err_span(args[0].span, "the argument to `closure_to_spec_fn` must be a closure")
                }
            }
            ExprItem::SignedMin | ExprItem::SignedMax | ExprItem::UnsignedMax => {
                record_spec_fn_no_proof_args(bctx, expr);
                assert!(args.len() == 1);
                let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
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
            ExprItem::IsVariant => {
                record_spec_fn_allow_proof_args(bctx, expr);
                assert!(args.len() == 2);
                let adt_arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
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
                let adt_arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
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
                    }),
                    adt_arg,
                ))
            }
        },
        VerusItem::CompilableOpr(CompilableOprItem::NewStrLit) => {
            record_compilable_operator(bctx, expr, CompilableOperator::NewStrLit);
            let s = if let ExprKind::Lit(lit0) = &args[0].kind {
                if let rustc_ast::LitKind::Str(s, _) = lit0.node {
                    s
                } else {
                    panic!("unexpected arguments to new_strlit")
                }
            } else {
                panic!("unexpected arguments to new_strlit")
            };

            let c = vir::ast::Constant::StrSlice(Arc::new(s.to_string()));
            mk_expr(ExprX::Const(c))
        }
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
            if get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(expr.hir_id))
                == Some(GhostBlockAttr::Wrapper)
            {
                let bctx = &BodyCtxt { in_ghost: true, ..bctx.clone() };
                let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
                let vir_arg = vir_args[0].clone();
                match (compilable_opr, get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(arg.hir_id))) {
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
                    let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertAssume { is_assume: false, expr: exp })
                }
                AssertItem::AssertBy => {
                    unsupported_err_unless!(args_len == 2, expr.span, "expected assert_by", &args);
                    let vars = Arc::new(vec![]);
                    let require = bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Bool),
                        ExprX::Const(Constant::Bool(true)),
                    );
                    let ensure = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    let proof = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertBy { vars, require, ensure, proof })
                }
                AssertItem::AssertByCompute => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_by_compute",
                        &args
                    );
                    let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertCompute(exp, ComputeMode::Z3))
                }
                AssertItem::AssertByComputeOnly => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_by_compute_only",
                        &args
                    );
                    let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    mk_expr(ExprX::AssertCompute(exp, ComputeMode::ComputeOnly))
                }
                AssertItem::AssertNonlinearBy | AssertItem::AssertBitvectorBy => {
                    unsupported_err_unless!(
                        args_len == 1,
                        expr.span,
                        "expected assert_nonlinear_by/assert_bitvector_by with one argument",
                        &args
                    );
                    let mut vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    let header = vir::headers::read_header(&mut vir_expr)?;
                    let requires = if header.require.len() >= 1 {
                        header.require
                    } else {
                        Arc::new(vec![bctx.spanned_typed_new(
                            expr.span,
                            &Arc::new(TypX::Bool),
                            ExprX::Const(Constant::Bool(true)),
                        )])
                    };
                    if header.ensure.len() == 0 {
                        return err_span(
                            expr.span,
                            "assert_nonlinear_by/assert_bitvector_by must have at least one ensures",
                        );
                    }
                    let ensures = header.ensure;
                    let proof = vir_expr;

                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(
                        expr_attrs,
                        Some(&mut *bctx.ctxt.diagnostics.borrow_mut()),
                    )?;
                    if expr_vattrs.spinoff_prover {
                        return err_span(
                            expr.span,
                            "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith and assert by bit_vector",
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
                    let vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                    let requires = Arc::new(vec![bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Bool),
                        ExprX::Const(Constant::Bool(true)),
                    )]);
                    let ensures = Arc::new(vec![vir_expr]);
                    let proof = bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Tuple(Arc::new(vec![]))),
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
        VerusItem::WithTriggers => {
            record_spec_fn_no_proof_args(bctx, expr);
            unsupported_err_unless!(args_len == 2, expr.span, "expected with_triggers", &args);
            let modifier = ExprModifier::REGULAR;
            let triggers_tuples = expr_to_vir(bctx, args[0], modifier)?;
            let body = expr_to_vir(bctx, args[1], modifier)?;
            let mut trigs: Vec<vir::ast::Exprs> = Vec::new();
            if let ExprX::Tuple(triggers) = &triggers_tuples.x {
                for trigger_tuple in triggers.iter() {
                    if let ExprX::Tuple(terms) = &trigger_tuple.x {
                        trigs.push(terms.clone());
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
        VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            let source_vir = mk_one_vir_arg(bctx, expr.span, &args)?;
            let source_ty = undecorate_typ(&source_vir.typ);
            let to_ty = undecorate_typ(&expr_typ()?);
            match (&*source_ty, &*to_ty) {
                (TypX::Int(IntRange::U(_)), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                (TypX::Int(IntRange::USize), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                (TypX::Int(IntRange::Nat), TypX::Int(IntRange::Nat)) => Ok(source_vir),
                (TypX::Int(IntRange::Int), TypX::Int(IntRange::Nat)) => {
                    Ok(mk_ty_clip(&to_ty, &source_vir, true))
                }
                (TypX::Int(_), TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(
                        expr_attrs,
                        Some(&mut *bctx.ctxt.diagnostics.borrow_mut()),
                    )?;
                    Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate))
                }
                (TypX::Char, TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(
                        expr_attrs,
                        Some(&mut *bctx.ctxt.diagnostics.borrow_mut()),
                    )?;
                    let source_unicode =
                        mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()))?;
                    Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate))
                }
                _ => err_span(
                    expr.span,
                    "Verus currently only supports casts from integer types and `char` to integer types",
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
            mk_expr(ExprX::Binary(BinaryOp::Arith(ArithOp::Sub, Mode::Spec), zero, varg))
        }
        VerusItem::Chained(chained_item) => {
            record_spec_fn_allow_proof_args(bctx, expr);
            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
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
        VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut)) => {
            record_spec_fn_no_proof_args(bctx, expr);

            assert!(args.len() == 1);
            let modif = is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(&args[0]), outer_modifier)?;
            let vir_arg = expr_to_vir(bctx, &args[0], modif)?;

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
            let vir_arg = expr_to_vir(bctx, &args[0], modif)?;

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
                        .help("decorations (like &,&mut,Ghost,Tracked,Box,Rc,...) are transparent for == or != in spec code"));
                }
            }

            // REVIEW: mk_vir_args handles mutable ref arguments, so you can do, e.g.,
            // `x == y` where x has type `&mut T` and y has type `T`.
            // Is this intentional?
            let vir_args = mk_vir_args(bctx, node_substs, f, &args)?;
            let lhs = vir_args[0].clone();
            let rhs = vir_args[1].clone();

            if matches!(equ_item, EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep) {
                assert!(node_substs.len() == 1);
                let t = match node_substs[0].unpack() {
                    GenericArgKind::Type(ty) => mid_ty_to_vir(
                        tcx,
                        &bctx.ctxt.verus_items,
                        bctx.fun_id,
                        expr.span,
                        &ty,
                        false,
                    )?,
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
            // Imply is marked as unimplemented! in builtin.
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
                return err_span(expr.span, "expected types for this operator");
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
                    let mode_for_ghostness = if bctx.in_ghost { Mode::Spec } else { Mode::Exec };
                    match arith_item {
                        ArithItem::BuiltinAdd => BinaryOp::Arith(ArithOp::Add, mode_for_ghostness),
                        ArithItem::BuiltinSub => BinaryOp::Arith(ArithOp::Sub, mode_for_ghostness),
                        ArithItem::BuiltinMul => BinaryOp::Arith(ArithOp::Mul, mode_for_ghostness),
                    }
                }
                VerusItem::BinaryOp(BinaryOpItem::SpecArith(spec_arith_item)) => {
                    match spec_arith_item {
                        SpecArithItem::Add => BinaryOp::Arith(ArithOp::Add, Mode::Spec),
                        SpecArithItem::Sub => BinaryOp::Arith(ArithOp::Sub, Mode::Spec),
                        SpecArithItem::Mul => BinaryOp::Arith(ArithOp::Mul, Mode::Spec),
                        SpecArithItem::EuclideanDiv => {
                            BinaryOp::Arith(ArithOp::EuclideanDiv, Mode::Spec)
                        }
                        SpecArithItem::EuclideanMod => {
                            BinaryOp::Arith(ArithOp::EuclideanMod, Mode::Spec)
                        }
                    }
                }
                VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(spec_bitwise)) => {
                    match spec_bitwise {
                        verus_items::SpecBitwiseItem::BitAnd => {
                            BinaryOp::Bitwise(BitwiseOp::BitAnd, Mode::Spec)
                        }
                        verus_items::SpecBitwiseItem::BitOr => {
                            BinaryOp::Bitwise(BitwiseOp::BitOr, Mode::Spec)
                        }
                        verus_items::SpecBitwiseItem::BitXor => {
                            if matches!(*lhs.typ, TypX::Bool) {
                                BinaryOp::Xor
                            } else {
                                BinaryOp::Bitwise(BitwiseOp::BitXor, Mode::Spec)
                            }
                        }
                        verus_items::SpecBitwiseItem::Shl => {
                            BinaryOp::Bitwise(BitwiseOp::Shl, Mode::Spec)
                        }
                        verus_items::SpecBitwiseItem::Shr => {
                            BinaryOp::Bitwise(BitwiseOp::Shr, Mode::Spec)
                        }
                    }
                }
                _ => unreachable!("internal error"),
            };

            let e = mk_expr(ExprX::Binary(vop, lhs, rhs))?;
            if matches!(
                verus_item,
                VerusItem::BinaryOp(BinaryOpItem::Arith(_) | BinaryOpItem::SpecArith(_))
            ) {
                Ok(mk_ty_clip(&expr_typ()?, &e, true))
            } else {
                Ok(e)
            }
        }
        VerusItem::BuiltinFunction(
            re @ (BuiltinFunctionItem::FnWithSpecificationRequires
            | BuiltinFunctionItem::FnWithSpecificationEnsures),
        ) => {
            record_spec_fn_no_proof_args(bctx, expr);

            let bsf = match re {
                BuiltinFunctionItem::FnWithSpecificationRequires => {
                    assert!(args.len() == 2);
                    BuiltinSpecFun::ClosureReq
                }
                BuiltinFunctionItem::FnWithSpecificationEnsures => {
                    assert!(args.len() == 3);
                    BuiltinSpecFun::ClosureEns
                }
            };

            let vir_args = args
                .iter()
                .map(|arg| expr_to_vir(bctx, &arg, ExprModifier::REGULAR))
                .collect::<Result<Vec<_>, _>>()?;

            let typ_args = mk_typ_args(bctx, node_substs, expr.span)?;

            return mk_expr(ExprX::Call(
                CallTarget::BuiltinSpecFun(bsf, typ_args),
                Arc::new(vir_args),
            ));
        }
        VerusItem::Pervasive(_, _)
        | VerusItem::Marker(_)
        | VerusItem::BuiltinType(_)
        | VerusItem::BuiltinTrait(_) => unreachable!(),
    }
}

fn get_impl_paths<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
) -> vir::ast::ImplPaths {
    if let rustc_middle::ty::FnDef(fid, _fsubsts) = bctx.ctxt.tcx.type_of(f).skip_binder().kind() {
        crate::rust_to_vir_base::get_impl_paths(
            bctx.ctxt.tcx,
            &bctx.ctxt.verus_items,
            bctx.fun_id,
            *fid,
            node_substs,
        )
    } else {
        panic!("unexpected function {:?}", f)
    }
}

fn extract_ensures<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<HeaderExpr, VirErr> {
    let expr = skip_closure_coercion(bctx, expr);
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(closure) => {
            let typs: Vec<Typ> = closure_param_typs(bctx, expr)?;
            let body = tcx.hir().body(closure.body);
            let mut xs: Vec<String> = Vec::new();
            for param in body.params.iter() {
                xs.push(pat_to_var(param.pat)?);
            }
            let expr = &body.value;
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            if typs.len() == 1 && xs.len() == 1 {
                let id_typ = Some((Arc::new(xs[0].clone()), typs[0].clone()));
                Ok(Arc::new(HeaderExprX::Ensures(id_typ, Arc::new(args))))
            } else if typs.len() == 0 && xs.len() == 0 {
                Ok(Arc::new(HeaderExprX::Ensures(None, Arc::new(args))))
            } else {
                err_span(expr.span, "expected 1 parameter in closure")
            }
        }
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            Ok(Arc::new(HeaderExprX::Ensures(None, Arc::new(args))))
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
            let body = tcx.hir().body(closure.body);
            let typs = closure_param_typs(bctx, expr)?;
            assert!(typs.len() == body.params.len());
            let mut binders: Vec<Binder<Typ>> = Vec::new();
            for (x, t) in body.params.iter().zip(typs) {
                binders.push(Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)?), a: t }));
            }
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() + header.ensure.len() > 0 {
                return err_span(expr.span, "forall/ensures cannot have requires/ensures");
            }
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
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    if matches!(bctx.types.expr_ty_adjusted(expr).kind(), TyKind::Bool) {
        expr_to_vir(bctx, expr, ExprModifier::REGULAR)
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
            let body = tcx.hir().body(closure.body);
            let typs = closure_param_typs(bctx, expr)?;
            assert!(body.params.len() == typs.len());
            let mut binders: Vec<Binder<Typ>> = Vec::new();
            for (x, t) in body.params.iter().zip(typs) {
                binders.push(Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)?), a: t }));
            }
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() > 1 {
                return err_span(expr.span, "assert_forall_by can have at most one requires");
            }
            if header.ensure.len() != 1 {
                return err_span(expr.span, "assert_forall_by must have exactly one ensures");
            }
            if header.ensure_id_typ.is_some() {
                return err_span(expr.span, "ensures clause must be a bool");
            }
            let typ = Arc::new(TypX::Tuple(Arc::new(vec![])));
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
            let ensure = header.ensure[0].clone();
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
            let closure_body = tcx.hir().body(closure.body);
            let mut params: Vec<Binder<Typ>> = Vec::new();
            let mut vars: Vec<vir::ast::Expr> = Vec::new();
            let typs = closure_param_typs(bctx, expr)?;
            assert!(closure_body.params.len() == typs.len());
            for (x, typ) in closure_body.params.iter().zip(typs) {
                let name = Arc::new(pat_to_var(x.pat)?);
                let vir_expr = bctx.spanned_typed_new(x.span, &typ, ExprX::Var(name.clone()));
                let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                erasure_info.hir_vir_ids.push((x.pat.hir_id, vir_expr.span.id));
                vars.push(vir_expr);
                params.push(Arc::new(BinderX { name, a: typ }));
            }
            let typs = vec_map(&params, |p| p.a.clone());
            let cond_expr = &closure_body.value;
            let cond = expr_to_vir(bctx, cond_expr, ExprModifier::REGULAR)?;
            let body = if tuple {
                let typ = Arc::new(TypX::Tuple(Arc::new(typs)));
                if !vir::ast_util::types_equal(&typ, &expr_typ) {
                    return err_span(
                        expr.span,
                        format!(
                            "expected choose_tuple to have type {:?}, found type {:?}",
                            typ, expr_typ
                        ),
                    );
                }
                bctx.spanned_typed_new(span, &typ, ExprX::Tuple(Arc::new(vars)))
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
                            return &args_slice[0];
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        },
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
            let e0 = expr_to_vir(bctx, exp0, ExprModifier::REGULAR)?;
            let e1 = expr_to_vir(bctx, exp1, ExprModifier::REGULAR)?;
            if vir::recursion::height_is_int(&e0.typ) {
                if lt {
                    // 0 <= x < y
                    let zerox = ExprX::Const(vir::ast_util::const_int_from_u128(0));
                    let zero = bctx.spanned_typed_new(span, &tint, zerox);
                    let op0 = BinaryOp::Inequality(InequalityOp::Le);
                    let cmp0 = mk_bop(op0, zero, e0);
                    let op1 = BinaryOp::Inequality(InequalityOp::Lt);
                    let e0 = expr_to_vir(bctx, exp0, ExprModifier::REGULAR)?;
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

fn mk_typ_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    substs: &rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    span: Span,
) -> Result<vir::ast::Typs, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let mut typ_args: Vec<Typ> = Vec::new();
    for typ_arg in substs {
        match typ_arg.unpack() {
            GenericArgKind::Type(ty) => {
                typ_args.push(mid_ty_to_vir(
                    tcx,
                    &bctx.ctxt.verus_items,
                    bctx.fun_id,
                    span,
                    &ty,
                    false,
                )?);
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
    // TODO(main_new) is calling `subst` still correct with the new API?
    let tcx = bctx.ctxt.tcx;
    let raw_inputs = bctx.ctxt.tcx.fn_sig(f).subst(tcx, node_substs).skip_binder().inputs();
    assert!(raw_inputs.len() == args.len());
    args.iter()
        .zip(raw_inputs)
        .map(|(arg, raw_param)| {
            let is_mut_ref_param = match raw_param.kind() {
                TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => true,
                _ => false,
            };
            if is_mut_ref_param {
                let expr = expr_to_vir(bctx, arg, ExprModifier { deref_mut: true, addr_of: true })?;
                Ok(bctx.spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else {
                expr_to_vir(
                    bctx,
                    arg,
                    is_expr_typ_mut_ref(bctx.types.expr_ty_adjusted(arg), ExprModifier::REGULAR)?,
                )
            }
        })
        .collect::<Result<Vec<_>, _>>()
}

fn mk_one_vir_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<vir::ast::Expr, VirErr> {
    unsupported_err_unless!(args.len() == 1, span, "expected 1 argument", &args);
    expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)
}

fn mk_two_vir_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    args: &Vec<&'tcx Expr<'tcx>>,
) -> Result<(vir::ast::Expr, vir::ast::Expr), VirErr> {
    unsupported_err_unless!(args.len() == 2, span, "expected 2 arguments", &args);
    let e0 = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
    let e1 = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
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
            format!("Verus builtin `{fn_name_for_error_msg:}` requires a string literal"),
        ),
    }
}

fn check_variant_field<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    adt_arg: &'tcx Expr<'tcx>,
    variant_name: &String,
    field_name_typ: Option<(String, &rustc_middle::ty::Ty<'tcx>)>,
) -> Result<(vir::ast::Path, Option<vir::ast::Ident>), VirErr> {
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

    let variant_opt = adt.variants().iter().find(|v| v.ident(tcx).as_str() == variant_name);
    let Some(variant) = variant_opt else {
        return err_span(span, format!("no variant `{variant_name:}` for this datatype"));
    };

    let vir_adt_ty = mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, bctx.fun_id, span, &ty, false)?;
    let adt_path = match &*vir_adt_ty {
        TypX::Datatype(path, _, _) => path.clone(),
        _ => {
            return err_span(span, format!("expected type to be datatype"));
        }
    };

    match field_name_typ {
        None => Ok((adt_path, None)),
        Some((field_name, expected_field_typ)) => {
            let field_opt = variant.fields.iter().find(|f| f.ident(tcx).as_str() == field_name);
            let Some(field) = field_opt else {
                return err_span(span, format!("no field `{field_name:}` for this variant"));
            };

            let field_ty = field.ty(tcx, substs);
            let vir_field_ty =
                mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, bctx.fun_id, span, &field_ty, false)?;
            let vir_expected_field_ty = mid_ty_to_vir(
                tcx,
                &bctx.ctxt.verus_items,
                bctx.fun_id,
                span,
                &expected_field_typ,
                false,
            )?;
            if !types_equal(&vir_field_ty, &vir_expected_field_ty) {
                return err_span(span, "field has the wrong type");
            }

            let field_ident = if field_name.as_str().bytes().nth(0).unwrap().is_ascii_digit() {
                let i = field_name.parse::<usize>().unwrap();
                positional_field_ident(i)
            } else {
                str_ident(&field_name)
            };

            Ok((adt_path, Some(field_ident)))
        }
    }
}

fn record_compilable_operator<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr, op: CompilableOperator) {
    let resolved_call = ResolvedCall::CompilableOperator(op);
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
}

fn record_spec_fn_allow_proof_args<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr) {
    let resolved_call = ResolvedCall::SpecAllowProofArgs;
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
}

fn record_spec_fn_no_proof_args<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr) {
    let resolved_call = ResolvedCall::Spec;
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
}

fn record_call<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr, resolved_call: ResolvedCall) {
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_calls.push((expr.hir_id, expr.span.data(), resolved_call));
}
