use crate::attributes::{get_ghost_block_opt, get_verifier_attrs, GetVariantField, GhostBlockAttr};
use crate::context::BodyCtxt;
use crate::erase::CompilableOperator;
use crate::rust_to_vir_base::{
    def_id_to_vir_path, is_smt_arith, mid_ty_to_vir, typ_of_node, typ_of_node_expect_mut_ref,
};
use crate::rust_to_vir_expr::{
    check_lit_int, closure_param_typs, closure_to_vir, expr_to_vir, extract_array, extract_tuple,
    get_fn_path, is_expr_typ_mut_ref, mk_ty_clip, pat_to_var, record_fun, ExprModifier,
};
use crate::util::{err_span, unsupported_err_span, vec_map, vec_map_result};
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, ChainedItem, CompilableOprItem, DirectiveItem,
    EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem, SpecGhostTrackedItem, SpecItem,
    SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use crate::{unsupported_err, unsupported_err_unless};
use air::ast::{Binder, BinderX};
use air::ast_util::str_ident;
use rustc_ast::{BorrowKind, LitKind, Mutability};
use rustc_hir::def::Res;
use rustc_hir::{Expr, ExprKind, Node, QPath};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{Clause, EarlyBinder, PredicateKind, TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArithOp, AssertQueryMode, AutospecUsage, BinaryOp, BitwiseOp, CallTarget, ComputeMode,
    Constant, ExprX, FieldOpr, FunX, HeaderExpr, HeaderExprX, Ident, InequalityOp, IntRange,
    IntegerTypeBoundKind, Mode, ModeCoercion, MultiOp, Quant, Typ, TypX, UnaryOp, UnaryOpr, VarAt,
    VirErr,
};
use vir::ast_util::{const_int_from_string, types_equal, undecorate_typ};
use vir::def::positional_field_ident;

pub(crate) fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
    fn_span: Span,
    args: Vec<&'tcx Expr<'tcx>>,
    outer_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;

    // DO NOT use f_name to find items (i.e. do not use f_name == "core::cmp::Eq"),
    // use `crate::verus_item::get_rust_item` instead
    let f_name = tcx.def_path_str(f);

    let verus_item = bctx.ctxt.get_verus_item(f);
    let rust_item = verus_items::get_rust_item(tcx, f);

    // TODO these were broken (they sometimes/often appear as std::cmp::*); do we need them?
    // let is_eq = f_name == "core::cmp::PartialEq::eq";
    // let is_ne = f_name == "core::cmp::PartialEq::ne";
    // let is_le = f_name == "core::cmp::PartialOrd::le";
    // let is_ge = f_name == "core::cmp::PartialOrd::ge";
    // let is_lt = f_name == "core::cmp::PartialOrd::lt";
    // let is_gt = f_name == "core::cmp::PartialOrd::gt";
    // let is_add = f_name == "std::ops::Add::add";
    // let is_sub = f_name == "std::ops::Sub::sub";
    // let is_mul = f_name == "std::ops::Mul::mul";

    let is_spec_op = matches!(
        verus_item,
        Some(
            VerusItem::BinaryOp(
                BinaryOpItem::SpecArith(_)
                    | BinaryOpItem::SpecBitwise(_)
                    | BinaryOpItem::Equality(_)
                    | BinaryOpItem::SpecOrd(_)
            ) | VerusItem::Chained(_)
                | VerusItem::UnaryOp(
                    UnaryOpItem::SpecLiteral(_)
                        | UnaryOpItem::SpecCastInteger
                        | UnaryOpItem::SpecNeg
                )
        )
    );

    // These functions are all no-ops in the SMT encoding, so we don't emit any VIR
    let is_smartptr_new =
        matches!(rust_item, Some(RustItem::BoxNew | RustItem::RcNew | RustItem::ArcNew));

    if let Some(VerusItem::OpenInvariantBlock(_)) = verus_item {
        // `open_invariant_begin` and `open_invariant_end` calls should only appear
        // through use of the `open_invariant!` macro, which creates an invariant block.
        // Thus, they should end up being processed by `invariant_block_to_vir` before
        // we get here. Thus, for any well-formed use of an invariant block, we should
        // not reach this point.
        return err_span(
            expr.span,
            format!(
                "{} should never be used except through open_atomic_invariant or open_local_invariant macro",
                f_name
            ),
        );
    }

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

    if matches!(rust_item, Some(RustItem::Panic)) {
        return err_span(
            expr.span,
            format!(
                "panic is not supported (if you used Rust's `assert!` macro, you may have meant to use Verus's `assert` function)"
            ),
        );
    }

    unsupported_err_unless!(
        bctx.ctxt
            .tcx
            .impl_of_method(f)
            .and_then(|method_def_id| bctx.ctxt.tcx.trait_id_of_impl(method_def_id))
            .is_none(),
        expr.span,
        "call of trait impl"
    );

    let is_spec_no_proof_args = matches!(
        verus_item,
        Some(
            VerusItem::Spec(_)
                | VerusItem::Quant(_)
                | VerusItem::Directive(_)
                | VerusItem::Expr(
                    ExprItem::Choose
                        | ExprItem::ChooseTuple
                        | ExprItem::Old
                        | ExprItem::StrSliceLen
                        | ExprItem::StrSliceGetChar
                        | ExprItem::StrSliceIsAscii
                        | ExprItem::ClosureToFnSpec
                        | ExprItem::ArchWordBits
                        | ExprItem::IsSmallerThan
                        | ExprItem::IsSmallerThanLexicographic
                        | ExprItem::IsSmallerThanRecursiveFunctionField
                )
                | VerusItem::Assert(_)
                | VerusItem::WithTriggers
                | VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(_))
        )
    );
    let is_spec_allow_proof_args_pre = is_spec_op
        || matches!(
            verus_item,
            Some(
                VerusItem::Expr(ExprItem::SignedMax | ExprItem::SignedMin | ExprItem::UnsignedMax)
                    | VerusItem::BinaryOp(BinaryOpItem::Arith(_))
            )
        );
    let is_compilable_operator = match verus_item {
        Some(VerusItem::CompilableOpr(compilable_opr)) => Some(match compilable_opr {
            CompilableOprItem::Implies => CompilableOperator::Implies,
            CompilableOprItem::NewStrLit => CompilableOperator::NewStrLit,
            CompilableOprItem::GhostExec | CompilableOprItem::GhostNew => {
                CompilableOperator::GhostExec
            }
            CompilableOprItem::TrackedNew => CompilableOperator::TrackedNew,
            CompilableOprItem::TrackedExec => CompilableOperator::TrackedExec,
            CompilableOprItem::TrackedExecBorrow => CompilableOperator::TrackedExecBorrow,
            CompilableOprItem::TrackedGet => CompilableOperator::TrackedGet,
            CompilableOprItem::TrackedBorrow => CompilableOperator::TrackedBorrow,
            CompilableOprItem::TrackedBorrowMut => CompilableOperator::TrackedBorrowMut,
        }),
        None if is_smartptr_new => Some(CompilableOperator::SmartPtrNew),
        _ => None,
    };
    let needs_name = !(is_spec_no_proof_args
        || is_spec_allow_proof_args_pre
        || is_compilable_operator.is_some());
    let path =
        if !needs_name { None } else { Some(def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, f)) };

    let is_get_variant = {
        let fn_attrs = if f.as_local().is_some() {
            match tcx.hir().get_if_local(f) {
                Some(rustc_hir::Node::ImplItem(
                    impl_item @ rustc_hir::ImplItem {
                        kind: rustc_hir::ImplItemKind::Fn(..), ..
                    },
                )) => Some(bctx.ctxt.tcx.hir().attrs(impl_item.hir_id())),
                Some(rustc_hir::Node::Item(
                    item @ rustc_hir::Item { kind: rustc_hir::ItemKind::Fn(..), .. },
                )) => Some(bctx.ctxt.tcx.hir().attrs(item.hir_id())),
                _ => None,
            }
        } else {
            Some(bctx.ctxt.tcx.item_attrs(f))
        };
        if let Some(fn_attrs) = fn_attrs {
            let fn_vattrs = get_verifier_attrs(fn_attrs)?;
            let is_get_variant = if let Some(variant_ident) = fn_vattrs.is_variant {
                Some((variant_ident, None))
            } else if let Some((variant_ident, field_ident)) = fn_vattrs.get_variant {
                Some((variant_ident, Some(field_ident)))
            } else {
                None
            };
            is_get_variant
        } else {
            None
        }
    };

    let name =
        if let Some(path) = &path { Some(Arc::new(FunX { path: path.clone() })) } else { None };

    let is_spec_allow_proof_args = is_spec_allow_proof_args_pre || is_get_variant.is_some();
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
            if let rustc_middle::ty::InstanceDef::Item(item) = inst.def {
                if let rustc_middle::ty::WithOptConstParam { did, const_param_did: None } = item {
                    let typs = mk_typ_args(bctx, &inst.substs, expr.span)?;
                    let f = Arc::new(FunX {
                        path: def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, did),
                    });
                    let impl_paths = get_impl_paths(bctx, did, &inst.substs);
                    resolved = Some((f, typs, impl_paths));
                }
            }
        }
        vir::ast::CallTargetKind::Method(resolved)
    };

    let record_name = match &target_kind {
        vir::ast::CallTargetKind::Method(Some((fun, _, _))) => Some(fun.clone()),
        _ => name.clone(),
    };

    record_fun(
        &bctx.ctxt,
        expr.hir_id,
        fn_span,
        &record_name,
        &f_name,
        is_spec_no_proof_args,
        is_spec_allow_proof_args,
        is_compilable_operator,
        autospec_usage,
    );

    let len = args.len();
    let expr_typ = || typ_of_node(bctx, expr.span, &expr.hir_id, false);
    let mk_expr = |x: ExprX| Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, x));
    let mk_expr_span = |span: Span, x: ExprX| Ok(bctx.spanned_typed_new(span, &expr_typ()?, x));

    match verus_item {
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(spec_literal_item))) => {
            unsupported_err_unless!(len == 1, expr.span, "expected spec_literal_*", &args);
            let arg = &args[0];
            let is_num = |s: &String| s.chars().count() > 0 && s.chars().all(|c| c.is_digit(10));
            match &args[0] {
                Expr { kind: ExprKind::Lit(Spanned { node: LitKind::Str(s, _), .. }), .. }
                    if is_num(&s.to_string()) =>
                {
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
                    return mk_expr(ExprX::Const(const_int_from_string(s.to_string())));
                }
                _ => {
                    return err_span(arg.span, "spec_literal_* requires a string literal");
                }
            }
        }
        Some(VerusItem::UnaryOp(
            UnaryOpItem::SpecNeg | UnaryOpItem::SpecCastInteger | UnaryOpItem::SpecGhostTracked(_),
        )) => {
            // handled separately later
        }
        Some(VerusItem::Spec(spec_item)) => match spec_item {
            SpecItem::NoMethodBody => {
                return mk_expr(ExprX::Header(Arc::new(HeaderExprX::NoMethodBody)));
            }
            SpecItem::Requires | SpecItem::Recommends => {
                unsupported_err_unless!(len == 1, expr.span, "expected requires/recommends", &args);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
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
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::OpensInvariants | SpecItem::OpensInvariantsExcept => {
                return err_span(
                    expr.span,
                    "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
                );
            }
            SpecItem::OpensInvariantsNone => {
                let header = Arc::new(HeaderExprX::InvariantOpens(Arc::new(Vec::new())));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::OpensInvariantsAny => {
                let header = Arc::new(HeaderExprX::InvariantOpensExcept(Arc::new(Vec::new())));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Ensures => {
                unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let header = extract_ensures(&bctx, args[0])?;
                let expr = mk_expr_span(args[0].span, ExprX::Header(header));
                // extract_ensures does most of the necessary work, so we can return at this point
                return expr;
            }
            SpecItem::Decreases => {
                unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
                let subargs = extract_tuple(args[0]);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Invariant | SpecItem::InvariantEnsures => {
                unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
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
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::DecreasesBy | SpecItem::RecommendsBy => {
                unsupported_err_unless!(len == 1, expr.span, "expected function", &args);
                let x = get_fn_path(bctx, &args[0])?;
                let header = Arc::new(HeaderExprX::DecreasesBy(x));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::DecreasesWhen | SpecItem::Admit | SpecItem::Assume => {
                // handled later, they require VIR args
            }
        },
        Some(VerusItem::Quant(quant_item)) => {
            unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
            let quant = match quant_item {
                QuantItem::Forall | QuantItem::ForallArith => air::ast::Quant::Forall,
                QuantItem::Exists => air::ast::Quant::Exists,
            };
            let quant = Quant { quant, boxed_params: quant_item != &QuantItem::ForallArith };
            return extract_quant(bctx, expr.span, quant, args[0]);
        }
        Some(VerusItem::Directive(directive_item)) => match directive_item {
            DirectiveItem::ExtraDependency | DirectiveItem::Hide | DirectiveItem::Reveal => {
                unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", &args);
                let x = get_fn_path(bctx, &args[0])?;
                match directive_item {
                    DirectiveItem::Hide => {
                        let header = Arc::new(HeaderExprX::Hide(x));
                        return mk_expr(ExprX::Header(header));
                    }
                    DirectiveItem::ExtraDependency => {
                        let header = Arc::new(HeaderExprX::ExtraDependency(x));
                        return mk_expr(ExprX::Header(header));
                    }
                    DirectiveItem::Reveal => {
                        return mk_expr(ExprX::Fuel(x, 1));
                    }
                    _ => unreachable!(),
                }
            }
            DirectiveItem::RevealFuel => {
                unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", &args);
                let x = get_fn_path(bctx, &args[0])?;
                match &expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?.x {
                    ExprX::Const(Constant::Int(i)) => {
                        let n = vir::ast_util::const_int_to_u32(
                            &bctx.ctxt.spans.to_air_span(expr.span),
                            i,
                        )?;
                        return mk_expr(ExprX::Fuel(x, n));
                    }
                    _ => panic!("internal error: is_reveal_fuel"),
                }
            }
            DirectiveItem::RevealStrlit => {
                if let Some(s) = if let ExprKind::Lit(lit0) = &args[0].kind {
                    if let rustc_ast::LitKind::Str(s, _) = lit0.node { Some(s) } else { None }
                } else {
                    None
                } {
                    return mk_expr(ExprX::RevealString(Arc::new(s.to_string())));
                } else {
                    return err_span(args[0].span, "string literal expected".to_string());
                }
            }
        },
        Some(VerusItem::Expr(expr_item)) => match expr_item {
            ExprItem::Choose => {
                unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
                return extract_choose(bctx, expr.span, args[0], false, expr_typ()?);
            }
            ExprItem::ChooseTuple => {
                unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
                return extract_choose(bctx, expr.span, args[0], true, expr_typ()?);
            }
            ExprItem::Old => {
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
                return err_span(
                    expr.span,
                    "only a variable binding is allowed as the argument to old",
                );
            }
            ExprItem::StrSliceLen => {
                return match &expr.kind {
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
                };
            }
            ExprItem::StrSliceGetChar => {
                return match &expr.kind {
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
                };
            }
            ExprItem::StrSliceIsAscii => {
                return match &expr.kind {
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
                };
            }
            ExprItem::ArchWordBits => {
                assert!(args.len() == 0);
                let arg = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Int(IntRange::Int)),
                    ExprX::Const(vir::ast_util::const_int_from_u128(0)),
                );

                let kind = IntegerTypeBoundKind::ArchWordBits;

                return mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg));
            }
            ExprItem::ClosureToFnSpec => {
                unsupported_err_unless!(len == 1, expr.span, "expected closure_to_spec_fn", &args);
                if let ExprKind::Closure(..) = &args[0].kind {
                    return closure_to_vir(
                        bctx,
                        &args[0],
                        expr_typ()?,
                        true,
                        ExprModifier::REGULAR,
                    );
                } else {
                    return err_span(
                        args[0].span,
                        "the argument to `closure_to_spec_fn` must be a closure",
                    );
                }
            }
            ExprItem::SignedMin | ExprItem::SignedMax | ExprItem::UnsignedMax => {
                assert!(args.len() == 1);
                let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let kind = match expr_item {
                    ExprItem::SignedMin => IntegerTypeBoundKind::SignedMin,
                    ExprItem::SignedMax => IntegerTypeBoundKind::SignedMax,
                    ExprItem::UnsignedMax => IntegerTypeBoundKind::UnsignedMax,
                    _ => unreachable!(),
                };
                return mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg));
            }
            ExprItem::IsSmallerThan
            | ExprItem::IsSmallerThanLexicographic
            | ExprItem::IsSmallerThanRecursiveFunctionField => {
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
                return mk_is_smaller_than(
                    bctx,
                    expr.span,
                    args0,
                    args1,
                    expr_item == &ExprItem::IsSmallerThanRecursiveFunctionField,
                );
            }
        },
        Some(VerusItem::CompilableOpr(compilable_opr)) => match compilable_opr {
            CompilableOprItem::NewStrLit => {
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
                return mk_expr(ExprX::Const(c));
            }
            _ => {
                // handled later, they require VIR args
            }
        },
        Some(VerusItem::BinaryOp(_) | VerusItem::Chained(_)) => {
            // handled elsewhere
        }
        Some(VerusItem::Assert(assert_item)) => match assert_item {
            AssertItem::Assert => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert", &args);
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertAssume { is_assume: false, expr: exp });
            }
            AssertItem::AssertBy => {
                unsupported_err_unless!(len == 2, expr.span, "expected assert_by", &args);
                let vars = Arc::new(vec![]);
                let require = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(true)),
                );
                let ensure = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let proof = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::Forall { vars, require, ensure, proof });
            }
            AssertItem::AssertByCompute => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert_by_compute", &args);
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertCompute(exp, ComputeMode::Z3));
            }
            AssertItem::AssertByComputeOnly => {
                unsupported_err_unless!(
                    len == 1,
                    expr.span,
                    "expected assert_by_compute_only",
                    &args
                );
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertCompute(exp, ComputeMode::ComputeOnly));
            }
            AssertItem::AssertNonlinearBy | AssertItem::AssertBitvectorBy => {
                unsupported_err_unless!(
                    len == 1,
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
                let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                if expr_vattrs.spinoff_prover {
                    return err_span(
                        expr.span,
                        "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith and assert by bit_vector",
                    );
                }
                return mk_expr(ExprX::AssertQuery {
                    requires,
                    ensures,
                    proof,
                    mode: match assert_item {
                        AssertItem::AssertNonlinearBy => AssertQueryMode::NonLinear,
                        AssertItem::AssertBitvectorBy => AssertQueryMode::BitVector,
                        _ => unreachable!(),
                    },
                });
            }
            AssertItem::AssertForallBy => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert_forall_by", &args);
                return extract_assert_forall_by(bctx, expr.span, args[0]);
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
                return mk_expr(ExprX::AssertQuery {
                    requires,
                    ensures,
                    proof,
                    mode: AssertQueryMode::BitVector,
                });
            }
        },
        Some(VerusItem::WithTriggers) => {
            unsupported_err_unless!(len == 2, expr.span, "expected with_triggers", &args);
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
            return mk_expr(ExprX::WithTriggers { triggers, body });
        }
        Some(
            VerusItem::OpenInvariantBlock(_)
            | VerusItem::Pervasive(_, _)
            | VerusItem::Marker(_)
            | VerusItem::BuiltinType(_)
            | VerusItem::BuiltinFunction(_),
        ) => {}
        None => (),
    }

    if is_smartptr_new {
        unsupported_err_unless!(len == 1, expr.span, "expected 1 argument", &args);
        let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;

        return Ok(arg);
    }

    let vir_args = mk_vir_args(bctx, node_substs, f, &args, verus_item, outer_modifier)?;

    match is_get_variant {
        Some((variant_name, None)) => {
            return mk_expr(ExprX::UnaryOpr(
                UnaryOpr::IsVariant {
                    datatype: variant_fn_get_datatype(tcx, &bctx.ctxt.verus_items, f, expr.span)?,
                    variant: str_ident(&variant_name),
                },
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            ));
        }
        Some((variant_name, Some(variant_field))) => {
            let variant_name_ident = str_ident(&variant_name);
            return mk_expr(ExprX::UnaryOpr(
                UnaryOpr::Field(FieldOpr {
                    datatype: variant_fn_get_datatype(tcx, &bctx.ctxt.verus_items, f, expr.span)?,
                    variant: variant_name_ident.clone(),
                    field: match variant_field {
                        GetVariantField::Named(n) => str_ident(&n),
                        GetVariantField::Unnamed(i) => positional_field_ident(i),
                    },
                    get_variant: true,
                }),
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            ));
        }
        None => {}
    }

    let is_smt_unary = if verus_item == Some(&VerusItem::UnaryOp(UnaryOpItem::SpecNeg)) {
        match *undecorate_typ(&typ_of_node(bctx, args[0].span, &args[0].hir_id, false)?) {
            TypX::Int(_) => true,
            _ => false,
        }
    } else {
        false
    };
    let is_smt_binary = match verus_item {
        Some(verus_item) => match verus_item {
            VerusItem::BinaryOp(BinaryOpItem::Equality(
                EqualityItem::Equal | EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep,
            )) => true,
            VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::SpecEq)) => {
                let t1 = typ_of_node(bctx, args[0].span, &args[0].hir_id, true)?;
                let t2 = typ_of_node(bctx, args[1].span, &args[1].hir_id, true)?;
                // REVIEW: there's some code that (harmlessly) uses == on types that are
                // different in decoration; Rust would reject this, but we currently allow it:
                let t1 = undecorate_typ(&t1);
                let t2 = undecorate_typ(&t2);
                if types_equal(&t1, &t2)
                    || is_smt_arith(
                        bctx,
                        args[0].span,
                        args[1].span,
                        &args[0].hir_id,
                        &args[1].hir_id,
                    )?
                {
                    true
                } else {
                    return err_span(expr.span, "types must be compatible to use == or !=");
                }
            }
            VerusItem::CompilableOpr(CompilableOprItem::Implies)
            | VerusItem::BinaryOp(
                BinaryOpItem::Arith(_)
                | BinaryOpItem::SpecArith(_)
                | BinaryOpItem::SpecBitwise(_)
                | BinaryOpItem::SpecOrd(_),
            ) => is_smt_arith(bctx, args[0].span, args[1].span, &args[0].hir_id, &args[1].hir_id)?,
            _ => false,
        },
        None => false,
    };

    match verus_item {
        Some(VerusItem::CompilableOpr(compilable_opr)) => match compilable_opr {
            CompilableOprItem::GhostExec | CompilableOprItem::TrackedExec => {
                // Handle some of the is_ghost_exec || is_tracked_exec cases here
                // (specifically, the exec-mode cases)
                unsupported_err_unless!(len == 1, expr.span, "expected Ghost/Tracked", &args);
                let arg = &args[0];
                if get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(expr.hir_id))
                    == Some(GhostBlockAttr::Wrapper)
                {
                    let vir_arg = vir_args[0].clone();
                    match (
                        compilable_opr,
                        get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(arg.hir_id)),
                    ) {
                        (CompilableOprItem::GhostExec, Some(GhostBlockAttr::GhostWrapped)) => {
                            let exprx = ExprX::Ghost {
                                alloc_wrapper: true,
                                tracked: false,
                                expr: vir_arg.clone(),
                            };
                            return Ok(bctx.spanned_typed_new(
                                arg.span,
                                &vir_arg.typ.clone(),
                                exprx,
                            ));
                        }
                        (CompilableOprItem::TrackedExec, Some(GhostBlockAttr::TrackedWrapped)) => {
                            let exprx = ExprX::Ghost {
                                alloc_wrapper: true,
                                tracked: true,
                                expr: vir_arg.clone(),
                            };
                            return Ok(bctx.spanned_typed_new(
                                arg.span,
                                &vir_arg.typ.clone(),
                                exprx,
                            ));
                        }
                        (_, attr) => {
                            return err_span(
                                expr.span,
                                format!("unexpected ghost block attribute {:?}", attr),
                            );
                        }
                    }
                }
            }
            _ => {
                // handled later
            }
        },
        Some(VerusItem::Spec(spec_item)) => match spec_item {
            SpecItem::DecreasesWhen => {
                unsupported_err_unless!(len == 1, expr.span, "expected decreases_when", &args);
                let header = Arc::new(HeaderExprX::DecreasesWhen(vir_args[0].clone()));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Admit => {
                unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
                let f = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(false)),
                );
                return mk_expr(ExprX::AssertAssume { is_assume: true, expr: f });
            }
            SpecItem::Assume => {
                unsupported_err_unless!(len == 1, expr.span, "expected assume", args);
                return mk_expr(ExprX::AssertAssume { is_assume: true, expr: vir_args[0].clone() });
            }
            _ => unreachable!(),
        },
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger)) => {
            unsupported_err_unless!(len == 1, expr.span, "spec_cast_integer", args);
            let source_vir = vir_args[0].clone();
            let source_ty = undecorate_typ(&source_vir.typ);
            let to_ty = undecorate_typ(&expr_typ()?);
            match (&*source_ty, &*to_ty) {
                (TypX::Int(IntRange::U(_)), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::USize), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::Nat), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::Int), TypX::Int(IntRange::Nat)) => {
                    return Ok(mk_ty_clip(&to_ty, &source_vir, true));
                }
                (TypX::Int(_), TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                    return Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate));
                }
                (TypX::Char, TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                    let source_unicode =
                        mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()))?;
                    return Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate));
                }
                _ => {
                    return err_span(
                        expr.span,
                        "Verus currently only supports casts from integer types and `char` to integer types",
                    );
                }
            }
        }
        _ => (),
    }

    if is_smt_unary {
        unsupported_err_unless!(len == 1, expr.span, "expected unary op", args);
        let varg = vir_args[0].clone();
        match verus_item {
            Some(&VerusItem::UnaryOp(UnaryOpItem::SpecNeg)) => {
                let zero_const = vir::ast_util::const_int_from_u128(0);
                let zero = mk_expr(ExprX::Const(zero_const))?;
                mk_expr(ExprX::Binary(BinaryOp::Arith(ArithOp::Sub, None), zero, varg))
            }
            _ => unreachable!("internal error"),
        }
    } else if is_smt_binary {
        unsupported_err_unless!(len == 2, expr.span, "expected binary op", args);
        let lhs = vir_args[0].clone();
        let rhs = vir_args[1].clone();
        if let Some(VerusItem::BinaryOp(BinaryOpItem::Equality(
            ei @ (EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep),
        ))) = verus_item
        {
            assert!(node_substs.len() == 1);
            let t = match node_substs[0].unpack() {
                GenericArgKind::Type(ty) => {
                    mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, expr.span, &ty, false)?
                }
                _ => panic!("unexpected ext_equal type argument"),
            };
            let vop = vir::ast::BinaryOpr::ExtEq(ei == &EqualityItem::ExtEqualDeep, t);
            return Ok(mk_expr(ExprX::BinaryOpr(vop, lhs, rhs))?);
        }
        let vop = match verus_item.expect("internal error") {
            VerusItem::BinaryOp(BinaryOpItem::Equality(equality_item)) => match equality_item {
                EqualityItem::Equal | EqualityItem::SpecEq => BinaryOp::Eq(Mode::Spec),
                EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep => unreachable!(),
            },
            VerusItem::BinaryOp(BinaryOpItem::SpecOrd(spec_ord_item)) => match spec_ord_item {
                SpecOrdItem::Le => BinaryOp::Inequality(InequalityOp::Le),
                SpecOrdItem::Ge => BinaryOp::Inequality(InequalityOp::Ge),
                SpecOrdItem::Lt => BinaryOp::Inequality(InequalityOp::Lt),
                SpecOrdItem::Gt => BinaryOp::Inequality(InequalityOp::Gt),
            },
            VerusItem::BinaryOp(BinaryOpItem::Arith(arith_item)) => match arith_item {
                ArithItem::BuiltinAdd => {
                    BinaryOp::Arith(ArithOp::Add, Some(bctx.ctxt.infer_mode()))
                }
                ArithItem::BuiltinSub => {
                    BinaryOp::Arith(ArithOp::Sub, Some(bctx.ctxt.infer_mode()))
                }
                ArithItem::BuiltinMul => {
                    BinaryOp::Arith(ArithOp::Mul, Some(bctx.ctxt.infer_mode()))
                }
            },
            VerusItem::BinaryOp(BinaryOpItem::SpecArith(spec_arith_item)) => {
                match spec_arith_item {
                    SpecArithItem::Add => BinaryOp::Arith(ArithOp::Add, None),
                    SpecArithItem::Sub => BinaryOp::Arith(ArithOp::Sub, None),
                    SpecArithItem::Mul => BinaryOp::Arith(ArithOp::Mul, None),
                    SpecArithItem::EuclideanDiv => BinaryOp::Arith(ArithOp::EuclideanDiv, None),
                    SpecArithItem::EuclideanMod => BinaryOp::Arith(ArithOp::EuclideanMod, None),
                }
            }
            VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(spec_bitwise)) => match spec_bitwise {
                verus_items::SpecBitwiseItem::BitAnd => {
                    BinaryOp::Bitwise(BitwiseOp::BitAnd, Mode::Spec)
                }
                verus_items::SpecBitwiseItem::BitOr => {
                    BinaryOp::Bitwise(BitwiseOp::BitOr, Mode::Spec)
                }
                verus_items::SpecBitwiseItem::BitXor => {
                    if matches!(*vir_args[0].typ, TypX::Bool) {
                        BinaryOp::Xor
                    } else {
                        BinaryOp::Bitwise(BitwiseOp::BitXor, Mode::Spec)
                    }
                }
                verus_items::SpecBitwiseItem::Shl => BinaryOp::Bitwise(BitwiseOp::Shl, Mode::Spec),
                verus_items::SpecBitwiseItem::Shr => BinaryOp::Bitwise(BitwiseOp::Shr, Mode::Spec),
            },
            VerusItem::CompilableOpr(CompilableOprItem::Implies) => BinaryOp::Implies,
            _ => unreachable!("internal error"),
        };
        let e = mk_expr(ExprX::Binary(vop, lhs, rhs))?;
        if matches!(
            verus_item,
            Some(VerusItem::BinaryOp(BinaryOpItem::Arith(_) | BinaryOpItem::SpecArith(_)))
        ) {
            Ok(mk_ty_clip(&expr_typ()?, &e, true))
        } else {
            Ok(e)
        }
    } else if let Some(VerusItem::Chained(chained_item)) = verus_item {
        match chained_item {
            ChainedItem::Value => {
                unsupported_err_unless!(len == 1, expr.span, "spec_chained_value", &args);
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
                unsupported_err_unless!(len == 1, expr.span, "spec_chained_cmp", args);
                Ok(vir_args[0].clone())
            }
            ChainedItem::Le | ChainedItem::Lt | ChainedItem::Ge | ChainedItem::Gt => {
                unsupported_err_unless!(len == 2, expr.span, "chained inequality", &args);
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
                    ChainedItem::Le => InequalityOp::Le,
                    ChainedItem::Lt => InequalityOp::Lt,
                    ChainedItem::Ge => InequalityOp::Ge,
                    ChainedItem::Gt => InequalityOp::Gt,
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
    } else if let Some(
        VerusItem::CompilableOpr(CompilableOprItem::GhostNew)
        | VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
            SpecGhostTrackedItem::GhostView
            | SpecGhostTrackedItem::GhostBorrow
            | SpecGhostTrackedItem::TrackedView,
        )),
    ) = verus_item
    {
        assert!(vir_args.len() == 1);
        let is_ghost_new =
            verus_item == Some(&VerusItem::CompilableOpr(CompilableOprItem::GhostNew));
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Spec,
            from_mode: Mode::Spec,
            to_mode: if is_ghost_new { Mode::Proof } else { Mode::Spec },
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item, Some(VerusItem::CompilableOpr(CompilableOprItem::GhostExec))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Spec,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item, Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedNew))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(
        verus_item,
        Some(VerusItem::CompilableOpr(
            CompilableOprItem::TrackedExec | CompilableOprItem::TrackedExecBorrow
        ))
    ) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Proof,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(
        verus_item,
        Some(VerusItem::CompilableOpr(
            CompilableOprItem::TrackedGet | CompilableOprItem::TrackedBorrow
        ))
    ) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(
        verus_item,
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
            SpecGhostTrackedItem::GhostBorrowMut
        )))
    ) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Spec,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
        Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else if matches!(
        verus_item,
        Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut))
    ) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
        Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else {
        let name = name.expect("not builtin");

        let typ_args = mk_typ_args(bctx, node_substs, expr.span)?;
        let impl_paths = get_impl_paths(bctx, f, node_substs);
        let target = CallTarget::Fun(target_kind, name, typ_args, impl_paths, autospec_usage);
        Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, ExprX::Call(target, Arc::new(vir_args))))
    }
}

fn get_impl_paths<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
) -> vir::ast::BoundImplPaths {
    let tcx = bctx.ctxt.tcx;
    let mut impl_paths = Vec::new();
    if let rustc_middle::ty::FnDef(fid, _fsubsts) = tcx.type_of(f).kind() {
        let param_env = tcx.param_env(bctx.fun_id);
        // REVIEW: do we need this?
        // let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);
        let mut cur_id = Some(*fid);
        while let Some(id) = cur_id {
            let preds = tcx.predicates_of(id);
            // It would be nice to use preds.instantiate(tcx, node_substs).predicates,
            // but that loses track of the relationship between the bounds and the type parameters,
            // so we use subst instead.
            for (pred, _) in preds.predicates {
                if let PredicateKind::Clause(Clause::Trait(t)) = pred.kind().skip_binder() {
                    let lhs = t.trait_ref.substs.types().next().expect("expect lhs of trait bound");
                    let param = match lhs.kind() {
                        TyKind::Param(param) if param.name == rustc_span::symbol::kw::SelfUpper => {
                            vir::def::trait_self_type_param()
                        }
                        TyKind::Param(param) => {
                            Arc::new(crate::rust_to_vir_base::param_ty_to_vir_name(&param))
                        }
                        kind => {
                            panic!("non-type-parameter trait bound {:?} {:?}", kind, t);
                        }
                    };

                    let spred = EarlyBinder(*pred).subst(tcx, node_substs);
                    let poly_trait_refs = spred.kind().map_bound(|p| {
                        if let PredicateKind::Clause(Clause::Trait(tp)) = &p {
                            tp.trait_ref
                        } else {
                            unreachable!()
                        }
                    });
                    let candidate = tcx.codegen_select_candidate((param_env, poly_trait_refs));
                    if let Ok(impl_source) = candidate {
                        if let rustc_middle::traits::ImplSource::UserDefined(u) = impl_source {
                            let impl_path =
                                def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, u.impl_def_id);
                            impl_paths.push((param, impl_path));
                        }
                    }
                }
            }
            cur_id = preds.parent;
        }
    }
    Arc::new(impl_paths)
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
            if !matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
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
    if matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
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
            let forallx = ExprX::Forall { vars, require, ensure, proof: vir_expr };
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

fn variant_fn_get_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    f: DefId,
    span: Span,
) -> Result<vir::ast::Path, VirErr> {
    let fn_sig = tcx.fn_sig(f);
    let fn_sig = fn_sig.skip_binder();
    let inputs = fn_sig.inputs();
    if inputs.len() == 1 {
        let vir_ty = &*mid_ty_to_vir(tcx, verus_items, span, &inputs[0], false)?;
        let vir_ty = match &*vir_ty {
            TypX::Decorate(_, ty) => ty,
            _ => vir_ty,
        };
        match &*vir_ty {
            TypX::Datatype(path, _typs) => {
                return Ok(path.clone());
            }
            _ => {}
        }
    }

    return err_span(span, "invalid is_variant call (possibly a bug with is_variant macro)");
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
                typ_args.push(mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, span, &ty, false)?);
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
    verus_item: Option<&VerusItem>,
    outer_modifier: ExprModifier,
) -> Result<Vec<vir::ast::Expr>, VirErr> {
    // TODO(main_new) is calling `subst` still correct with the new API?
    let tcx = bctx.ctxt.tcx;
    let raw_inputs =
        EarlyBinder(bctx.ctxt.tcx.fn_sig(f)).subst(tcx, node_substs).skip_binder().inputs();
    assert!(raw_inputs.len() == args.len());
    args.iter()
        .zip(raw_inputs)
        .map(|(arg, raw_param)| {
            let is_mut_ref_param = match raw_param.kind() {
                TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => true,
                _ => false,
            };
            if matches!(
                verus_item,
                Some(
                    VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut)
                        | VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
                            SpecGhostTrackedItem::GhostBorrowMut
                        ))
                )
            ) {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, outer_modifier)?)
            } else if is_mut_ref_param {
                let arg_x = match &arg.kind {
                    ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => e,
                    _ => arg,
                };
                let deref_mut = match bctx.types.node_type(arg_x.hir_id).ref_mutability() {
                    Some(Mutability::Mut) => true,
                    _ => false,
                };
                let expr = expr_to_vir(bctx, arg_x, ExprModifier { addr_of: true, deref_mut })?;
                Ok(bctx.spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, ExprModifier::REGULAR)?)
            }
        })
        .collect::<Result<Vec<_>, _>>()
}
