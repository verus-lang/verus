//! Validates calls redirected by [`crate::proof_with_ast_rewrite`] to the verified
//! counterparts of functions declared `#[verus_spec(with ..)]`.
//!
//! The rewrite runs before type checking so that rustc checks the extra ghost/tracked
//! arguments. The macro emits the call a second time, without them, as the compiled copy
//! of `proof_with_callee`; `crate::rust_to_vir_expr::check_proof_with_callee` checks that
//! the two calls agree after type checking, and [`check_proof_with_args`] checks that
//! the two calls have the same arguments apart from the extra arguments.
//! Pre-type-check counterpart lookup lives in [`crate::proof_with_ast_rewrite`].

use crate::attributes::{is_unverified_stub, is_verified_counterpart};
use crate::context::{BodyCtxt, Context};
use crate::util::{err_span, err_span_vec};
use rustc_data_structures::sorted_map::SortedMap;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    Body, BodyId, Expr, ExprKind, HirId, ItemLocalId, Lifetime, LifetimeKind, Pat, PatKind, Path,
    PathSegment,
};
use rustc_hir_pretty::{Nested, PpAnn, State};
use rustc_middle::ty::{self, AssocKind, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitable};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;
use std::collections::HashMap;
use vir::ast::VirErr;

/// Checks that the verified call of a `proof_with_callee` has the receiver and arguments
/// of the compiled call, followed by the extra arguments.
/// The callees are compared by `check_proof_with_callee`.
pub(crate) fn check_proof_with_args<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    verified: &'tcx Expr<'tcx>,
    compiled: &'tcx Expr<'tcx>,
) -> Result<(), VirErr> {
    let operands = |e: &'tcx Expr<'tcx>| -> Option<Vec<&'tcx Expr<'tcx>>> {
        match &e.kind {
            ExprKind::Call(_, args) => Some(args.iter().collect()),
            ExprKind::MethodCall(_, receiver, args, _) => {
                Some(std::iter::once(*receiver).chain(args.iter()).collect())
            }
            _ => None,
        }
    };
    let (Some(ver), Some(comp)) = (operands(verified), operands(compiled)) else {
        return err_span(compiled.span, "ill-formed `proof_with!` call");
    };
    let same_kind = matches!(
        (&verified.kind, &compiled.kind),
        (ExprKind::Call(..), ExprKind::Call(..))
            | (ExprKind::MethodCall(..), ExprKind::MethodCall(..))
    );
    let bodies = &bctx.ctxt.tcx.hir_owner_nodes(compiled.hir_id.owner).bodies;
    if !same_kind
        || ver.len() < comp.len()
        || !ver.iter().zip(comp.iter()).all(|(v, c)| same_shape(bodies, v, c))
    {
        return err_span(
            compiled.span,
            "ill-formed `proof_with!` call: the two copies of the call must be the same code",
        );
    }
    Ok(())
}

/// Rejects calls to a verified counterpart other than the verified call of a
/// `proof_with_callee` marker. A direct call is unsound: it can expose extra ghost or
/// tracked outputs without requiring the corresponding inputs, and the counterpart is
/// not compiled. Generated counterparts and stubs are exempt: the stub forwards to the
/// counterpart, and a counterpart's `ensures` may name itself.
pub(crate) fn check_direct_call<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
) -> Result<(), VirErr> {
    let tcx = bctx.ctxt.tcx;
    if !is_verified_counterpart(def_attrs(tcx, f)) {
        return Ok(());
    }
    let caller = def_attrs(tcx, bctx.fun_id);
    if is_verified_counterpart(caller) || is_unverified_stub(caller) {
        return Ok(());
    }
    let marker = tcx.hir_parent_iter(expr.hir_id).find_map(|(_, node)| match node {
        rustc_hir::Node::Expr(e @ Expr { kind: ExprKind::Call(..), .. }) => Some(e),
        _ => None,
    });
    if let Some(Expr { kind: ExprKind::Call(fun, [verified, _]), .. }) = marker {
        if crate::rust_to_vir_expr::is_proof_with_callee(bctx, fun)
            && crate::rust_to_vir_expr::proof_with_verified_call(tcx, verified)
                .is_some_and(|call| call.hir_id == expr.hir_id)
        {
            return Ok(());
        }
    }
    err_span(
        expr.span,
        format!(
            "`{}` is the verified counterpart of a function declared with `with ..` \
             and cannot be called directly; call the function it belongs to and pass \
             the extra arguments with `proof_with!`",
            tcx.item_name(f)
        ),
    )
}

/// Rejects a `with ..` function whose own type or const generic is used only by the
/// ghost/tracked parameters or results. Rust could not infer such a generic from the
/// executable call, and the verified call must not infer it from ghost arguments.
pub(crate) fn check_ghost_only_generics<'tcx>(
    ctxt: &crate::context::ContextX<'tcx>,
    span: Span,
    stub: DefId,
) -> Result<(), VirErr> {
    let tcx = ctxt.tcx;
    let Some(verified) = ctxt.proof_with.find_verified_counterpart(tcx, stub) else {
        return Ok(());
    };
    let names = |def: DefId, params: Vec<u32>| -> Vec<Symbol> {
        let generics = tcx.generics_of(def);
        params.into_iter().map(|i| generics.param_at(i as usize, tcx).name).collect()
    };
    let exec_sig = tcx.fn_sig(stub).instantiate_identity().skip_binder();
    let mut exec = names(stub, params_in(exec_sig));
    for pred in tcx.param_env(stub).caller_bounds() {
        // A where clause relating several generics can let the executable call infer them.
        let params = params_in(pred);
        if params.len() > 1 {
            exec.extend(names(stub, params));
        }
    }
    let verified_sig = tcx.fn_sig(verified).instantiate_identity().skip_binder();
    let used = names(verified, params_in(verified_sig));
    for param in &tcx.generics_of(verified).own_params {
        if matches!(param.kind, ty::GenericParamDefKind::Lifetime) {
            continue;
        }
        if used.contains(&param.name) && !exec.contains(&param.name) {
            return err_span(
                span,
                format!(
                    "generic parameter `{}` is used only by ghost/tracked parameters or \
                     results, so it cannot be inferred from the executable call",
                    param.name
                ),
            );
        }
    }
    Ok(())
}

/// The indices of the type and const generic parameters that `value` mentions.
fn params_in<'tcx>(value: impl TypeVisitable<TyCtxt<'tcx>>) -> Vec<u32> {
    struct Params(Vec<u32>);
    impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for Params {
        fn visit_ty(&mut self, t: Ty<'tcx>) {
            if let TyKind::Param(p) = t.kind() {
                self.0.push(p.index);
            }
            t.super_visit_with(self)
        }

        fn visit_const(&mut self, c: ty::Const<'tcx>) {
            if let ty::ConstKind::Param(p) = c.kind() {
                self.0.push(p.index);
            }
            c.super_visit_with(self)
        }
    }
    let mut params = Params(Vec::new());
    value.visit_with(&mut params);
    params.0.sort();
    params.0.dedup();
    params.0
}

/// An override without `with` has no verified counterpart for the body Rust runs.
pub(crate) fn check_verus_spec_with_overrides<'tcx>(
    ctxt: &Context<'tcx>,
    impl_def_id: DefId,
    trait_def_id: DefId,
) -> Result<(), Vec<VirErr>> {
    let tcx = ctxt.tcx;
    for item in tcx.associated_items(impl_def_id).in_definition_order() {
        if !matches!(item.kind, AssocKind::Fn { .. }) {
            continue;
        }
        let Some(decl) = item.trait_item_def_id() else { continue };
        if tcx.parent(decl) == trait_def_id
            && is_unverified_stub(def_attrs(tcx, decl))
            && !is_unverified_stub(def_attrs(tcx, item.def_id))
        {
            return err_span_vec(
                tcx.def_span(item.def_id),
                format!(
                    "cannot override `{}`: a trait method declared with `#[verus_spec(with ...)]` \
                     cannot be overridden without repeating the `with` clause",
                    tcx.def_path_str(decl)
                ),
            );
        }
    }
    Ok(())
}

fn def_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [rustc_hir::Attribute] {
    match def_id.as_local() {
        Some(local) => tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
        None => tcx.attrs_for_def(def_id),
    }
}

/// Whether two expressions are the same source code, resolved the same way.
///
/// The macro emits both copies from the same tokens. A hand-written marker could pair
/// different calls, which would make the conformance check compare the redirected call
/// against an unrelated one, or verify a call the compiled program does not make. The copies are compared as pretty-printed text, which
/// covers their structure, names and literals. Printing does not show what a name
/// refers to, and hygiene can make equal names resolve differently, so the resolved
/// paths, lifetimes and bindings are compared too.
fn same_shape<'tcx>(
    bodies: &SortedMap<ItemLocalId, &'tcx Body<'tcx>>,
    a: &'tcx Expr<'tcx>,
    b: &'tcx Expr<'tcx>,
) -> bool {
    let print = |e| rustc_hir_pretty::expr_to_string(&Bodies(bodies), e);
    let resolutions = |e| {
        let mut r = Resolutions { bodies, resolved: Vec::new(), bound: HashMap::new() };
        r.visit_expr(e);
        r.resolved
    };
    print(a) == print(b) && resolutions(a) == resolutions(b)
}

/// Prints closure and inline-const bodies from the owner being rewritten.
struct Bodies<'a, 'tcx>(&'a SortedMap<ItemLocalId, &'tcx Body<'tcx>>);

impl PpAnn for Bodies<'_, '_> {
    fn nested(&self, state: &mut State<'_>, nested: Nested) {
        let body = |id: BodyId| self.0[&id.hir_id.local_id];
        let text = match nested {
            Nested::Body(id) => rustc_hir_pretty::expr_to_string(self, body(id).value),
            Nested::BodyParamPat(id, i) => {
                rustc_hir_pretty::pat_to_string(self, body(id).params[i].pat)
            }
            // The two copies' items are distinct definitions, so a nested item
            // (including a `use`) makes the copies differ.
            Nested::Item(id) => format!("{id:?}"),
            _ => return,
        };
        state.word(text);
    }
}

struct Resolutions<'a, 'tcx> {
    bodies: &'a SortedMap<ItemLocalId, &'tcx Body<'tcx>>,
    /// A variable bound in the tree is `Ok` of its binding order.
    resolved: Vec<Res<Result<usize, HirId>>>,
    bound: HashMap<HirId, usize>,
}

impl Resolutions<'_, '_> {
    fn push(&mut self, res: Res) {
        // Each copy is lowered separately, so a variable bound inside it has a different
        // `HirId` in each copy and is compared by binding order (`Ok`). A variable bound
        // outside must be the same one in both copies, so its `HirId` is kept (`Err`).
        let res = res.map_id(|id| self.bound.get(&id).copied().ok_or(id));
        self.resolved.push(res);
    }
}

impl<'tcx> Visitor<'tcx> for Resolutions<'_, 'tcx> {
    fn visit_nested_body(&mut self, id: BodyId) {
        let body = self.bodies[&id.hir_id.local_id];
        intravisit::walk_body(self, body);
    }

    fn visit_pat(&mut self, p: &'tcx Pat<'tcx>) {
        if let PatKind::Binding(_, id, ..) = p.kind {
            let n = self.bound.len();
            self.bound.insert(id, n);
        }
        intravisit::walk_pat(self, p);
    }

    /// Other lifetimes are determined by their printed names.
    fn visit_lifetime(&mut self, l: &'tcx Lifetime) {
        if let LifetimeKind::Param(id) = l.kind {
            self.push(Res::Def(DefKind::LifetimeParam, id.to_def_id()));
        }
    }

    fn visit_path(&mut self, path: &Path<'tcx>, _id: HirId) {
        self.push(path.res);
        intravisit::walk_path(self, path);
    }

    fn visit_path_segment(&mut self, s: &'tcx PathSegment<'tcx>) {
        self.push(s.res);
        intravisit::walk_path_segment(self, s);
    }
}
