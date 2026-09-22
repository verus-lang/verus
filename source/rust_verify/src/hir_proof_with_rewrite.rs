//! Rewrites `proof_with((extra, ..), f(args))` to call the verified counterpart of
//! `f`. The proc macro cannot resolve aliases or method receivers during expansion,
//! so this pass runs after name resolution. It runs before type checking so rustc
//! checks the types, borrows, and lifetimes of the extra ghost or tracked arguments.
//!
//! # Free functions and inherent methods
//!
//! The stub and counterpart are siblings, so [`counterpart_of`] finds the prefixed
//! name under their common parent.
//!
//! ```ignore
//! // #[verus_spec(with Tracked(t): Tracked<u8>)] fn f(x: u8) -> u8 { x }
//!
//! #[verus::internal(unverified_stub)]
//! fn f(x: u8) -> u8 { unimplemented!() }
//!
//! #[verus::internal(verified_with)]
//! fn _VERUS_WITH_f(x: u8, verus_tmp_t: Tracked<u8>) -> u8 { x }
//!
//! // proof_with!{t} let y = f(x);
//! let y = proof_with((t,), f(x));
//! let y = _VERUS_WITH_f(x, t);
//! ```
//!
//! # Trait methods
//!
//! A counterpart cannot be added to an external trait, and adding one to a local
//! trait would change every implementation. The proc macro instead generates two
//! companion subtraits: `_VERUS_WITH_TRAIT_Tr` declares the counterparts and is
//! blanket-implemented for every implementor of `Tr`, so a call needs no extra bound;
//! `_VERUS_WITH_IMPL_TRAIT_Tr` carries the body of an implementation that
//! overrides the method. [`Ctxt::companions_of_trait`] locates the declaring trait's
//! method, while [`Ctxt::companions_declaring`] handles calls whose trait is
//! unresolved here.
//!
//! ```ignore
//! // trait Tr { #[verus_spec(with Tracked(t): Tracked<u8>)] fn m(&self); }
//! // impl Tr for S { .. }
//!
//! trait Tr {
//!     #[verus::internal(unverified_stub)]
//!     fn m(&self);
//! }
//! #[verus::internal(verified_trait)]
//! trait _VERUS_WITH_TRAIT_Tr: Tr {
//!     #[verus::internal(verified_with)]
//!     #[verifier::external_body]
//!     fn _VERUS_WITH_m(&self, verus_tmp_t: Tracked<u8>) { unimplemented!() }
//! }
//! impl<_VerusSelf: Tr + ?Sized> _VERUS_WITH_TRAIT_Tr for _VerusSelf {}
//!
//! trait _VERUS_WITH_IMPL_TRAIT_Tr: Tr {
//!     #[verus::internal(verified_with)]
//!     #[verifier::external_body]
//!     fn _VERUS_WITH_IMPL_m(&self, verus_tmp_t: Tracked<u8>) { unimplemented!() }
//! }
//!
//! impl Tr for S { fn m(&self) { unimplemented!() } }
//! impl _VERUS_WITH_IMPL_TRAIT_Tr for S {
//!     fn _VERUS_WITH_IMPL_m(&self, verus_tmp_t: Tracked<u8>) {}
//! }
//!
//! // proof_with!{t} s.m();
//! proof_with((t,), s.m());
//! s._VERUS_WITH_m(t);
//! ```
//!
//! The call always names `_VERUS_WITH_m`, so it resolves through the blanket
//! impl. `fn_call_to_vir` then redirects it to `_VERUS_WITH_IMPL_m` when the
//! receiver's type overrides the method, so the implementation's own contract
//! applies at static dispatch.
//!
//! # External functions
//!
//! The counterpart belongs to the local `assume_specification`, and
//! [`external_target_map`] indexes it by the external function named in the
//! specification body's trailing call.
//!
//! ```ignore
//! // #[verifier::external_fn_specification]
//! // #[verus_spec(with Tracked(t): Tracked<u8>)]
//! // fn ext_spec(x: u8) -> u8 { ext(x) }
//!
//! #[verifier::external_fn_specification]
//! #[verus::internal(unverified_stub)]
//! fn ext_spec(x: u8) -> u8 { ext(x) }
//!
//! #[verus::internal(verified_with)]
//! fn _VERUS_WITH_ext_spec(
//!     x: u8,
//!     verus_tmp_t: Tracked<u8>,
//! ) -> u8 { unimplemented!() }
//!
//! // proof_with!{t} let z = ext(x);
//! let z = proof_with((t,), ext(x));
//! let z = _VERUS_WITH_ext_spec(x, t);
//! ```

use crate::attributes::{Attr, parse_attrs_opt};
use rustc_data_structures::steal::Steal;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{
    Arm, Block, Expr, ExprField, ExprKind, ItemLocalId, LetExpr, MaybeOwner, Node,
    OwnerNode, PathSegment, QPath, Stmt, StmtKind, StructTailExpr,
};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Symbol;

/// This prefix must match `builtin_macros::attr_rewrite::WITH`.
const WITH_PREFIX: &str = "_VERUS_WITH";
/// This prefix must match `builtin_macros::unerased_proxies::VERUS_UNERASED_PROXY`.
const UNERASED_PROXY_PREFIX: &str = "VERUS_UNERASED_PROXY__";

#[inline]
fn with_name(name: Symbol) -> Symbol {
    Symbol::intern(&format!("{WITH_PREFIX}_{name}"))
}

/// Rewriting a marked call needs the whole crate -- the companion traits and the
/// `assume_specification` stubs of every module -- but HIR is lowered one owner at
/// a time. Every owner is therefore lowered on the first call and kept, so `lower`
/// is called exactly once per definition, as the query itself would, and the crate
/// is indexed once.
///
/// A definition the crate walk did not reach is lowered on demand; the index is
/// ready by then, so the rewrite is the same either way.
pub(crate) fn lower_to_hir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    lower: fn(TyCtxt<'tcx>, LocalDefId) -> MaybeOwner<'tcx>,
) -> MaybeOwner<'tcx> {
    // Lowering an owner lowers the owners it was nested in, to read their children.
    if partial_lowering() {
        return lower_once(tcx, def_id, lower);
    }
    let crate_ = crate_owners(tcx, lower);
    let owner = match crate_.owners.get(def_id).copied().flatten() {
        Some(owner) => from_static_owner(owner),
        None => lower(tcx, def_id),
    };
    let MaybeOwner::Owner(inner_owner) = owner else {
        return owner;
    };
    let ctxt = Ctxt {
        tcx,
        owners: from_static_owners(crate_.indexed),
    };
    rewrite_owner(&ctxt, inner_owner, def_id).unwrap_or(owner)
}

/// The owners of the crate being compiled, lowered and indexed once.
///
/// The lowered owners are held for the rest of the session, so they are given the
/// `'static` lifetime; `CRATE_OWNERS` records which `TyCtxt` they were lowered by,
/// which is what makes reading them back as `'tcx` sound.
struct CrateOwners {
    owners: &'static IndexVec<LocalDefId, Option<MaybeOwner<'static>>>,
    /// The same owners, read by definition and without the holes, for `Ctxt`.
    indexed: &'static IndexVec<LocalDefId, MaybeOwner<'static>>,
}

/// `CrateOwners` holds HIR, which is neither `Send` nor `Sync`, so the table is
/// kept as an address and read back by the thread that asks for the `TyCtxt` that
/// built it.
static CRATE_OWNERS: std::sync::Mutex<Option<(usize, usize)>> = std::sync::Mutex::new(None);

thread_local! {
    /// The owners lowered so far, while `crate_owners` is filling them in.
    static PARTIAL: std::cell::RefCell<Option<IndexVec<LocalDefId, Option<MaybeOwner<'static>>>>> =
        const { std::cell::RefCell::new(None) };
}

fn partial_lowering() -> bool {
    PARTIAL.with(|partial| partial.borrow().is_some())
}

/// Lowers `def_id` unless `crate_owners` already did: the default lowering steals
/// the AST of a definition, so it may not be run twice for the same one.
fn lower_once<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    lower: fn(TyCtxt<'tcx>, LocalDefId) -> MaybeOwner<'tcx>,
) -> MaybeOwner<'tcx> {
    let lowered = PARTIAL.with(|partial| {
        partial.borrow().as_ref().and_then(|owners| owners.get(def_id).copied().flatten())
    });
    if let Some(owner) = lowered {
        return from_static_owner(owner);
    }
    let owner = lower(tcx, def_id);
    PARTIAL.with(|partial| {
        if let Some(owners) = partial.borrow_mut().as_mut() {
            *owners.ensure_contains_elem(def_id, || None) = Some(to_static_owner(owner));
        }
    });
    owner
}

/// Collects the owners declared by an owner: the items of a module, of an
/// implementation, of a trait or of an `extern` block, and, through `parenting`,
/// the items declared inside a body.
fn nested_owners<'tcx>(owner: &rustc_hir::OwnerInfo<'tcx>, pending: &mut Vec<LocalDefId>) {
    match owner.node() {
        OwnerNode::Crate(module) => {
            pending.extend(module.item_ids.iter().map(|id| id.owner_id.def_id))
        }
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Mod(_, module) => {
                pending.extend(module.item_ids.iter().map(|id| id.owner_id.def_id))
            }
            rustc_hir::ItemKind::Impl(impl_) => {
                pending.extend(impl_.items.iter().map(|id| id.owner_id.def_id))
            }
            rustc_hir::ItemKind::Trait { items, .. } => {
                pending.extend(items.iter().map(|id| id.owner_id.def_id))
            }
            rustc_hir::ItemKind::ForeignMod { items, .. } => {
                pending.extend(items.iter().map(|id| id.owner_id.def_id))
            }
            _ => {}
        },
        _ => {}
    }
    // `parenting` only records an owner declared below the root node of this one,
    // so the items above are not in it, in no fixed order.
    let nested = std::cell::RefCell::new(pending);
    owner.parenting.items().all(|(nested_id, _)| {
        nested.borrow_mut().push(*nested_id);
        true
    });
}

/// Fills a definition that lowering did not produce an owner for.
fn non_owner<'tcx>() -> MaybeOwner<'tcx> {
    MaybeOwner::NonOwner(rustc_hir::HirId::INVALID)
}

fn crate_owners<'tcx>(
    tcx: TyCtxt<'tcx>,
    lower: fn(TyCtxt<'tcx>, LocalDefId) -> MaybeOwner<'tcx>,
) -> &'static CrateOwners {
    // `TyCtxt` derefs to a reference, so the `GlobalCtxt` has to be reached twice.
    let gcx = std::ptr::from_ref(&**tcx) as usize;
    let mut cached = CRATE_OWNERS.lock().expect("CRATE_OWNERS");
    if let Some((cached_gcx, crate_)) = *cached {
        if cached_gcx == gcx {
            return unsafe { &*(crate_ as *const CrateOwners) };
        }
    }

    PARTIAL.with(|partial| *partial.borrow_mut() = Some(IndexVec::new()));
    // Only the definitions the crate is made of are lowered here. Lowering one that
    // is not an owner of its own -- a generic parameter, a field, a nested use tree
    // -- reads the owner it belongs to through the query, which would cache it
    // before the index it has to be rewritten with exists.
    let mut pending = vec![rustc_span::def_id::CRATE_DEF_ID];
    while let Some(def_id) = pending.pop() {
        if let MaybeOwner::Owner(owner) = lower_once(tcx, def_id, lower) {
            nested_owners(owner, &mut pending);
        }
    }
    let lowered = PARTIAL.with(|partial| partial.borrow_mut().take()).expect("PARTIAL");

    let mut indexed: IndexVec<LocalDefId, MaybeOwner<'static>> = IndexVec::new();
    for (def_id, owner) in lowered.iter_enumerated() {
        *indexed.ensure_contains_elem(def_id, non_owner) = owner.unwrap_or_else(non_owner);
    }
    let owners = Box::leak(Box::new(lowered));
    let indexed: &'static IndexVec<LocalDefId, MaybeOwner<'static>> = Box::leak(Box::new(indexed));
    let crate_: &'static CrateOwners = Box::leak(Box::new(CrateOwners { owners, indexed }));
    *cached = Some((gcx, std::ptr::from_ref(crate_) as usize));
    crate_
}

/// Sound because `CRATE_OWNERS` only hands these back for the `TyCtxt` that lowered
/// them, whose arena outlives the query that is asking.
fn to_static_owner<'tcx>(owner: MaybeOwner<'tcx>) -> MaybeOwner<'static> {
    unsafe { std::mem::transmute(owner) }
}

fn from_static_owner<'tcx>(owner: MaybeOwner<'static>) -> MaybeOwner<'tcx> {
    unsafe { std::mem::transmute(owner) }
}

fn from_static_owners<'tcx>(
    owners: &'static IndexVec<LocalDefId, MaybeOwner<'static>>,
) -> &'tcx IndexVec<LocalDefId, MaybeOwner<'tcx>> {
    unsafe { std::mem::transmute(owners) }
}

struct Ctxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Local HIR must be read here because `tcx` would re-enter `lower_to_hir`.
    owners: &'a IndexVec<LocalDefId, MaybeOwner<'tcx>>,
}

fn owner_attrs<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<&'tcx [rustc_hir::Attribute]> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    Some(owner.attrs.get(ItemLocalId::ZERO))
}

/// Local attributes must bypass `tcx` to avoid re-entering `lower_to_hir`.
fn def_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Option<&'tcx [rustc_hir::Attribute]> {
    match def_id.as_local() {
        Some(local) => owner_attrs(owners, local),
        None => Some(tcx.attrs_for_def(def_id)),
    }
}

/// Local children must bypass `module_children` and `associated_items`, which
/// re-enter `lower_to_hir`.
fn local_child_fn<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    parent: LocalDefId,
    name: Symbol,
) -> Option<LocalDefId> {
    let MaybeOwner::Owner(owner) = owners.get(parent)? else {
        return None;
    };
    let children: Vec<LocalDefId> = match owner.node() {
        OwnerNode::Crate(module) => module.item_ids.iter().map(|id| id.owner_id.def_id).collect(),
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Mod(_, module) => {
                module.item_ids.iter().map(|id| id.owner_id.def_id).collect()
            }
            rustc_hir::ItemKind::Impl(impl_) => {
                impl_.items.iter().map(|id| id.owner_id.def_id).collect()
            }
            rustc_hir::ItemKind::Trait { items, .. } => {
                items.iter().map(|id| id.owner_id.def_id).collect()
            }
            _ => return None,
        },
        _ => return None,
    };
    children.into_iter().find(|child| local_fn_name(owners, *child) == Some(name))
}

fn local_fn_name<'tcx>(
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: LocalDefId,
) -> Option<Symbol> {
    let MaybeOwner::Owner(owner) = owners.get(def_id)? else {
        return None;
    };
    match owner.node() {
        OwnerNode::Item(item) => match &item.kind {
            rustc_hir::ItemKind::Fn { ident, .. } => Some(ident.name),
            _ => None,
        },
        OwnerNode::ImplItem(item) => match &item.kind {
            rustc_hir::ImplItemKind::Fn(..) => Some(item.ident.name),
            _ => None,
        },
        OwnerNode::TraitItem(item) => match &item.kind {
            rustc_hir::TraitItemKind::Fn(..) => Some(item.ident.name),
            _ => None,
        },
        _ => None,
    }
}

impl<'tcx> Ctxt<'_, 'tcx> {
    fn attrs(&self, def_id: DefId) -> Option<&'tcx [rustc_hir::Attribute]> {
        def_attrs(self.tcx, self.owners, def_id)
    }

    /// The diagnostic attribute is read directly because the Verus item map is not
    /// available yet, and `is_diagnostic_item` hangs on a local item by re-entering
    /// `lower_to_hir`. This also handles a builtin embedded as a module.
    fn is_proof_with_marker(&self, callee: &Expr<'tcx>) -> bool {
        let ExprKind::Path(QPath::Resolved(None, path)) = &callee.kind else {
            return false;
        };
        let Res::Def(DefKind::Fn, def_id) = path.res else {
            return false;
        };
        let Some(attrs) = self.attrs(def_id) else {
            return false;
        };
        attrs.iter().any(|attr| match attr {
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::RustcDiagnosticItem(
                name,
            )) => {
                name.as_str() == "verus::verus_builtin::proof_with"
                    || name.as_str() == "verus::verus_builtin::proof_with_ret"
            }
            _ => false,
        })
    }

    fn is_verified_counterpart(&self, def_id: DefId) -> bool {
        let Some(attrs) = self.attrs(def_id) else {
            return false;
        };
        parse_attrs_opt(attrs, None).iter().any(|a| matches!(a, Attr::VerifiedWith))
    }

    fn is_unverified_stub(&self, def_id: DefId) -> bool {
        let Some(attrs) = self.attrs(def_id) else {
            return false;
        };
        parse_attrs_opt(attrs, None).iter().any(|a| matches!(a, Attr::UnverifiedStub))
    }

    fn verified_counterpart(&self, def_id: DefId) -> Option<DefId> {
        if !self.is_unverified_stub(def_id) {
            return None;
        }
        counterpart_of(self.tcx, self.owners, def_id)
    }

}

fn rewrite_owner<'tcx>(
    ctxt: &Ctxt<'_, 'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    def_id: LocalDefId,
) -> Option<MaybeOwner<'tcx>> {
    let tcx = ctxt.tcx;
    let mut bodies = inner_owner.nodes.bodies.clone();
    let mut nodes = inner_owner.nodes.nodes.clone();
    let mut changed = false;
    let in_counterpart = ctxt.is_verified_counterpart(def_id.to_def_id())
        || ctxt.is_unverified_stub(def_id.to_def_id());

    for (local_id, body) in inner_owner.nodes.bodies.iter() {
        let mut folder = Folder {
            ctxt,
            updates: Vec::new(),
            reparents: Vec::new(),
            in_counterpart,
        };
        let Some(value) = folder.fold_expr(body.value) else {
            continue;
        };
        for (id, node) in folder.updates.iter() {
            if let Some(parented) = nodes.get_mut(*id) {
                parented.node = *node;
            }
        }
        // Reparenting prevents upward HIR walks from reaching the removed marker.
        // Abandoned entries are harmless because traversals start from body trees.
        for (id, reparent) in folder.reparents.iter() {
            let parent = match reparent {
                Reparent::To(parent) => Some(*parent),
                Reparent::AdoptFrom(other) => nodes.get(*other).map(|p| p.parent),
            };
            if let (Some(parented), Some(parent)) = (nodes.get_mut(*id), parent) {
                parented.parent = parent;
            }
        }
        let body = tcx.hir_arena.alloc(rustc_hir::Body { params: body.params, value });
        bodies[local_id] = body;
        changed = true;
    }
    if !changed {
        return None;
    }

    let nodes = rustc_hir::OwnerNodes { opt_hash: inner_owner.nodes.opt_hash, nodes, bodies };
    let owner_info = mk_owner(tcx, inner_owner, nodes);
    Some(MaybeOwner::Owner(owner_info))
}

fn mk_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    inner_owner: &'tcx rustc_hir::OwnerInfo<'tcx>,
    nodes: rustc_hir::OwnerNodes<'tcx>,
) -> &'tcx rustc_hir::OwnerInfo<'tcx> {
    tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
        nodes,
        parenting: inner_owner.parenting.clone(),
        attrs: rustc_hir::AttributeMap {
            map: inner_owner.attrs.map.clone(),
            opt_hash: inner_owner.attrs.opt_hash,
            define_opaque: inner_owner.attrs.define_opaque,
        },
        trait_map: inner_owner.trait_map.clone(),
        children: inner_owner.children.clone(),
        opt_hash: inner_owner.opt_hash,
        delayed_lints: Steal::new(Vec::new().into_boxed_slice()),
    })
}

enum Reparent {
    To(ItemLocalId),
    /// The replacement call inherits the removed marker's parent during write-back.
    AdoptFrom(ItemLocalId),
}

/// Immutable HIR requires reallocating each ancestor of a rewritten expression.
struct Folder<'a, 'tcx> {
    ctxt: &'a Ctxt<'a, 'tcx>,
    updates: Vec<(ItemLocalId, Node<'tcx>)>,
    reparents: Vec<(ItemLocalId, Reparent)>,
    /// A counterpart may name itself in its generated `ensures`, and the stub it
    /// replaces forwards to it.
    in_counterpart: bool,
}

impl<'a, 'tcx> Folder<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn mk_expr(&mut self, old: &'tcx Expr<'tcx>, kind: ExprKind<'tcx>) -> &'tcx Expr<'tcx> {
        let new: &'tcx Expr<'tcx> =
            self.tcx().hir_arena.alloc(Expr { hir_id: old.hir_id, kind, span: old.span });
        self.updates.push((old.hir_id.local_id, Node::Expr(new)));
        new
    }

    fn alloc_exprs(&self, exprs: Vec<Expr<'tcx>>) -> &'tcx [Expr<'tcx>] {
        self.tcx().hir_arena.alloc_slice(&exprs)
    }

    fn fold_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        self.reject_direct_call(expr);
        if let Some(new) = self.try_rewrite_proof_with(expr) {
            return Some(new);
        }
        let kind = match &expr.kind {
            ExprKind::Array(elems) => ExprKind::Array(self.fold_exprs(elems)?),
            ExprKind::Tup(elems) => ExprKind::Tup(self.fold_exprs(elems)?),
            ExprKind::Call(callee, args) => {
                let new_callee = self.fold_expr(callee);
                let new_args = self.fold_exprs(args);
                if new_callee.is_none() && new_args.is_none() {
                    return None;
                }
                ExprKind::Call(new_callee.unwrap_or(callee), new_args.unwrap_or(args))
            }
            ExprKind::MethodCall(seg, receiver, args, span) => {
                let new_receiver = self.fold_expr(receiver);
                let new_args = self.fold_exprs(args);
                if new_receiver.is_none() && new_args.is_none() {
                    return None;
                }
                ExprKind::MethodCall(
                    seg,
                    new_receiver.unwrap_or(receiver),
                    new_args.unwrap_or(args),
                    *span,
                )
            }
            ExprKind::Use(e, span) => ExprKind::Use(self.fold_expr(e)?, *span),
            ExprKind::Binary(op, lhs, rhs) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::Binary(*op, new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs))
            }
            ExprKind::Unary(op, e) => ExprKind::Unary(*op, self.fold_expr(e)?),
            ExprKind::Cast(e, ty) => ExprKind::Cast(self.fold_expr(e)?, ty),
            ExprKind::Type(e, ty) => ExprKind::Type(self.fold_expr(e)?, ty),
            ExprKind::DropTemps(e) => ExprKind::DropTemps(self.fold_expr(e)?),
            ExprKind::Let(let_expr) => {
                let init = self.fold_expr(let_expr.init)?;
                ExprKind::Let(self.tcx().hir_arena.alloc(LetExpr { init, ..**let_expr }))
            }
            ExprKind::If(cond, then, els) => {
                let new_cond = self.fold_expr(cond);
                let new_then = self.fold_expr(then);
                let new_els = els.and_then(|e| self.fold_expr(e));
                if new_cond.is_none() && new_then.is_none() && new_els.is_none() {
                    return None;
                }
                ExprKind::If(new_cond.unwrap_or(cond), new_then.unwrap_or(then), new_els.or(*els))
            }
            ExprKind::Loop(block, label, source, span) => {
                ExprKind::Loop(self.fold_block(block)?, *label, *source, *span)
            }
            ExprKind::Match(scrutinee, arms, source) => {
                let new_scrutinee = self.fold_expr(scrutinee);
                let new_arms = self.fold_arms(arms);
                if new_scrutinee.is_none() && new_arms.is_none() {
                    return None;
                }
                ExprKind::Match(
                    new_scrutinee.unwrap_or(scrutinee),
                    new_arms.unwrap_or(arms),
                    *source,
                )
            }
            ExprKind::Block(block, label) => ExprKind::Block(self.fold_block(block)?, *label),
            ExprKind::Assign(lhs, rhs, span) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::Assign(new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs), *span)
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                let new_lhs = self.fold_expr(lhs);
                let new_rhs = self.fold_expr(rhs);
                if new_lhs.is_none() && new_rhs.is_none() {
                    return None;
                }
                ExprKind::AssignOp(*op, new_lhs.unwrap_or(lhs), new_rhs.unwrap_or(rhs))
            }
            ExprKind::Field(e, ident) => ExprKind::Field(self.fold_expr(e)?, *ident),
            ExprKind::Index(base, idx, span) => {
                let new_base = self.fold_expr(base);
                let new_idx = self.fold_expr(idx);
                if new_base.is_none() && new_idx.is_none() {
                    return None;
                }
                ExprKind::Index(new_base.unwrap_or(base), new_idx.unwrap_or(idx), *span)
            }
            ExprKind::AddrOf(kind, m, e) => ExprKind::AddrOf(*kind, *m, self.fold_expr(e)?),
            ExprKind::Break(dest, e) => ExprKind::Break(*dest, Some(self.fold_expr((*e)?)?)),
            ExprKind::Ret(e) => ExprKind::Ret(Some(self.fold_expr((*e)?)?)),
            ExprKind::Become(e) => ExprKind::Become(self.fold_expr(e)?),
            ExprKind::Struct(qpath, fields, tail) => {
                let new_fields = self.fold_fields(fields);
                let new_tail = match tail {
                    StructTailExpr::Base(base) => self.fold_expr(base).map(StructTailExpr::Base),
                    StructTailExpr::None
                    | StructTailExpr::DefaultFields(_)
                    | StructTailExpr::NoneWithError(_) => None,
                };
                if new_fields.is_none() && new_tail.is_none() {
                    return None;
                }
                ExprKind::Struct(qpath, new_fields.unwrap_or(fields), new_tail.unwrap_or(*tail))
            }
            ExprKind::Repeat(e, count) => ExprKind::Repeat(self.fold_expr(e)?, count),
            ExprKind::Yield(e, source) => ExprKind::Yield(self.fold_expr(e)?, *source),
            ExprKind::UnsafeBinderCast(kind, e, ty) => {
                ExprKind::UnsafeBinderCast(*kind, self.fold_expr(e)?, *ty)
            }
            // Const blocks have their own owners, and closure bodies have separate
            // entries in the enclosing owner's body map.
            ExprKind::ConstBlock(..)
            | ExprKind::Closure(..)
            | ExprKind::Lit(..)
            | ExprKind::Path(..)
            | ExprKind::Continue(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::OffsetOf(..)
            | ExprKind::Err(..) => return None,
        };
        Some(self.mk_expr(expr, kind))
    }

    /// Direct calls are unsound because they can expose extra ghost or tracked
    /// outputs without requiring the corresponding inputs. Generated stubs and
    /// counterparts are exempt: their bodies are not verified.
    ///
    /// Method calls resolve after this pass and are rejected in `rust_to_vir`.
    fn reject_direct_call(&self, expr: &'tcx Expr<'tcx>) {
        if self.in_counterpart {
            return;
        }
        let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
            return;
        };
        let Some(def_id) = path.res.opt_def_id() else {
            return;
        };
        if !self.ctxt.is_verified_counterpart(def_id) {
            return;
        }
        self.tcx().dcx().span_err(
            expr.span,
            format!(
                "`{}` is the verified counterpart of a function declared with `with ..` \
                 and cannot be called directly; call the function it belongs to and pass \
                 the extra arguments with `proof_with!`",
                self.tcx().item_name(def_id)
            ),
        );
    }

    fn fold_exprs(&mut self, exprs: &'tcx [Expr<'tcx>]) -> Option<&'tcx [Expr<'tcx>]> {
        let mut new: Option<Vec<Expr<'tcx>>> = None;
        for (i, e) in exprs.iter().enumerate() {
            if let Some(folded) = self.fold_expr(e) {
                new.get_or_insert_with(|| exprs.to_vec())[i] = *folded;
            }
        }
        new.map(|v| self.alloc_exprs(v))
    }

    fn fold_fields(&mut self, fields: &'tcx [ExprField<'tcx>]) -> Option<&'tcx [ExprField<'tcx>]> {
        let mut new: Option<Vec<ExprField<'tcx>>> = None;
        for (i, f) in fields.iter().enumerate() {
            if let Some(folded) = self.fold_expr(f.expr) {
                new.get_or_insert_with(|| fields.to_vec())[i].expr = folded;
            }
        }
        new.map(|v| &*self.tcx().hir_arena.alloc_slice(&v))
    }

    fn fold_arms(&mut self, arms: &'tcx [Arm<'tcx>]) -> Option<&'tcx [Arm<'tcx>]> {
        let mut new: Option<Vec<Arm<'tcx>>> = None;
        for (i, arm) in arms.iter().enumerate() {
            let new_guard = arm.guard.and_then(|g| self.fold_expr(g));
            let new_body = self.fold_expr(arm.body);
            if new_guard.is_none() && new_body.is_none() {
                continue;
            }
            let arm = &mut new.get_or_insert_with(|| arms.to_vec())[i];
            if let Some(guard) = new_guard {
                arm.guard = Some(guard);
            }
            if let Some(body) = new_body {
                arm.body = body;
            }
        }
        new.map(|v| &*self.tcx().hir_arena.alloc_slice(&v))
    }

    fn fold_block(&mut self, block: &'tcx Block<'tcx>) -> Option<&'tcx Block<'tcx>> {
        let mut new_stmts: Option<Vec<Stmt<'tcx>>> = None;
        for (i, stmt) in block.stmts.iter().enumerate() {
            if let Some(folded) = self.fold_stmt(stmt) {
                new_stmts.get_or_insert_with(|| block.stmts.to_vec())[i] = folded;
            }
        }
        let new_expr = block.expr.and_then(|e| self.fold_expr(e));
        if new_stmts.is_none() && new_expr.is_none() {
            return None;
        }
        let stmts = match new_stmts {
            Some(v) => self.tcx().hir_arena.alloc_slice(&v),
            None => block.stmts,
        };
        let new: &'tcx Block<'tcx> =
            self.tcx().hir_arena.alloc(Block { stmts, expr: new_expr.or(block.expr), ..*block });
        self.updates.push((block.hir_id.local_id, Node::Block(new)));
        Some(new)
    }

    fn fold_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) -> Option<Stmt<'tcx>> {
        let kind = match &stmt.kind {
            StmtKind::Let(let_stmt) => {
                let init = let_stmt.init.and_then(|e| self.fold_expr(e));
                let els = let_stmt.els.and_then(|b| self.fold_block(b));
                if init.is_none() && els.is_none() {
                    return None;
                }
                let new = self.tcx().hir_arena.alloc(rustc_hir::LetStmt {
                    init: init.or(let_stmt.init),
                    els: els.or(let_stmt.els),
                    ..**let_stmt
                });
                StmtKind::Let(new)
            }
            StmtKind::Expr(e) => StmtKind::Expr(self.fold_expr(e)?),
            StmtKind::Semi(e) => StmtKind::Semi(self.fold_expr(e)?),
            StmtKind::Item(_) => return None,
        };
        let new = Stmt { kind, ..*stmt };
        self.updates.push((stmt.hir_id.local_id, Node::Stmt(self.tcx().hir_arena.alloc(new))));
        Some(new)
    }

    fn try_rewrite_proof_with(&mut self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Call(marker, marker_args) = &expr.kind else {
            return None;
        };
        if marker_args.len() != 2 || !self.ctxt.is_proof_with_marker(marker) {
            return None;
        }

        let raw_extra_args: &'tcx [Expr<'tcx>] = match &marker_args[0].kind {
            ExprKind::Tup(elems) => elems,
            _ => std::slice::from_ref(&marker_args[0]),
        };
        let extra_args: Vec<Expr<'tcx>> = raw_extra_args
            .iter()
            .map(|e| match self.fold_expr(e) {
                Some(folded) => *folded,
                None => *e,
            })
            .collect();
        let call = &marker_args[1];
        let call = self.fold_expr(call).unwrap_or(call);

        let extra_ids: Vec<ItemLocalId> = extra_args.iter().map(|e| e.hir_id.local_id).collect();

        let new_kind = match &call.kind {
            ExprKind::Call(callee, args) => {
                let mut new_args = args.to_vec();
                new_args.extend(extra_args);
                let verified_callee = self.redirect_callee(callee)?;
                ExprKind::Call(verified_callee, self.alloc_exprs(new_args))
            }
            ExprKind::MethodCall(seg, receiver, args, span) => {
                let mut new_args = args.to_vec();
                new_args.extend(extra_args);
                let new_seg = self.rewrite_method(seg)?;
                ExprKind::MethodCall(new_seg, receiver, self.alloc_exprs(new_args), *span)
            }
            _ => {
                self.tcx().dcx().span_err(
                    call.span,
                    "`with` ghost inputs/outputs can only be applied to a function call",
                );
                return None;
            }
        };
        // The retained call inherits the removed marker's parent, while the extra
        // arguments become children of that call.
        let new = self.mk_expr(call, new_kind);
        for id in extra_ids {
            self.reparents.push((id, Reparent::To(call.hir_id.local_id)));
        }
        self.reparents.push((call.hir_id.local_id, Reparent::AdoptFrom(expr.hir_id.local_id)));
        Some(new)
    }

    fn redirect_callee(&mut self, callee: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        let ExprKind::Path(qpath) = &callee.kind else {
            self.tcx()
                .dcx()
                .span_err(callee.span, "`with` ghost inputs/outputs: unsupported callee");
            return None;
        };
        let new_qpath = match qpath {
            QPath::Resolved(self_ty, path) => {
                let Res::Def(def_kind, def_id) = path.res else {
                    return None;
                };
                let Some(verified) = self.ctxt.verified_counterpart(def_id) else {
                    // `def_path_str` reads crate attributes and would re-enter
                    // `lower_to_hir`.
                    let name = path.segments.last().map(|s| s.ident.to_string());
                    let name = name.unwrap_or_else(|| "function".to_owned());
                    self.tcx().dcx().span_err(
                        callee.span,
                        format!(
                            "`{name}` does not accept extra ghost/tracked arguments: \
                             it is not declared with `#[verus_spec(with ..)]`"
                        ),
                    );
                    return Some(callee);
                };
                QPath::Resolved(*self_ty, self.redirect_path(path, def_kind, verified)?)
            }
            QPath::TypeRelative(ty, seg) => QPath::TypeRelative(ty, self.rename_segment(seg)?),
        };
        Some(self.mk_expr(callee, ExprKind::Path(new_qpath)))
    }

    /// A qualified trait call must also name the companion trait that declares the
    /// counterpart. An external specification may use a different item name.
    fn redirect_path(
        &self,
        path: &'tcx rustc_hir::Path<'tcx>,
        def_kind: DefKind,
        verified: DefId,
    ) -> Option<&'tcx rustc_hir::Path<'tcx>> {
        let tcx = self.tcx();
        let rename = |seg: &PathSegment<'tcx>, res: Res| PathSegment {
            ident: rustc_span::symbol::Ident::new(tcx.item_name(res.def_id()), seg.ident.span),
            res,
            ..*seg
        };
        let res = Res::Def(def_kind, verified);
        let mut segments = path.segments.to_vec();
        let last = *segments.last()?;
        *segments.last_mut()? = rename(&last, res);
        Some(tcx.hir_arena.alloc(rustc_hir::Path {
            span: path.span,
            res,
            segments: tcx.hir_arena.alloc_slice(&segments),
        }))
    }

    fn rename_segment(
        &mut self,
        seg: &'tcx rustc_hir::PathSegment<'tcx>,
    ) -> Option<&'tcx rustc_hir::PathSegment<'tcx>> {
        let ident = rustc_span::symbol::Ident::new(with_name(seg.ident.name), seg.ident.span);
        Some(self.tcx().hir_arena.alloc(rustc_hir::PathSegment { ident, ..*seg }))
    }

    fn rewrite_method(
        &mut self,
        seg: &'tcx rustc_hir::PathSegment<'tcx>,
    ) -> Option<&'tcx rustc_hir::PathSegment<'tcx>> {
        self.rename_segment(seg)
    }
}

fn counterpart_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Option<DefId> {
    let name = counterpart_name(tcx, owners, def_id);
    let parent = tcx.opt_parent(def_id)?;
    if let Some(parent) = parent.as_local() {
        // Local child queries would re-enter `lower_to_hir`.
        return local_child_fn(owners, parent, name).map(LocalDefId::to_def_id);
    }
    match tcx.def_kind(parent) {
        DefKind::Mod => tcx
            .module_children(parent)
            .iter()
            .find(|child| child.ident.name == name)
            .and_then(|child| child.res.opt_def_id()),
        DefKind::Impl { .. } | DefKind::Trait => tcx
            .associated_items(parent)
            .filter_by_name_unhygienic(name)
            .next()
            .map(|assoc| assoc.def_id),
        _ => None,
    }
}

/// An unerased `const fn` proxy drops its proxy prefix before counterpart lookup.
fn counterpart_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &IndexVec<LocalDefId, MaybeOwner<'tcx>>,
    def_id: DefId,
) -> Symbol {
    let is_unerased_proxy = parse_attrs_opt(def_attrs(tcx, owners, def_id).unwrap_or(&[]), None)
        .iter()
        .any(|a| matches!(a, Attr::UnerasedProxy));
    let name = tcx.item_name(def_id);
    let name = name.as_str();
    let name = match is_unerased_proxy {
        true => name.strip_prefix(UNERASED_PROXY_PREFIX).unwrap_or(name),
        false => name,
    };
    with_name(Symbol::intern(name))
}
