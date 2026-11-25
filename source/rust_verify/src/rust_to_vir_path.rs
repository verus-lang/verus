use crate::verus_items::{VerusItem, VerusItems};
use rustc_hir::QPath;
use rustc_hir::definitions::DefPath;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_span::sym;
use std::collections::HashMap;
use std::ops::DerefMut;
use std::sync::Arc;
use vir::ast::{CrateId, Path, PathX, Segment};

pub(crate) fn def_id_to_friendly<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
) -> String {
    match def_id_to_vir_path_option(tcx, verus_items, def_id) {
        None => format!("{:?}", def_id),
        Some(p) => vir::ast_util::path_as_friendly_rust_name(&p),
    }
}

pub(crate) fn def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
    path_def_id_map: Option<impl DerefMut<Target = HashMap<Path, DefId>>>,
) -> Path {
    let result = def_id_to_vir_path_option(tcx, verus_items, def_id)
        .unwrap_or_else(|| panic!("unhandled name {:?}", def_id));
    match path_def_id_map {
        Some(mut map) => map.deref_mut().insert(result.clone(), def_id),
        None => None,
    };
    result
}

pub(crate) fn def_id_to_vir_path_option<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
) -> Option<Path> {
    let result = remapped_def_id_to_vir_path(tcx, verus_items, def_id);
    if let Some(path) = &result {
        register_friendly_path_as_rust_name(tcx, verus_items, def_id, path);
    }
    result
}

// Register an alternative "friendly" paths for printing better error messages
// or for the command-line --verify-function arguments.
fn register_friendly_path_as_rust_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
    path: &Path,
) {
    let hir_id = if let Some(local_id) = def_id.as_local() {
        tcx.local_def_id_to_hir_id(local_id)
    } else {
        return;
    };
    let node = tcx.hir_node(hir_id);
    let is_impl_item_fn = matches!(
        node,
        rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
            kind: rustc_hir::ImplItemKind::Fn(..),
            ..
        })
    );
    if !is_impl_item_fn {
        return;
    }
    let mut parent_node = tcx.hir_parent_iter(hir_id);
    let (_, parent_node) = parent_node.next().expect("unexpected empty impl path");
    let friendly_self_ty = match parent_node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll),
            owner_id,
            ..
        }) => match &impll.self_ty.kind {
            rustc_hir::TyKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
            )) => remapped_def_id_to_vir_path(tcx, verus_items, *self_def_id),
            _ => {
                // To handle cases like [T] which are not syntactically datatypes
                // but converted into VIR datatypes.
                let self_ty = tcx.type_of(owner_id.to_def_id()).skip_binder();
                match self_ty.kind() {
                    TyKind::Slice(_) => Some(vir::def::slice_type()),
                    _ => None,
                }
            }
        },
        _ => None,
    };
    if let Some(ty_path) = friendly_self_ty {
        let friendly_path = ty_path.push_segment(def_to_friendly_path_ident(tcx, def_id));
        vir::ast_util::set_path_as_rust_name(path, &friendly_path);
    }
}

fn def_to_friendly_path_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Segment {
    let path = def_path_to_vir_path(tcx, tcx.def_path(def_id)).expect("unexpected empty impl path");
    // A function declared with `with ..` is shown under its name in VIR.
    match with_fn_path(tcx, def_id, path).last_segment() {
        Segment::V(name, _) => Segment::V(name, 0),
        _ => panic!("unexpected name of impl"),
    }
}

fn remapped_def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
) -> Option<Path> {
    use crate::verus_items::RustPrivate;
    let verus_item = verus_items.id_to_name.get(&def_id);
    if let Some(VerusItem::RustPrivate(RustPrivate::Path(path))) = verus_item {
        return Some(path.clone());
    }
    if let Some(v @ VerusItem::RustPrivate(_)) = verus_item {
        if let Some(id) = verus_items.name_to_rust_private_id.get(v) {
            return checked_def_id_to_vir_path(tcx, verus_items, *id);
        }
    }
    return checked_def_id_to_vir_path(tcx, verus_items, def_id);
}

/// We want to translate the DefPaths to nice-looking-paths, when possible,
/// which means throwing out the disambiguators. However, if we screw up, we could get
/// conflicting paths. So we keep a map of all the translations we to do double-check.
///
/// (Note: we still need to keep the mapping deterministic so it's consistent across
/// Verus runs for different crates. So don't try anything clever like "only add disambiguators
/// when necessary".)
fn checked_def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
) -> Option<Path> {
    static DEF_ID_TO_VIR_MAP: std::sync::Mutex<
        Option<(HashMap<DefId, Path>, HashMap<Path, DefId>)>,
    > = std::sync::Mutex::new(None);

    let mut maps = DEF_ID_TO_VIR_MAP.lock().unwrap();
    if maps.is_none() {
        *maps = Some((HashMap::new(), HashMap::new()));
    }
    let maps = maps.as_mut().unwrap();

    if let Some(path) = maps.0.get(&def_id) {
        return Some(path.clone());
    }

    let Some(path) = unchecked_def_id_to_vir_path(tcx, verus_items, def_id) else {
        return None;
    };

    if let Some(other_def_id) = maps.1.get(&path) {
        panic!(
            "Verus Internal Error: collision for path mapping of {:?} and {:?}",
            def_id, other_def_id
        );
    }
    maps.0.insert(def_id, path.clone());
    maps.1.insert(path.clone(), def_id);
    Some(path)
}

fn unchecked_def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &VerusItems,
    def_id: DefId,
) -> Option<Path> {
    let verus_item = verus_items.id_to_name.get(&def_id);
    if let Some(VerusItem::Vstd(_, Some(fn_name))) = verus_item {
        // interpreter.rs and def.rs refer directly to some impl methods,
        // so make sure we use the fn_name names from `verus_items`.
        // All segments but the last are in the type namespace;
        // the last segment is in the namespace of the item itself.
        let names: Vec<&str> = fn_name.split("::").collect();
        let (last, prefix) = names.split_last().expect("fn_name");
        let mut segments: Vec<Segment> =
            prefix.iter().map(|x| Segment::T(Arc::new(x.to_string()), 0)).collect();
        let last = Arc::new(last.to_string());
        let in_type_ns = matches!(
            tcx.def_path(def_id).data.last().map(|d| &d.data),
            Some(rustc_hir::definitions::DefPathData::TypeNs(_))
        );
        segments.push(if in_type_ns { Segment::T(last, 0) } else { Segment::V(last, 0) });
        return Some(Arc::new(PathX { krate: CrateId::Vstd, segments: Arc::new(segments) }));
    }
    def_path_to_vir_path(tcx, tcx.def_path(def_id)).map(|p| with_fn_path(tcx, def_id, p))
}

/// Maps generated pairs so the verified counterpart, which holds the specification, retains
/// the source name in VIR. This keeps diagnostics, `--verify-function`, and profiler output
/// aligned with the user's function rather than a generated counterpart name.
///
/// Attribute markers disambiguate user-written names that begin with `VERIFIED_PREFIX`.
/// Definitions and call sites both pass through this function, so the mapping cannot live only
/// in `check_item_fn`. Trait-method specification items are separate items whose names embed
/// the function name, so only the portion after their prefix is renamed.
fn with_fn_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, path: Path) -> Path {
    use rustc_hir::def::DefKind;
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return path;
    }
    let Segment::V(name, disambiguator) = path.last_segment() else {
        return path;
    };
    let (prefix, base) = match name.strip_prefix(vir::def::VERUS_SPEC) {
        Some(rest) => (vir::def::VERUS_SPEC, rest),
        None => ("", name.as_str()),
    };
    fn strip_verified(base: &str) -> Option<&str> {
        base.strip_prefix(crate::attributes::VERIFIED_IMPL_PREFIX)
            .or_else(|| base.strip_prefix(crate::attributes::VERIFIED_PREFIX))
    }
    let renamed = match strip_verified(base) {
        Some(base) if crate::attributes::is_verified_counterpart(def_attrs(tcx, def_id)) => {
            base.to_owned()
        }
        Some(_) => return path,
        None if crate::attributes::is_unverified_stub(def_attrs(tcx, def_id))
            && has_sibling_counterpart(tcx, def_id) =>
        {
            format!("{}{base}", crate::attributes::UNVERIFIED_PREFIX)
        }
        None => return path,
    };
    path.replace_last(Segment::V(Arc::new(format!("{prefix}{renamed}")), disambiguator))
}

/// Does `with_fn_path` rename this function? Only the two halves of a `with ..` split
/// are renamed; every other function keeps the name it is written with.
pub(crate) fn is_with_fn_renamed<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    match def_path_to_vir_path(tcx, tcx.def_path(def_id)) {
        Some(path) => with_fn_path(tcx, def_id, path.clone()).last_segment() != path.last_segment(),
        None => false,
    }
}

/// A free function, inherent method, or method of a trait declared in this crate can give up
/// its name because its counterpart is a sibling item or a companion-trait method.
/// An `external_trait_specification` method cannot because it is named after the external
/// method it specifies, and call sites compute exactly that name.
fn has_sibling_counterpart<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    let Some(parent) = tcx.opt_parent(def_id) else {
        return false;
    };
    match tcx.def_kind(parent) {
        DefKind::Mod | DefKind::Impl { .. } => true,
        DefKind::Trait => crate::attributes::parse_attrs_opt(def_attrs(tcx, parent), None)
            .into_iter()
            .all(|a| !matches!(a, crate::attributes::Attr::ExternalTraitSpecification(..))),
        _ => false,
    }
}

/// The attributes of any item, local or not.
fn def_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [rustc_hir::Attribute] {
    match def_id.as_local() {
        Some(local) => tcx.hir_attrs(tcx.local_def_id_to_hir_id(local)),
        None => tcx.attrs_for_def(def_id),
    }
}

pub(crate) fn def_path_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> Option<Path> {
    let krate = mk_crate_id(tcx, def_path.krate);
    let mut segments: Vec<Segment> = Vec::new();
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        let s = match &d.data {
            DefPathData::ValueNs(symbol) => {
                Segment::V(Arc::new(symbol.to_string()), d.disambiguator)
            }
            DefPathData::TypeNs(symbol) => {
                Segment::T(Arc::new(symbol.to_string()), d.disambiguator)
            }
            DefPathData::Ctor => Segment::Ctor(d.disambiguator),
            DefPathData::Impl => Segment::Impl(d.disambiguator),
            DefPathData::ForeignMod => Segment::ForeignMod(d.disambiguator),
            DefPathData::OpaqueTy => Segment::OpaqueTy(d.disambiguator),
            DefPathData::Closure => Segment::Closure(d.disambiguator),
            DefPathData::AnonConst => Segment::AnonConst(d.disambiguator),
            _ => return None,
        };
        segments.push(s);
    }
    Some(Arc::new(PathX { krate, segments: Arc::new(segments) }))
}

pub(crate) fn def_path_to_segments_without_disambiguation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_path: DefPath,
) -> Option<Vec<String>> {
    let krate = mk_crate_id(tcx, def_path.krate);
    let mut segments: Vec<String> = Vec::new();
    segments.push(vir::def::krate_to_string_ignore_stable_id(&krate));
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        match &d.data {
            DefPathData::ValueNs(symbol) => {
                segments.push(symbol.to_string());
            }
            DefPathData::TypeNs(symbol) => {
                segments.push(symbol.to_string());
            }
            _ => return None,
        }
    }
    Some(segments)
}

/// A diagnostic item that is always defined by vstd (and only by vstd),
/// used to identify the actual vstd crate.
const VSTD_IDENTIFYING_DIAGNOSTIC_ITEM: &str = "verus::vstd::invariant::open_invariant_end";

/// Map a crate to its CrateId.
///
/// The actual `core`, `alloc`, and `vstd` crates get the special ids
/// `CrateId::Core`, `CrateId::Alloc`, and `CrateId::Vstd`.
/// We cannot identify these crates by name alone,
/// since any crate can be compiled with `--crate-name core`, `--crate-name alloc`, etc.
/// Instead, we identify each of them by an item that it defines.
/// Rust guarantees that each lang item and each diagnostic item is defined by at most one crate
/// in the crate graph, and defining either requires internal rustc features:
/// - `core` defines the `sized` lang item
/// - `alloc` defines the `owned_box` lang item
/// - `vstd` defines the `VSTD_IDENTIFYING_DIAGNOSTIC_ITEM` diagnostic item
/// All other crates (including crates that merely share one of these names)
/// get a `CrateId::Id` with Rust's stable crate id.
pub(crate) fn mk_crate_id<'tcx>(tcx: TyCtxt<'tcx>, krate: CrateNum) -> CrateId {
    let s = tcx.crate_name(krate).to_string();
    // The AST rewrite needs dependency IDs before local HIR is available.
    let defines_lang_item = |name| {
        if krate == LOCAL_CRATE {
            tcx.lang_items().iter().any(|(item, id)| item.name() == name && id.is_local())
        } else {
            tcx.defined_lang_items(krate).iter().any(|&(_, item)| item.name() == name)
        }
    };
    match s.as_str() {
        "core" if defines_lang_item(sym::sized) => CrateId::Core,
        "alloc" if defines_lang_item(sym::owned_box) => CrateId::Alloc,
        "vstd"
            if tcx
                .diagnostic_items(krate)
                .name_to_id
                .contains_key(&rustc_span::Symbol::intern(VSTD_IDENTIFYING_DIAGNOSTIC_ITEM)) =>
        {
            CrateId::Vstd
        }
        _ => CrateId::Id(Arc::new(s), tcx.stable_crate_id(krate).as_u64()),
    }
}
