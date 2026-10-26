use crate::verus_items::{VerusItem, VerusItems};
use rustc_hir::QPath;
use rustc_hir::definitions::DefPath;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::{CrateNum, DefId};
use std::collections::HashMap;
use std::ops::DerefMut;
use std::sync::Arc;
use vir::ast::{CrateId, Path, PathX};

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

fn def_to_friendly_path_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> vir::ast::Ident {
    let def_path = tcx.def_path(def_id);
    match def_path.data.last().expect("unexpected empty impl path").data {
        rustc_hir::definitions::DefPathData::ValueNs(name) => Arc::new(name.to_string()),
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
        // so make sure we use the fn_name names from `verus_items`
        let segments = fn_name.split("::").map(|x| Arc::new(x.to_string())).collect();
        return Some(Arc::new(PathX { krate: CrateId::Vstd, segments: Arc::new(segments) }));
    }
    def_path_to_vir_path(tcx, tcx.def_path(def_id))
}

fn def_path_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> Option<Path> {
    let krate = mk_crate_id(tcx, def_path.krate);
    let mut segments: Vec<vir::ast::Ident> = Vec::new();
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        let s = match &d.data {
            DefPathData::ValueNs(symbol) => {
                if d.disambiguator == 0 {
                    symbol.to_string()
                } else {
                    format!(
                        "{:}{:}%{:}",
                        vir::def::RUST_DEF_VALUE_NS_DISAMBIGUATED,
                        d.disambiguator,
                        symbol.as_str()
                    )
                }
            }
            DefPathData::TypeNs(symbol) => {
                if d.disambiguator == 0 {
                    format!("{:}{:}", vir::def::RUST_DEF_TYPE_NS, symbol.as_str())
                } else {
                    format!(
                        "{:}{:}%{:}",
                        vir::def::RUST_DEF_TYPE_NS_DISAMBIGUATED,
                        d.disambiguator,
                        symbol.as_str()
                    )
                }
            }
            DefPathData::Ctor => vir::def::RUST_DEF_CTOR.to_string(),
            DefPathData::Impl => vir::def::impl_ident(d.disambiguator),
            DefPathData::ForeignMod => {
                vir::def::RUST_DEF_FOREIGN_MOD.to_string() + &d.disambiguator.to_string()
            }
            DefPathData::OpaqueTy => {
                vir::def::RUST_OPAQUE_TYPE.to_string() + &d.disambiguator.to_string()
            }
            DefPathData::Closure => {
                vir::def::RUST_DEF_CLOSURE.to_string() + &d.disambiguator.to_string()
            }
            DefPathData::AnonConst => {
                vir::def::RUST_DEF_ANON_CONST.to_string() + &d.disambiguator.to_string()
            }
            _ => return None,
        };
        segments.push(Arc::new(s));
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

pub(crate) fn mk_crate_id<'tcx>(tcx: TyCtxt<'tcx>, krate: CrateNum) -> CrateId {
    let stable_id = tcx.stable_crate_id(krate).as_u64();
    let s = tcx.crate_name(krate).to_string();
    match s.as_str() {
        "vstd" => CrateId::Vstd,
        "core" => CrateId::Core,
        "alloc" => CrateId::Alloc,
        _ => CrateId::Id(Arc::new(s), stable_id),
    }
}
