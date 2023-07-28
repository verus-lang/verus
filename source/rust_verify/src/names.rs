use crate::unsupported_err;
use crate::util::unsupported_err_span;
use rustc_hir::definitions::DefPath;
use rustc_hir::{ItemKind, MaybeOwner, OwnerNode};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use vir::ast::{Ident, VirErr};

// rustc uses u32 disambiguators to distinguish one DefPathData::Impl from another.
// However, these u32 values aren't necessarily stable between the erase_ghost and !erase_ghost
// versions of the HIR.
// Therefore, we replace these disambiguators with our own disambiguation based on the
// impl declaration.

type TypPath = Vec<String>;

// Represent as much of type structure as possible
// without including any impl names in any paths inside the type
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypTree {
    String(String),
    Path(TypPath),
    Decorate(String, Box<TypTree>),
    Apply(TypPath, Vec<Box<TypTree>>),
}

// A fingerprint for an impl block that captures everything we need
// to recognize the same impl block across ghost and erased compiler executions.
// Note that we don't care about distinguishing between multiple inherent (no trait) impl blocks
// with the same self type (e.g. impl S { fn f() {} } impl S { fn g() {} });
// these can just be merged into a single impl block.
// For impls for traits (e.g. impl T1 for S { ... } impl T2 for S { ... }),
// we should distinguish the impl blocks.
// Otherwise, we would lose precision by merging the blocks together,
// which would be sound but could cause our nontermination checking (recursion.rs)
// to report spurious errors.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
struct ImplFingerprint {
    parent: TypPath,
    generics: Vec<String>,
    trait_path: Option<TypPath>,
    trait_args: Vec<TypTree>,
    self_typ: TypTree,
}

// rustc's internal name in a particular run of rustc.
// It consists of TypPath data, which is stable across runs of rustc,
// and numeric disambiguators, which can vary between runs of rustc.
// Our goal is to remap RustcLocalImplId to completely stable names.
pub(crate) type RustcLocalImplId = (TypPath, Vec<u32>);

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct ImplNameCtxt {
    // For any (unstable) RustcLocalImplId, compute a stable name.
    // (this stable name is just the single segment representing "impl%id";
    // it needs to be combined with the rest of the path to form a complete path).
    // Example:
    // - when compiling vstd (both with erase_ghost and !erase_ghost):
    //   - rustc creates its own internal names for impls in vstd
    //     - these names may be different in erase_ghost and !erase_ghost
    //     - example:
    //       - in erase_ghost: impl%2
    //       - in !erase_ghost: impl%3
    //   - we represent these rustc internal names with RustcLocalImplId
    //     - example:
    //       - in erase_ghost: ("impl", [2])
    //       - in !erase_ghost: ("impl", [3])
    //   - we map the RustcLocalImplId to our own Ident in map_to_stable_name
    //     - we create a mapping for erase_ghost and another mapping for !erase_ghost
    //     - the Ident values are the same in erase_ghost and !erase_ghost
    //     - example:
    //       - in erase_ghost: ("impl", [2]) -> impl_Vec7
    //       - in !erase_ghost: ("impl", [3]) -> impl_Vec7
    //   - in our own VIR AST for the vstd library (created with !erase_ghost),
    //     we use the stable Ident values
    //     - impl_Vec7
    //   - rustc emits a library file on disk using its erase_ghost internal names
    //       - in erase_ghost: impl%2
    //   - we serialize and emit our VIR AST in CrateWithMetadata
    //     - the serialized VIR AST contains impl_Vec7
    //   - we also serialize the erase_ghost mapping in CrateWithMetadata
    //     - ("impl", [2]) -> impl_Vec7
    //     - see the export_impls function below and see import_export.rs
    // - when a client application imports vstd:
    //   - rustc reads in the erase_ghost-compiled vstd library from disk
    //     - this file contains the *same* erase_ghost rustc internal names
    //       created while compiling vstd
    //       - in erase_ghost: impl%2
    //     - we again represent these internal names with the same RustcLocalImplId
    //       as we did while compiling vstd
    //       - in erase_ghost: ("impl", [2])
    //   - we read in the serialized mapping from CrateWithMetadata created when compiling vstd
    //     - in erase_ghost: ("impl", [2]) -> impl_Vec7
    //   - we use the RustcLocalImplId and deserialized map_to_stable_name to recover the same
    //     Ident values that were used while compiling vstd
    //     - impl_Vec7
    //   - the key result is that these Ident values will match the !erase_ghost Ident values
    //     that are present in the rest of the deserialized VIR AST for the vstd library
    //     (whereas if we hadn't done the remapping, we would have seen inconsistent names,
    //     impl%2 from the !erase_ghost rustc-emitted library, and impl%3 in our deserialized
    //     VIR AST)
    pub(crate) map_to_stable_name: HashMap<RustcLocalImplId, Ident>,
}

#[derive(Debug)]
pub(crate) struct ImplNameState {
    impl_table: HashMap<ImplFingerprint, Ident>,
}

fn def_path_to_rustc_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_path: DefPath,
    num_segments: usize,
) -> RustcLocalImplId {
    let mut path = vec![tcx.crate_name(def_path.krate).to_string()];
    let mut disambiguators: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        if i >= num_segments {
            break;
        }
        match &d.data {
            DefPathData::ValueNs(symbol) | DefPathData::TypeNs(symbol) => {
                path.push(symbol.to_string());
            }
            DefPathData::Ctor => {
                path.push(vir::def::RUST_DEF_CTOR.to_string());
            }
            DefPathData::Impl => {
                // We don't have names for the impls at this point, so just use "impl"
                path.push("impl".to_string());
                disambiguators.push(d.disambiguator);
            }
            _ => {}
        }
        i += 1;
    }
    (path, disambiguators)
}

fn def_path_to_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> TypPath {
    def_path_to_rustc_id(tcx, def_path, usize::MAX).0
}

impl ImplNameCtxt {
    pub(crate) fn extend(&mut self, other: ImplNameCtxt) {
        for (id, x) in other.map_to_stable_name.into_iter() {
            if let Some(y) = self.map_to_stable_name.get(&id) {
                assert!(&x == y);
            } else {
                self.map_to_stable_name.insert(id, x);
            }
        }
    }

    pub(crate) fn get_stable_impl_name<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_path: DefPath,
        num_segments: usize,
    ) -> Option<Ident> {
        let id = def_path_to_rustc_id(tcx, def_path, num_segments);
        self.map_to_stable_name.get(&id).cloned()
    }
}

impl TypTree {
    fn short_name(&self) -> String {
        match self {
            TypTree::String(s) => s.clone(),
            TypTree::Path(p) | TypTree::Apply(p, _) => p.last().expect("path").clone(),
            TypTree::Decorate(_, t) => t.short_name(),
        }
    }
}

fn typ_tree<'tcx>(tcx: TyCtxt<'tcx>, span: Span, ty: &Ty<'tcx>) -> Result<TypTree, VirErr> {
    let box_rec =
        |ty: &Ty<'tcx>| -> Result<Box<TypTree>, VirErr> { Ok(Box::new(typ_tree(tcx, span, ty)?)) };
    let t = match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) => {
            TypTree::String(ty.to_string())
        }
        TyKind::Adt(AdtDef(adt), args) => {
            let path = def_path_to_path(tcx, tcx.def_path(adt.did));
            let mut typ_args: Vec<Box<TypTree>> = Vec::new();
            for arg in args.iter() {
                match arg.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(t) => {
                        typ_args.push(box_rec(&t)?);
                    }
                    _ => {}
                }
            }
            TypTree::Apply(path, typ_args)
        }
        TyKind::Foreign(did) => TypTree::Path(def_path_to_path(tcx, tcx.def_path(*did))),
        TyKind::Str => TypTree::String("str".to_string()),
        TyKind::Array(t, _len) => TypTree::Decorate("array".to_string(), box_rec(t)?),
        TyKind::Slice(t) => TypTree::Decorate("slice".to_string(), box_rec(t)?),
        TyKind::RawPtr(tmut) => {
            TypTree::Decorate(format!("raw{:?}", tmut.mutbl), box_rec(&tmut.ty)?)
        }
        TyKind::Ref(_region, t, muta) => TypTree::Decorate(format!("ref{:?}", muta), box_rec(t)?),
        TyKind::Never => TypTree::String("never".to_string()),
        TyKind::Tuple(ts) => {
            let path = vec!["tuple".to_string()];
            let typ_args = ts.iter().map(|t| box_rec(&t)).collect::<Result<_, _>>()?;
            TypTree::Apply(path, typ_args)
        }
        TyKind::Alias(_kind, alias) => {
            let path = def_path_to_path(tcx, tcx.def_path(alias.def_id));
            let mut typ_args: Vec<Box<TypTree>> = Vec::new();
            if let Some(args) = alias.substs.try_as_type_list() {
                for t in args.iter() {
                    typ_args.push(box_rec(&t)?);
                }
            }
            TypTree::Apply(path, typ_args)
        }
        TyKind::Param(_) => TypTree::String(ty.to_string()),
        TyKind::Bound(..) => TypTree::String(ty.to_string()),
        TyKind::Closure(..) => TypTree::String("closure".to_string()),

        TyKind::FnDef(..) => unsupported_err!(span, "anonymous function types"),
        TyKind::FnPtr(..) => unsupported_err!(span, "function pointer types"),
        TyKind::Dynamic(..) => unsupported_err!(span, "dynamic types"),
        TyKind::Generator(..) => unsupported_err!(span, "generator types"),
        TyKind::GeneratorWitness(..) => unsupported_err!(span, "generator witness types"),
        TyKind::Placeholder(..) => unsupported_err!(span, "type inference placeholder types"),
        TyKind::Infer(..) => unsupported_err!(span, "type inference placeholder types"),
        TyKind::Error(..) => unsupported_err!(span, "type inference placeholder error types"),
    };
    Ok(t)
}

fn traverse_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    state: &mut ImplNameState,
    _export: bool,
) -> Result<ImplNameCtxt, VirErr> {
    let hir = tcx.hir();
    let krate = hir.krate();
    let mut map_to_stable_name = HashMap::new();
    let mut make_name_table: HashMap<(TypPath, String, Option<String>), u64> = HashMap::new();
    let mut make_name =
        |parent: &TypPath, self_name: String, trait_name: Option<String>| -> Ident {
            let key = (parent.clone(), self_name.clone(), trait_name.clone());
            let n = if let Some(m) = make_name_table.get(&key) { m + 1 } else { 0 };
            make_name_table.insert(key, n);
            vir::def::impl_name(self_name, trait_name, n)
        };
    for owner in &krate.owners {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Impl(impll) => {
                        use crate::rustc_middle::ty::DefIdTree;
                        let impl_def_id = item.owner_id.to_def_id();
                        let impl_name_id =
                            def_path_to_rustc_id(tcx, tcx.def_path(impl_def_id), usize::MAX);
                        let parent_id = tcx.parent(impl_def_id);
                        // compute ImplFingerprint fingerprint for impll
                        let parent_def_path = tcx.def_path(parent_id);
                        let parent = def_path_to_path(tcx, parent_def_path);
                        let mut generics = Vec::new();
                        for param in tcx.generics_of(impl_def_id).params.iter() {
                            generics.push(param.name.to_string());
                        }
                        let (trait_path, trait_args) = if let Some(tref) = &impll.of_trait {
                            let path = def_path_to_path(tcx, tcx.def_path(tref.path.res.def_id()));
                            let trait_ref =
                                tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");
                            let mut trait_args: Vec<TypTree> = Vec::new();
                            for ty in trait_ref.0.substs.types() {
                                trait_args.push(typ_tree(tcx, item.span, &ty)?);
                            }
                            (Some(path), trait_args)
                        } else {
                            (None, vec![])
                        };
                        let trait_name =
                            trait_path.as_ref().map(|path| path.last().cloned().unwrap());
                        let self_typ = typ_tree(tcx, item.span, &tcx.type_of(impl_def_id))?;
                        let self_name = self_typ.short_name();
                        let fingerprint = ImplFingerprint {
                            parent: parent.clone(),
                            generics,
                            trait_path,
                            trait_args,
                            self_typ,
                        };
                        // store fingerprint and name in state
                        let prev = state.impl_table.get(&fingerprint);
                        let name = if let Some(name) = prev {
                            name.clone()
                        } else {
                            let name = make_name(&parent, self_name, trait_name);
                            state.impl_table.insert(fingerprint, name.clone());
                            name
                        };
                        assert!(!map_to_stable_name.contains_key(&impl_name_id));
                        map_to_stable_name.insert(impl_name_id, name);
                    }
                    _ => {}
                },
                _ => (),
            }
        }
    }
    Ok(ImplNameCtxt { map_to_stable_name })
}

pub(crate) fn collect_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<(ImplNameState, ImplNameCtxt), VirErr> {
    let mut state = ImplNameState { impl_table: HashMap::new() };
    let impl_ctxt = traverse_impls(tcx, &mut state, false)?;
    Ok((state, impl_ctxt))
}

pub(crate) fn export_impls<'tcx>(
    queries: &'tcx verus_rustc_interface::Queries<'tcx>,
    state: &mut ImplNameState,
) -> ImplNameCtxt {
    queries.global_ctxt().expect("global_ctxt").enter(|tcx| {
        match traverse_impls(tcx, state, false) {
            Ok(imp) => imp,
            Err(err) => {
                dbg!(err);
                panic!("internal error: found unsupported feature during export")
            }
        }
    })
}
