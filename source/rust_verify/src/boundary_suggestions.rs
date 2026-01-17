use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    EarlyParamRegion, GenericArg, GenericParamDefKind, InstantiatedPredicates, Ty, TyCtxt, TyKind,
};
use rustc_type_ir::{
    Interner, TypeFoldable, TypeFolder, TypeSuperVisitable, TypeVisitable, TypeVisitor,
};
use vir::ast::VirErr;

use crate::{context::Context, rust_to_vir_base::mk_visibility};

pub(crate) fn build_boundary_suggestion<'tcx>(
    ctxt: &Context<'tcx>,
    external_def_id: DefId,
    path: &Arc<vir::ast::PathX>,
) -> Result<String, VirErr> {
    match ctxt.tcx.def_kind(external_def_id) {
        rustc_hir::def::DefKind::Struct
        | rustc_hir::def::DefKind::Union
        | rustc_hir::def::DefKind::Enum
        | rustc_hir::def::DefKind::Variant => {
            build_external_type_suggestion(ctxt, external_def_id, path)
        }
        rustc_hir::def::DefKind::AssocFn | rustc_hir::def::DefKind::Fn => {
            build_fn_assume_specification_suggestion(ctxt, external_def_id)
        }
        rustc_hir::def::DefKind::Const => {
            build_const_assume_specification_suggestion(ctxt, external_def_id, path)
        }
        _ => Err(crate::util::error("Building boundary suggestion for non type/fn/const")),
    }
}
pub(crate) fn build_external_type_suggestion<'tcx>(
    ctxt: &Context<'tcx>,
    external_def_id: DefId,
    path: &Arc<vir::ast::PathX>,
) -> Result<String, VirErr> {
    let path_string = ctxt.tcx.def_path_str(external_def_id);
    let path_string = prepend_crate_if_local(external_def_id, path_string);

    let generics = ctxt.tcx.generics_of(external_def_id);
    let mut region_renamer: RegionRenamer<'_> =
        build_region_renamer(ctxt, external_def_id, generics)?;

    let predicates = ctxt.tcx.predicates_of(external_def_id).instantiate_identity(ctxt.tcx);
    let predicates = predicates.fold_with(&mut region_renamer);

    let (param_declarations, type_param_set) =
        build_generics_declarations(ctxt, generics, &predicates, &region_renamer)?;
    let all_type_symbols = type_param_set.clone();
    // Map to str so that the type params come out sorted.
    let all_type_params: BTreeSet<&str> = all_type_symbols.iter().map(|s| s.as_str()).collect(); // Need to have all type params for recursive declarations.
    let where_clauses = build_where_clauses(ctxt, predicates, type_param_set)?;
    let visibility = mk_visibility(ctxt, external_def_id);
    let suggestion = format!(
            "{}{}{}{}{}{}{}{}{}{}{}{}",
            // Polarity annotations
            all_type_params.iter().fold(String::new(), |acc, x| acc
                + "#[verifier::reject_recursive_types("
                + x
                + ")]\n",),
            "#[verifier::external_type_specification]\n",
            match visibility.restricted_to {
                None => "pub ",
                Some(_) => "", // This may be the point that it makes sense to check for the type being in a private module or otherwise not visible
            },
            "struct ",
            "Ex".to_owned() + &path.last_segment(), // Proxy type name
            if generics.is_empty() {
                "".to_owned()
            } else {
                // "".to_owned()
                // Generic parameter list, need all params and inline bounds here
                param_declarations
                    .iter()
                    .fold("<".to_owned(), |acc, (_, decl)| acc + decl + ", ")
                    .trim_end_matches(", ")
                    .to_owned()
                    + ">"
            },
            "(",
            path_string, // External Type name
            if param_declarations.is_empty() {
                "".to_owned()
            } else {
                param_declarations
                    .iter()
                    .fold("<".to_owned(), |acc, (param, _)| acc + param.name.as_str() + ", ")
                    .trim_end_matches(", ")
                    .to_owned()
                    + ">"
            }, // External type generic parameters
            ")",
            if where_clauses.is_empty() {
                "".to_owned()
            } else {
                where_clauses.iter().fold("\nwhere".to_owned(), |acc, x| acc + "\n" + &x + ",")
            }, // Where clause generic bounds
            ";",
        );
    Ok(suggestion)
}
pub(crate) fn check_visibilities<'tcx, T: TypeVisitable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    ty: T,
) -> Result<(), VirErr> {
    let mut walker: VisibilityWalker<'_> =
        VisibilityWalker { tcx: tcx, visibilities: HashMap::new() };
    ty.visit_with(&mut walker);
    for p in walker.visibilities {
        match p {
            (def_id, None) => {
                if let Some(_) = tcx.hir_get_if_local(def_id) {
                    continue;
                };
                return crate::util::err_span(
                    tcx.def_span(def_id),
                    format!(
                        "Could not build suggestion as there is no visible path to {}.",
                        tcx.def_path_str(def_id)
                    ),
                );
            }
            _ => (),
        }
    }
    Ok(())
}
pub(crate) fn build_fn_assume_specification_suggestion<'tcx>(
    ctxt: &Context<'tcx>,
    external_def_id: DefId,
) -> Result<String, VirErr> {
    // First, we will validate that this function and the types referenced from it are accessible from the calling code.

    let fn_sig = ctxt.tcx.fn_sig(external_def_id).instantiate_identity().skip_binder();
    check_visibilities(ctxt.tcx, fn_sig)?;

    let ret_ty = fn_sig.output();

    let visibility = mk_visibility(ctxt, external_def_id);

    let predicates = ctxt.tcx.predicates_of(external_def_id);
    let inst_predicates = predicates.instantiate_identity(ctxt.tcx);
    let generics = ctxt.tcx.generics_of(external_def_id);
    let mut region_renamer: RegionRenamer<'_> =
        build_region_renamer(ctxt, external_def_id, generics)?;
    let fn_sig = fn_sig.fold_with(&mut region_renamer);
    let inst_predicates = inst_predicates.fold_with(&mut region_renamer);
    let (param_declarations, type_params) =
        build_generics_declarations(ctxt, generics, &inst_predicates, &region_renamer)?;

    let where_clauses = build_where_clauses(ctxt, inst_predicates, type_params)?;

    let path_string = if let Some(_trait_def_id) = ctxt.tcx.trait_of_assoc(external_def_id) {
        return Err(crate::util::error(
            "Cannot build specification for unresolved trait item.  Consider an external_trait_specification declaration.",
        ));
    } else if let Some(impl_def_id) = ctxt.tcx.impl_of_assoc(external_def_id) {
        let of_trait = ctxt.tcx.impl_opt_trait_ref(impl_def_id).is_some();
        if of_trait {
            let impl_trait = ctxt.tcx.impl_trait_header(impl_def_id);
            let trait_ref = impl_trait.trait_ref.skip_binder();
            let self_ty = trait_ref.self_ty().fold_with(&mut region_renamer);
            format!(
                "<{} as {}>::{}",
                prepend_crate_if_local_for_type(ctxt, &self_ty, self_ty.to_string()),
                prepend_crate_if_local(
                    trait_ref.def_id,
                    ctxt.tcx.def_path_str_with_args(trait_ref.def_id, trait_ref.args),
                ),
                prepend_crate_if_local(
                    external_def_id,
                    ctxt.tcx.item_ident(external_def_id).to_string(),
                ),
            )
        } else {
            // This is an inherent impl, don't need to build a trait impl string.
            prepend_crate_if_local(external_def_id, ctxt.tcx.def_path_str(external_def_id))
        }
    } else {
        prepend_crate_if_local(external_def_id, ctxt.tcx.def_path_str(external_def_id))
    };

    let suggestion_text = format!(
        "{}assume_specification{} [{}] ({}){}{}{};",
        if visibility.is_public() { "pub " } else { "" },
        if generics.is_empty() {
            "".to_owned()
        } else {
            // "".to_owned()
            // Generic parameter list, need all params and inline bounds here
            param_declarations
                .iter()
                .fold("<".to_owned(), |acc, (_, decl)| acc + decl + ", ")
                .trim_end_matches(", ")
                .to_owned()
                + ">"
        },
        path_string, //path,
        fn_sig
            .inputs()
            .iter()
            .enumerate()
            .map(|(i, val)| {
                "_".to_owned()
                    + i.to_string().as_str()
                    + ": "
                    + &prepend_crate_if_local_for_type(ctxt, val, val.to_string())
            })
            .fold("".to_string(), |acc, s| acc + &s + ", ")
            .trim_end_matches(", "), //params,
        if ret_ty.is_unit() { "" } else { " -> " },
        if ret_ty.is_unit() {
            "".to_owned()
        } else {
            prepend_crate_if_local_for_type(ctxt, &ret_ty, ret_ty.to_string())
        },
        if where_clauses.is_empty() {
            "".to_owned()
        } else {
            where_clauses.iter().fold("\nwhere".to_owned(), |acc, x| acc + "\n" + &x + ",")
        },
    );
    Ok(suggestion_text)
}

fn prepend_crate_if_local_for_type<'tcx>(ctxt: &Context<'tcx>, ty: &Ty<'tcx>, s: String) -> String {
    match ty.kind() {
        rustc_type_ir::TyKind::Adt(adt_def, _) => prepend_crate_if_local(adt_def.did(), s),
        rustc_type_ir::TyKind::FnDef(did, _) => prepend_crate_if_local(*did, s),
        rustc_type_ir::TyKind::Ref(region, inner_ty, _) => match region.get_name(ctxt.tcx) {
            Some(sym) => {
                "&".to_owned()
                    + sym.as_str()
                    + " "
                    + &prepend_crate_if_local_for_type(ctxt, inner_ty, inner_ty.to_string())
            }
            None => {
                "&".to_owned()
                    + &prepend_crate_if_local_for_type(ctxt, inner_ty, inner_ty.to_string())
            }
        },
        _ => s,
    }
}

fn prepend_crate_if_local<'tcx>(external_def_id: DefId, s: String) -> String {
    if external_def_id.is_local() { "crate::".to_owned() + &s } else { s }
}
/// A called external item may have anonymous early-bound lifetimes.
/// These must be made explicit for the assume_specification/other declaration.
/// The RegionRenamer generates fresh lifetime names for anonymous early bound regions
/// and implements TypeFoldable in order to make the mapping and apply it.
fn build_region_renamer<'tcx>(
    ctxt: &crate::context::Context<'tcx>,
    external_def_id: DefId,
    generics: &'tcx rustc_middle::ty::Generics,
) -> Result<RegionRenamer<'tcx>, Arc<vir::messages::MessageX>> {
    let substs_early = crate::rust_to_vir_func::get_substs_early(
        ctxt.tcx.type_of(external_def_id).instantiate_identity(),
        ctxt.tcx.def_span(external_def_id),
    )?;
    let early_lifetimes = substs_early.iter().filter_map(GenericArg::as_region);
    let mut region_renamer = RegionRenamer::new(ctxt.tcx, external_def_id);
    for param_idx in 0..generics.count() {
        let param = generics.param_at(param_idx, ctxt.tcx);
        if let GenericParamDefKind::Lifetime = param.kind {
            region_renamer.used_names.insert(param.name.to_ident_string());
        }
    }
    early_lifetimes.clone().for_each(|r| region_renamer.log_name(r));
    early_lifetimes.for_each(|r| {
        region_renamer.rename_if_anon_early(r);
    });
    Ok(region_renamer)
}

fn build_where_clauses<'tcx>(
    ctxt: &crate::context::Context<'tcx>,
    inst_predicates: InstantiatedPredicates<'tcx>,
    mut unsized_type_params: BTreeSet<rustc_span::Symbol>,
) -> Result<Vec<String>, VirErr> {
    let mut where_clauses: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let string_clauses = inst_predicates.iter().filter_map(|(pred_clause, _)| {
        match pred_clause.kind().skip_binder() {
            rustc_type_ir::ClauseKind::Trait(trait_predicate) => {
                // Check if this is an implicit Sized trait bound.
                if Some(trait_predicate.trait_ref.def_id) == ctxt.tcx.lang_items().sized_trait() {
                    let arg = trait_predicate
                        .trait_ref
                        .args
                        .first()
                        .expect("Sized should have an arg")
                        .as_type()
                        .expect("Arg of Sized should be a type");
                    match arg.kind() {
                        rustc_type_ir::TyKind::Param(param_ty) => {
                            // If we have a Sized bound for a type param, we do not need a ?Sized bound.
                            unsized_type_params.remove(&param_ty.name);
                            None
                        }
                        _ => {
                            let trait_args = trait_predicate.trait_ref.args;
                            let trait_with_args_str = ctxt.tcx.def_path_str_with_args(
                                trait_predicate.trait_ref.def_id,
                                trait_args,
                            );
                            // A sized trait on a non type param, such as an associated type.
                            Some((trait_predicate.self_ty().to_string(), trait_with_args_str))
                        }
                    }
                } else {
                    // Assuming that trait ref args for an fn trait are [self_ty, args_tuple]
                    let trait_ref = trait_predicate.trait_ref;
                    if ctxt.tcx.is_fn_trait(trait_ref.def_id) {
                        let mut args_tuple_ty_str = trait_ref.args[1].to_string().split_off(1);
                        args_tuple_ty_str.pop(); // remove trailing paren
                        Some((
                            trait_predicate.self_ty().to_string(),
                            format!(
                                "{}({})",
                                ctxt.tcx.def_path_str(trait_ref.def_id),
                                args_tuple_ty_str,
                            ),
                        ))
                    } else {
                        let trait_args = trait_predicate.trait_ref.args;
                        let trait_with_args_str = ctxt
                            .tcx
                            .def_path_str_with_args(trait_predicate.trait_ref.def_id, trait_args);
                        Some((
                            prepend_crate_if_local_for_type(
                                ctxt,
                                &trait_predicate.self_ty(),
                                trait_predicate.self_ty().to_string(),
                            ),
                            prepend_crate_if_local(
                                trait_predicate.trait_ref.def_id,
                                trait_with_args_str.to_string(),
                            ),
                        ))
                    }
                }
            }
            rustc_type_ir::ClauseKind::ConstArgHasType(_, _) => {
                // These were already handled and need to be in the inline declaration of the param.
                None
            }
            rustc_type_ir::ClauseKind::RegionOutlives(outlives_predicate) => {
                Some((outlives_predicate.0.to_string(), outlives_predicate.1.to_string()))
            }
            rustc_type_ir::ClauseKind::TypeOutlives(_outlives_predicate) => {
                // Type outlive clauses conflict with the predicates_match logic.
                None // Some((outlives_predicate.0.to_string(), outlives_predicate.1.to_string()))
            }
            rustc_type_ir::ClauseKind::Projection(projection_predicate) => {
                let (trait_ref, proj_term_args) =
                    projection_predicate.projection_term.trait_ref_and_own_args(ctxt.tcx);
                let projected_item_id = projection_predicate.projection_term.def_id;
                // Assuming here that the only projection predicate possible on an Fn trait is the Output restriction.
                // Assuming that trait ref args for an fn trait are [self_ty, args_tuple]
                if ctxt.tcx.is_fn_trait(trait_ref.def_id) {
                    // The args of a Fn trait are implicitly wrapped in a Tuple
                    let mut args_tuple_ty_str = trait_ref.args[1].to_string().split_off(1);
                    args_tuple_ty_str.pop(); // remove starting paren (above) and trailing paren
                    Some((
                        projection_predicate.self_ty().to_string(),
                        format!(
                            "{}({}) -> {}",
                            ctxt.tcx.def_path_str(trait_ref.def_id),
                            args_tuple_ty_str,
                            projection_predicate.term,
                        ),
                    ))
                } else {
                    Some((
                        projection_predicate.self_ty().to_string(),
                        format!(
                            "{}<{} = {}>",
                            ctxt.tcx.def_path_str_with_args(trait_ref.def_id, proj_term_args),
                            ctxt.tcx.item_name(projected_item_id).as_str(),
                            projection_predicate.term
                        ),
                    ))
                }
            }
            rustc_type_ir::ClauseKind::WellFormed(_) => None,
            rustc_type_ir::ClauseKind::ConstEvaluatable(_) => None,
            rustc_type_ir::ClauseKind::HostEffect(_) => None,
            rustc_type_ir::ClauseKind::UnstableFeature(_) => None,
        }
    });
    // Group the clauses by ident.
    for (ident, clause) in string_clauses {
        if !where_clauses.contains_key(&ident) {
            where_clauses.insert(ident.clone(), Vec::new());
        }
        where_clauses.get_mut(&ident).unwrap().push(clause);
    }

    // Add ?Sized clauses to those type params that need them.
    for unsized_arg in unsized_type_params {
        let ident = unsized_arg.to_ident_string();
        if !where_clauses.contains_key(&ident) {
            where_clauses.insert(ident.clone(), Vec::new());
        }
        where_clauses.get_mut(&ident).unwrap().push("?Sized".to_owned());
    }

    // Eliminate any clauses that are prefixes of other clauses.
    // This hack removes the trait refs that are implied by projection clauses.
    where_clauses.iter_mut().for_each(|(_, clause_set)| {
        let new_set = clause_set.clone();
        clause_set.retain(|c| !new_set.iter().any(|c2| c2.starts_with(c) && c2 != c));
    });

    // Fold the clauses into sums per clause self_ty
    let clause_vec: Vec<String> = where_clauses
        .iter_mut()
        .filter_map(|(ident, clause_set)| {
            let clauses = clause_set.drain(..).reduce(|acc, x| acc + " + " + &x);
            clauses.map(|c| format!("{}: {}", ident, c))
        })
        .collect();
    Ok(clause_vec)
}

fn build_generics_declarations<'tcx>(
    ctxt: &crate::context::Context<'tcx>,
    generics: &'tcx rustc_middle::ty::Generics,
    predicates: &InstantiatedPredicates,
    region_renamer: &RegionRenamer<'tcx>,
) -> Result<
    (Vec<(&'tcx rustc_middle::ty::GenericParamDef, String)>, BTreeSet<rustc_span::Symbol>),
    VirErr,
> {
    let mut param_declarations: Vec<_> = Vec::new();
    let mut unsized_type_params = BTreeSet::new();

    // If there is a const generic parameter, the type of it becomes a predicate.
    // Extract these ConstArgHasType predicates.
    let const_types: Vec<_> = predicates
        .iter()
        .filter_map(|(pred, _)| match pred.kind().skip_binder() {
            rustc_type_ir::ClauseKind::ConstArgHasType(c, t) => Some((c, t)),
            _ => None,
        })
        .collect();

    for param_idx in 0..generics.count() {
        let param = generics.param_at(param_idx, ctxt.tcx);

        let name =
            match param.kind {
                rustc_middle::ty::GenericParamDefKind::Lifetime => {
                    match region_renamer.renamed_region_map.get(&param.def_id) {
                        Some(renamed_r) => renamed_r.get_name_or_anon(ctxt.tcx),
                        None => param.name,
                    }
                    .to_ident_string()
                }
                rustc_middle::ty::GenericParamDefKind::Type { .. } => {
                    unsized_type_params.insert(param.name);
                    param.name.to_ident_string()
                }
                rustc_middle::ty::GenericParamDefKind::Const { .. } => {
                    let type_predicate =
                        const_types.iter().find_map(|(c, t)| match c.kind() {
                            rustc_type_ir::ConstKind::Param(p) => {
                                if (p.index as usize) == param_idx { Some(t) } else { None }
                            }
                            _ => None,
                        });
                    if let Some(t) = type_predicate {
                        "const ".to_owned() + &param.name.to_ident_string() + ": " + &t.to_string()
                    } else {
                        return crate::util::err_span(
                            ctxt.tcx.def_span(param.def_id),
                            format!(
                                "Could not find type for const generic parameter {}",
                                param.name.as_str()
                            ),
                        );
                    }
                }
            };

        param_declarations.push((param, name));
    }
    Ok((param_declarations, unsized_type_params))
}

pub(crate) fn build_const_assume_specification_suggestion<'tcx>(
    _ctxt: &Context<'tcx>,
    _external_def_id: DefId,
    _path: &Arc<vir::ast::PathX>,
) -> Result<String, VirErr> {
    Err(crate::util::error("const suggestion not supported"))
}

/// Suggestions should have idiomatic region names.
/// The RegionRenamer allows regions which are params
/// to be renamed.  In particular it looks for anonymous
/// early bound lifetimes, which must be explicit for
/// assume_specification to work.
///
/// The generated names are in the pattern 'a, 'b, ...
struct RegionRenamer<'tcx> {
    tcx: TyCtxt<'tcx>,
    target_def_id: DefId,
    used_names: HashSet<String>,
    last_name_generated: Vec<u8>,
    renamed_region_map: HashMap<DefId, rustc_middle::ty::Region<'tcx>>,
}
impl<'tcx> TypeFolder<TyCtxt<'tcx>> for RegionRenamer<'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn fold_region(
        &mut self,
        r: <TyCtxt<'tcx> as Interner>::Region,
    ) -> <TyCtxt<'tcx> as Interner>::Region {
        self.rename_if_anon_early(r)
    }
}
impl<'tcx> RegionRenamer<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, target_def_id: DefId) -> Self {
        Self {
            tcx,
            target_def_id,
            used_names: HashSet::new(),
            last_name_generated: Vec::new(),
            renamed_region_map: HashMap::new(),
        }
    }
    /// Alphabetically increments the current name,
    /// adding another letter if necessary.
    /// Returns the new name, which is not guaranteed to be fresh.
    fn increment_name(&mut self) -> String {
        let last_char = self.last_name_generated.pop();
        match last_char {
            None => {
                self.last_name_generated.push(b'\'');
                self.last_name_generated.push(b'a');
            }
            Some(b'z') => {
                self.last_name_generated.push(b'z');
                self.last_name_generated.push(b'a');
            }
            Some(c) => {
                self.last_name_generated.push(c + 1);
            }
        }
        String::from_utf8_lossy(&self.last_name_generated).to_string()
    }
    /// Returns a fresh name by calling `increment_name`
    /// until the yielded name is fresh.
    fn fresh_name(&mut self) -> String {
        loop {
            let name = self.increment_name();
            if !self.used_names.contains(&name) {
                self.used_names.insert(name.clone());
                return name;
            }
            if self.last_name_generated.len() > 5 {
                panic!("Generated fresh lifetime name over len 5, something is wrong.")
            }
        }
    }
    fn rename_if_anon_early(
        &mut self,
        r: rustc_middle::ty::Region<'tcx>,
    ) -> rustc_middle::ty::Region<'tcx> {
        match r.get_name(self.tcx) {
            Some(_) => r,
            None => self.rename_region_if_early(r),
        }
    }
    fn log_name(&mut self, r: rustc_middle::ty::Region<'tcx>) {
        if let Some(s) = r.get_name(self.tcx) {
            self.used_names.insert(s.to_ident_string());
        }
    }

    fn rename_region_if_early(
        &mut self,
        r: rustc_middle::ty::Region<'tcx>,
    ) -> rustc_middle::ty::Region<'tcx> {
        // We only want to rename parameters, so skip over anything that doesn't have a DefId
        let def_id = match r.opt_param_def_id(self.tcx, self.target_def_id) {
            Some(did) => did,
            None => return r,
        };
        // If the region has already been renamed, return the new region.
        if let Some(replacement_region) = self.renamed_region_map.get(&def_id) {
            *replacement_region
        } else if let rustc_type_ir::RegionKind::ReEarlyParam(inner_region) = r.kind() {
            let replacement_region = rustc_middle::ty::Region::new_early_param(
                self.tcx,
                EarlyParamRegion {
                    index: inner_region.index,
                    name: rustc_span::Symbol::intern(&self.fresh_name()),
                },
            );
            self.renamed_region_map.insert(def_id, replacement_region);
            replacement_region
        } else {
            r
        }
    }
}

struct VisibilityWalker<'tcx> {
    tcx: TyCtxt<'tcx>,
    visibilities: HashMap<DefId, Option<&'tcx DefId>>,
}
impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for VisibilityWalker<'tcx> {
    fn visit_ty(&mut self, t: <TyCtxt<'tcx> as Interner>::Ty) -> Self::Result {
        let did = match t.kind() {
            TyKind::Adt(adt_def, _) => Some(adt_def.did()),
            TyKind::Foreign(def_id)
            | TyKind::FnDef(def_id, _)
            | TyKind::Closure(def_id, _)
            | TyKind::Coroutine(def_id, _)
            | TyKind::CoroutineClosure(def_id, _)
            | TyKind::CoroutineWitness(def_id, _) => Some(*def_id),
            _ => None,
        };
        // Not completely sure about this visibility judgement.  Are there cases in which the result
        // of visible_parent_map is None but a suggestion could still be built?
        did.and_then(|did| {
            self.visibilities.insert(did, self.tcx.visible_parent_map(()).get(&did))
        });
        t.super_visit_with(self);
    }
}
