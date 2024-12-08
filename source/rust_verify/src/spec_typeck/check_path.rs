use rustc_hir::def_id::DefId;
use rustc_hir::hir_id::HirId;
use rustc_hir::{PrimTy, QPath, GenericArg, PathSegment};
use rustc_hir::def::{Res, DefKind};
use rustc_hir::def_id::LocalDefId;
use vir::ast::{Typ, Typs, Ident, VirErr};
use crate::spec_typeck::State;
use std::sync::Arc;
use rustc_span::Span;
use rustc_middle::ty::{Ty, TyCtxt, GenericParamDef, Region, Const, GenericPredicates, AdtDef, Generics, PolyTraitRef, GenericParamDefKind};
use rustc_infer::infer::InferCtxt;
use rustc_errors::ErrorGuaranteed;
use rustc_hir_analysis::hir_ty_lowering::{GenericPathSegment, IsMethodCall, GenericArgCountMismatch, HirTyLowerer};
use rustc_hir_analysis::hir_ty_lowering::generics::check_generic_arg_count_for_call;
use crate::util::err_span;
use rustc_hir::GenericArgsParentheses;
use std::collections::HashSet;

pub enum PathResolution {
    Local(HirId),
    Fn(DefId, Typs),
    Const(DefId),
    Datatype(DefId, Typs),
    DatatypeVariant(DefId, Ident, Typs),
    PrimTy(PrimTy),
}

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_qpath(
        &mut self,
        qpath: &QPath<'tcx>,
    ) -> Result<PathResolution, VirErr> {
        match qpath {
            QPath::Resolved(qualified_self, path) => {
                self.check_res(path.span, qualified_self, &path.res, path.segments)
            }
            QPath::TypeRelative(_ty, _path_segment) => {
                todo!()
            }
            QPath::LangItem(..) => {
                todo!()
            }
        }
    }

    fn check_res(
        &mut self,
        span: Span,
        qualified_self: &Option<&'tcx rustc_hir::Ty<'tcx>>,
        res: &Res,
        segments: &'tcx [PathSegment],
    ) -> Result<PathResolution, VirErr> {
        match res {
            Res::Def(def_kind, def_id) => {
                match def_kind {
                    DefKind::Fn => {
                        let generic_params = self.check_path_generics(span, qualified_self, *def_kind, *def_id, segments)?;
                        Ok(PathResolution::Fn(*def_id, Arc::new(generic_params)))
                    }
                    DefKind::Struct => {
                        assert!(qualified_self.is_none());
                        let generic_params = self.check_path_generics_last_only(*def_id, segments)?;
                        Ok(PathResolution::Datatype(*def_id, Arc::new(generic_params)))
                    }
                    _ => todo!()
                }
            }
            Res::PrimTy(prim_ty) => Ok(PathResolution::PrimTy(*prim_ty)),
            Res::Local(id) => Ok(PathResolution::Local(*id)),
            _ => todo!(),
        }
    }

    pub fn check_path_generics_last_only(
        &mut self,
        def_id: DefId,
        segments: &'tcx [PathSegment],
    ) -> Result<Vec<Typ>, VirErr> {
        for seg in segments.split_last().unwrap().1.iter() {
            if seg.args.is_some() {
                return err_span(seg.args.unwrap().span_ext, "unexpected generic arguments here");
            }
        }
        let generics = self.tcx.generics_of(def_id);
        self.check_segment_generics(&segments[segments.len() - 1], generics)
    }

    pub fn check_path_generics(
        &mut self,
        span: Span,
        qualified_self: &Option<&'tcx rustc_hir::Ty<'tcx>>,
        def_kind: DefKind,
        def_id: DefId,
        segments: &'tcx [PathSegment],
    ) -> Result<Vec<Typ>, VirErr> {
        assert!(qualified_self.is_none());
        let generic_segments = self.lowerer().probe_generic_path_segments(
            segments, None, def_kind, def_id, span);
        let mut idx_set = HashSet::new();
        for GenericPathSegment(def_id, index) in &generic_segments {
            let seg = &segments[*index];
            let generics = self.tcx.generics_of(def_id);
            let arg_count = check_generic_arg_count_for_call(self.tcx, *def_id, generics, seg, IsMethodCall::No);
            if let Err(GenericArgCountMismatch { .. }) = arg_count.correct {
                return err_span(seg.args.unwrap().span_ext, "too many generic arguments here");
            }
            idx_set.insert(*index);
        }

        for i in 0 .. segments.len() {
            if !idx_set.contains(&i) {
                if segments[i].args.is_some() {
                    return err_span(segments[i].args.unwrap().span_ext, "unexpected generic arguments here");
                }
            }
        }

        let mut generic_params = vec![];
        for GenericPathSegment(def_id, index) in &generic_segments {
            let seg = &segments[*index];
            let generics = self.tcx.generics_of(def_id);
            generic_params.append(&mut self.check_segment_generics(seg, generics)?);
        }
        Ok(generic_params)
    }

    pub fn check_segment_generics(&mut self, segment: &'tcx PathSegment, generics: &'tcx Generics) -> Result<Vec<Typ>, VirErr> {
        if let Some(args) = &segment.args {
            if args.bindings.len() > 0 {
                todo!();
            }
            if !matches!(args.parenthesized, GenericArgsParentheses::No) {
                todo!();
            }
        }

        let mut idx = 0;
        let get_next_segment_arg = &mut || {
            match &segment.args {
                None => None,
                Some(args) => {
                    while idx < args.args.len() && matches!(args.args[idx], GenericArg::Lifetime(_)) {
                        idx += 1
                    }
                    if idx < args.args.len() {
                        idx += 1;
                        Some(&args.args[idx - 1])
                    } else {
                        None
                    }
                }
            }
        };

        let mut v: Vec<Typ> = vec![];
        for generic_param_def in generics.params.iter() {
            match &generic_param_def.kind {
                GenericParamDefKind::Lifetime => { }
                GenericParamDefKind::Type { has_default, synthetic } => {
                    if *has_default { todo!() }
                    if *synthetic { todo!() }

                    let arg = get_next_segment_arg();
                    let typ = match arg {
                        None => self.new_unknown_typ(),
                        Some(GenericArg::Lifetime(_)) => unreachable!(),
                        Some(arg @ GenericArg::Const(_)) => {
                            return err_span(arg.span(), "unexpected const param (normal type param expected)");
                        }
                        Some(GenericArg::Infer(_)) => self.new_unknown_typ(),
                        Some(GenericArg::Type(ty)) => self.check_ty(ty)?,
                    };
                    v.push(typ);
                }
                GenericParamDefKind::Const { has_default, is_host_effect: false } => {
                    if *has_default { todo!() }
                    todo!()
                }
                GenericParamDefKind::Const { has_default: _, is_host_effect: true } => { }
            }
        }

        if let Some(next) = get_next_segment_arg() {
            return err_span(next.span(), "unexpected type param");
        }

        Ok(v)
    }

    pub fn get_item_mode(&self, def_id: DefId) -> Result<vir::ast::Mode, VirErr> {
        match def_id.as_local() {
            Some(local_def_id) => {
                let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
                let attrs = self.tcx.hir().attrs(hir_id);
                let mode = crate::attributes::get_mode_opt(attrs);
                match mode {
                    Some(mode) => Ok(mode),
                    None => Ok(vir::ast::Mode::Exec),
                }
            }
            None => {
                todo!()
            }
        }
    }
}

// Implement this trait so we can call probe_generic_path_segments
impl<'a, 'tcx> HirTyLowerer<'tcx> for State<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> { self.tcx }

    fn item_def_id(&self) -> DefId { unreachable!() }

    fn allow_infer(&self) -> bool { unreachable!() }

    fn re_infer(
        &self,
        _param: Option<&GenericParamDef>,
        _span: Span
    ) -> Option<Region<'tcx>> { unreachable!() }

    fn ty_infer(&self, _param: Option<&GenericParamDef>, _span: Span) -> Ty<'tcx> {
        unreachable!()
    }

    fn ct_infer(
        &self,
        _ty: Ty<'tcx>,
        _param: Option<&GenericParamDef>,
        _span: Span
    ) -> Const<'tcx> { unreachable!() }

    fn probe_ty_param_bounds(
        &self,
        _span: Span,
        _def_id: LocalDefId,
        _assoc_name: rustc_span::symbol::Ident
    ) -> GenericPredicates<'tcx> { unreachable!() }

    fn lower_assoc_ty(
        &self,
        _span: Span,
        _item_def_id: DefId,
        _item_segment: &rustc_hir::PathSegment,
        _poly_trait_ref: PolyTraitRef<'tcx>
    ) -> Ty<'tcx> { unreachable!() }

    fn probe_adt(&self, _span: Span, _ty: Ty<'tcx>) -> Option<AdtDef<'tcx>> {
        todo!()
    }

    fn record_ty(&self, _hir_id: HirId, _ty: Ty<'tcx>, _span: Span) {
        unreachable!()
    }

    fn infcx(&self) -> Option<&InferCtxt<'tcx>> {
        unreachable!()
    }

    fn set_tainted_by_errors(&self, _e: ErrorGuaranteed) {
        unreachable!()
    }
}
