use crate::spec_typeck::State;
use rustc_hir::def_id::DefId;
use vir::ast::{Typs, Typ, VirErr};
use vir::sst_util::subst_typ;
use rustc_span::Span;
use std::collections::HashMap;
use crate::rust_to_vir_base::mid_ty_to_vir;
use std::sync::Arc;
use rustc_middle::ty::{Generics, GenericParamDefKind, GenericParamDef, VariantDef};

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn fn_item_type_substitution(&mut self, span: Span, def_id: DefId, typ_args: &Typs)
        -> Result<(Typs, Typ), VirErr>
    {
        let mut sig_typ_params: Vec<vir::ast::Ident> = vec![];

        let generic_defs = self.get_generic_defs(self.tcx.generics_of(def_id));
        let has_self = self.tcx.trait_of_item(def_id).is_some();
        if has_self {
            sig_typ_params.push(vir::def::trait_self_type_param());
        }
        for generic_def in generic_defs.iter().skip(has_self as usize) {
            match &generic_def.kind {
                GenericParamDefKind::Type { synthetic: _, has_default: _ } | GenericParamDefKind::Const { is_host_effect: false, has_default: _ } => {
                    let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(generic_def);
                    sig_typ_params.push(Arc::new(ident));
                }
                GenericParamDefKind::Const { is_host_effect: true, .. } => { }
                GenericParamDefKind::Lifetime => { }
            }
        }

        let mut typ_substs = HashMap::new();
        assert!(sig_typ_params.len() == typ_args.len());
        for (param_ident, typ_arg) in sig_typ_params.iter().zip(typ_args.iter()) {
            typ_substs.insert(param_ident.clone(), typ_arg.clone());
        }

        let fn_sig = self.tcx.fn_sig(def_id);

        let inputs = fn_sig.skip_binder().inputs().skip_binder();
        let mut vir_input_typs = vec![];
        for input in inputs.iter() {
            let vir_typ = mid_ty_to_vir(
                self.tcx,
                &self.bctx.ctxt.verus_items,
                def_id,
                span,
                input,
                false,
            )?;
            let vir_typ = subst_typ(&typ_substs, &vir_typ);
            let vir_typ = self.normalize_typ(&vir_typ);
            vir_input_typs.push(vir_typ);
        }

        let vir_output_typ = mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            def_id,
            span,
            &fn_sig.skip_binder().output().skip_binder(),
            false,
        )?;
        let vir_output_typ = subst_typ(&typ_substs, &vir_output_typ);
        let vir_output_typ = self.normalize_typ(&vir_output_typ);

        Ok((Arc::new(vir_input_typs), vir_output_typ))
    }

    /*pub fn item_type_substitution(&mut self, def_id: DefId, typ_args: &Typs)
        -> Result<(Typs, Typ), VirErr>
    {
    }*/

    fn get_generic_defs(&self, generics: &Generics) -> Vec<GenericParamDef> {
        match &generics.parent {
            None => generics.params.clone(),
            Some(parent_id) => {
                let mut v = self.get_generic_defs(self.tcx.generics_of(parent_id));
                v.append(&mut generics.params.clone());
                v
            }
        }
    }

    pub fn item_type_substitution(&mut self, span: Span, def_id: DefId, typ_args: &Typs)
        -> Result<Typ, VirErr>
    {
        let mut sig_typ_params: Vec<vir::ast::Ident> = vec![];

        let generic_defs = self.get_generic_defs(self.tcx.generics_of(def_id));
        for generic_def in generic_defs.iter() {
            match &generic_def.kind {
                GenericParamDefKind::Type { synthetic: _, has_default: _ } | GenericParamDefKind::Const { is_host_effect: false, has_default: _ } => {
                    let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(generic_def);
                    sig_typ_params.push(Arc::new(ident));
                }
                GenericParamDefKind::Const { is_host_effect: true, .. } => { }
                GenericParamDefKind::Lifetime => { }
            }
        }

        let mut typ_substs = HashMap::new();
        assert!(sig_typ_params.len() == typ_args.len());
        for (param_ident, typ_arg) in sig_typ_params.iter().zip(typ_args.iter()) {
            typ_substs.insert(param_ident.clone(), typ_arg.clone());
        }

        let item_ty = self.tcx.type_of(def_id).skip_binder();

        let vir_item_typ = mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            def_id,
            span,
            &item_ty,
            false,
        )?;
        let vir_item_typ = subst_typ(&typ_substs, &vir_item_typ);
        let vir_item_typ = self.normalize_typ(&vir_item_typ);

        Ok(vir_item_typ)
    }

    pub fn get_field_typ_positional(&mut self, span: Span, variant_def: &VariantDef, typ_args: &Typs, i: usize) -> Result<Typ, VirErr> {
        self.get_field_typ(span, variant_def, typ_args, &format!("{:}", i))
    }

    pub fn get_field_typ(&mut self, span: Span, variant_def: &VariantDef, typ_args: &Typs, field: &str) -> Result<Typ, VirErr> {
        let mut sig_typ_params: Vec<vir::ast::Ident> = vec![];

        let generic_defs = self.get_generic_defs(self.tcx.generics_of(variant_def.def_id));
        for generic_def in generic_defs.iter() {
            match &generic_def.kind {
                GenericParamDefKind::Type { synthetic: _, has_default: _ } | GenericParamDefKind::Const { is_host_effect: false, has_default: _ } => {
                    let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(generic_def);
                    sig_typ_params.push(Arc::new(ident));
                }
                GenericParamDefKind::Const { is_host_effect: true, .. } => { }
                GenericParamDefKind::Lifetime => { }
            }
        }

        let mut typ_substs = HashMap::new();
        assert!(sig_typ_params.len() == typ_args.len());
        for (param_ident, typ_arg) in sig_typ_params.iter().zip(typ_args.iter()) {
            typ_substs.insert(param_ident.clone(), typ_arg.clone());
        }

        let mut field_def = None;
        for fd in variant_def.fields.iter() {
            if fd.ident(self.tcx).as_str() == field {
                field_def = Some(fd);
                break;
            }
        }
        let field_def = field_def.unwrap();
        let field_ty = self.tcx.type_of(field_def.did).skip_binder();

        let vir_field_typ = mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            variant_def.def_id,
            span,
            &field_ty,
            false,
        )?;
        let vir_field_typ = subst_typ(&typ_substs, &vir_field_typ);
        let vir_field_typ = self.normalize_typ(&vir_field_typ);

        Ok(vir_field_typ)
       
    }
}
