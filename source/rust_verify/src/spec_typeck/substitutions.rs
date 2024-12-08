use crate::spec_typeck::State;
use rustc_hir::def_id::DefId;
use vir::ast::{Typs, Typ, VirErr};
use vir::sst_util::subst_typ;
use rustc_span::Span;
use std::collections::HashMap;
use crate::rust_to_vir_base::mid_ty_to_vir;
use std::sync::Arc;

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn fn_item_type_substitution(&mut self, span: Span, def_id: DefId, typ_args: &Typs)
        -> Result<(Typs, Typ), VirErr>
    {
        // TODO duplicate work
        let (sig_typ_params, _sig_typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_no_polarity(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            span,
            None,
            def_id,
            Some(&mut *self.bctx.ctxt.diagnostics.borrow_mut()),
        )?;

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

        Ok((Arc::new(vir_input_typs), vir_output_typ))
    }

    /*pub fn item_type_substitution(&mut self, def_id: DefId, typ_args: &Typs)
        -> Result<(Typs, Typ), VirErr>
    {
    }*/
}
