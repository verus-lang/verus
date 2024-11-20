use crate::util::{
    err_span,
};
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{PatternX, Pattern, Typ, VirErr, VarIdent, TypX, Dt, Binder, Typs, TypDecoration};
use rustc_hir::{PatKind, BindingMode, ByRef, Mutability, Pat, PatField};
use rustc_middle::ty::VariantDef;
use vir::def::{field_ident_from_rust, positional_field_ident};
use rustc_hir::def_id::DefId;
use rustc_span::Span;
use crate::rust_to_vir_expr::handle_dot_dot;
use std::sync::Arc;
use vir::ast_util::mk_tuple_typ;
use air::ast_util::ident_binder;
use air::ast_util::str_ident;
use rustc_hir::def::CtorKind;

impl<'a, 'tcx> State<'a, 'tcx> {
    /// Checks that the pattern matches the expected type, and adds bindings to the scope map

    pub fn check_pat(
        &mut self,
        pat: &Pat<'tcx>,
        expected_typ: &Typ,
    ) -> Result<Pattern, VirErr>
    {
        let mut bindings = vec![];
        let pat = self.check_pat_rec(pat, expected_typ, &mut bindings)?;

        for (var_ident, typ) in bindings.into_iter() {
            self.scope_map.insert(var_ident, typ).expect("scope_map insert");
        }

        Ok(pat)
    }

    fn check_pat_rec(
        &mut self,
        pat: &Pat<'tcx>,
        expected_typ: &Typ,
        bindings: &mut Vec<(VarIdent, Typ)>,
    ) -> Result<Pattern, VirErr> {
        let bctx = self.bctx;
        let mk_pattern = |x| Ok(bctx.spanned_typed_new(pat.span, expected_typ, x));

        match &pat.kind {
            PatKind::Wild => {
                mk_pattern(PatternX::Wildcard(false))
            }
            PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), hir_id, ident, None) => {
                let var_ident = crate::rust_to_vir_base::local_to_var(ident, hir_id.local_id);
                add_binding(pat.span, bindings, var_ident.clone(), expected_typ)?;
                mk_pattern(PatternX::Var { name: var_ident, mutable: false })
            }
            PatKind::Tuple(pats, dot_dot_pos) => {
                let t = self.get_typ_as_concrete_as_possible(expected_typ)?;
                let (t, decs) = undec(&t);
                let typs = match &*t {
                    TypX::Datatype(Dt::Tuple(n), typ_args, _) => {
                        assert!(typ_args.len() == *n);
                        typ_args.clone()
                    }
                    TypX::UnificationVar(_) => {
                        if dot_dot_pos.as_opt_usize().is_some() {
                            todo!();
                        }
                        let n = pats.len();
                        let mut typ_args = vec![];
                        for _i in 0 .. n {
                            typ_args.push(self.new_unknown_typ());
                        }
                        let typ_args = Arc::new(typ_args);
                        let tup_typ = mk_tuple_typ(&typ_args);
                        self.expect_exact(expected_typ, &tup_typ)?;
                        typ_args
                    }
                    _ => todo!(),
                };

                let n = typs.len();
                let (n_wildcards, pos_to_insert_wildcards) =
                    handle_dot_dot(pats.len(), n, &dot_dot_pos);

                let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();

                for (i, pat) in pats.iter().enumerate() {
                    let actual_idx = if i < pos_to_insert_wildcards { i } else { i + n_wildcards };
                    let field_typ = redec(typs[actual_idx].clone(), &decs);
                    let pattern = self.check_pat_rec(pat, &field_typ, bindings)?;
                    let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                    binders.push(binder);
                }

                let variant_name = vir::def::prefix_tuple_variant(n);
                mk_pattern(PatternX::Constructor(Dt::Tuple(n), variant_name, Arc::new(binders)))
            }
            PatKind::Struct(qpath, fields, has_dot_dot) => {
                match self.check_qpath_for_expr(qpath, pat.hir_id)? {
                    PathResolution::Datatype(def_id, typ_args) => {
                        // TODO visibility of fields
                        let (variant_name, variant_def) = self.check_braces_struct_valid(
                            def_id, &[], fields, *has_dot_dot, qpath.span())?;
                        self.pattern_braces_ctor(pat.span, &typ_args, fields,
                           def_id,
                           variant_def,
                           variant_name, expected_typ)
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        let variant_def = adt_def.variant_with_id(variant_def_id);
                        self.check_braces_variant_valid(&adt_def, variant_def,
                            &[], fields, *has_dot_dot, qpath.span())?;
                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
                        self.pattern_braces_ctor(pat.span, &typ_args, fields,
                           enum_did, variant_def, variant_name, expected_typ)
                    }
                    _ => {
                        return err_span(pat.span, "expected struct or enum variant");
                    }
                }
            }
            PatKind::TupleStruct(qpath, pats, dot_dot_pos) => {
                match self.check_qpath_for_expr(qpath, pat.hir_id)? {
                    PathResolution::Datatype(_def_id, _typ_args) => {
                        todo!()
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        let variant_def = adt_def.variant_with_id(variant_def_id);

                        if variant_def.ctor_kind() != Some(CtorKind::Fn) {
                            return err_span(pat.span, "expected tuple struct or tuple variant");
                        }

                        if dot_dot_pos.as_opt_usize().is_none() && pats.len() != variant_def.fields.len()
                            || pats.len() > variant_def.fields.len()
                        {
                            return err_span(pat.span, format!("this pattern has {:} field{:}, but the corresponding tuple variant has {:} field{:}",
                                pats.len(),
                                if pats.len() == 1 { "" } else { "s" },
                                variant_def.fields.len(),
                                if variant_def.fields.len() == 1 { "" } else { "s" },
                            ));
                        }

                        let vir_path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                                            &self.bctx.ctxt.verus_items, enum_did);
                        let dt = Dt::Path(vir_path);
                        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

                        let expected_typ = self.get_typ_as_concrete_as_possible(expected_typ)?;
                        let (expected_typ, decs) = undec(&expected_typ);
                        self.expect_exact(&expected_typ, &typ)?;

                        let (n_wildcards, pos_to_insert_wildcards) =
                            handle_dot_dot(pats.len(), variant_def.fields.len(), &dot_dot_pos);

                        let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
                        for (i, pat) in pats.iter().enumerate() {
                            let actual_idx = if i < pos_to_insert_wildcards { i } else { i + n_wildcards };

                            let field_typ = self.get_field_typ_positional(pat.span, variant_def, &typ_args, actual_idx)?;
                            let field_typ = redec(field_typ, &decs);
                            let pattern = self.check_pat(pat, &field_typ)?;
                            let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                            binders.push(binder);
                        }

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());

                        mk_pattern(PatternX::Constructor(dt, variant_name, Arc::new(binders)))
                    }
                    _ => {
                        return err_span(pat.span, "expected struct or enum variant");
                    }
                }
            }
            PatKind::Path(qpath) => {
                match self.check_qpath_for_expr(qpath, pat.hir_id)? {
                    PathResolution::Datatype(_def_id, _typ_args) => {
                        todo!();
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        let variant_def = adt_def.variant_with_id(variant_def_id);

                        if variant_def.ctor_kind() != Some(CtorKind::Const) {
                            return err_span(pat.span, "expected tuple struct or tuple variant");
                        }

                        assert!(variant_def.fields.len() == 0);

                        let vir_path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                                            &self.bctx.ctxt.verus_items, enum_did);
                        let dt = Dt::Path(vir_path);
                        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

                        let expected_typ = self.get_typ_as_concrete_as_possible(expected_typ)?;
                        let (expected_typ, _decs) = undec(&expected_typ);
                        self.expect_exact(&expected_typ, &typ)?;

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());

                        mk_pattern(PatternX::Constructor(dt, variant_name, Arc::new(vec![])))
                    }
                    _ => todo!()
                }
            }
            _ => {
                return err_span(pat.span, format!("Verus ghost code does not support the following pattern kind: {:?}", &pat.kind));
          }
        }
    }

    fn pattern_braces_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        fields: &'tcx [PatField],
        adt_def_id: DefId,
        variant_def: &VariantDef,
        variant_name: vir::ast::Ident,
        expected_typ: &Typ,
    ) -> Result<vir::ast::Pattern, VirErr> {
        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                            &self.bctx.ctxt.verus_items, adt_def_id);
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let expected_typ = self.get_typ_as_concrete_as_possible(expected_typ)?;
        let (expected_typ, decs) = undec(&expected_typ);
        self.expect_exact(&expected_typ, &typ)?;

        let mut ident_binders = vec![];
        for field in fields.iter() {
            let field_typ = self.get_field_typ(field.span, variant_def, &typ_args, &field.ident.as_str())?;
            let field_typ = redec(field_typ, &decs);
            let vir_pattern = self.check_pat(&field.pat, &field_typ)?;

            let ident = field_ident_from_rust(field.ident.as_str());
            ident_binders.push(ident_binder(&ident, &vir_pattern));
        }

        let x = PatternX::Constructor(dt, variant_name, Arc::new(ident_binders));
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }
}

fn undec(t: &Typ) -> (Typ, Vec<TypDecoration>) {
    let mut t = t;
    let mut v = vec![];
    loop {
        match &**t {
            TypX::Decorate(dec @ TypDecoration::Ref, None, inner) => {
                t = inner;
                v.push(*dec);
            }
            _ => { break; }
        }
    }
    (t.clone(), v)
}

fn redec(t: Typ, v: &Vec<TypDecoration>) -> Typ {
    let mut t = t;
    for dec in v.iter().rev() {
        t = Arc::new(TypX::Decorate(*dec, None, t));
    }
    t
}

fn add_binding(
    span: Span,
    bindings: &mut Vec<(VarIdent, Typ)>,
    var_ident: VarIdent,
    typ: &Typ
) -> Result<(), VirErr>
{
    for b in bindings.iter() {
        if b.0 == var_ident {
            return err_span(span, format!("identifier `{:?}` bound more than once in this pattern", b.0))
        }
    }
    bindings.push((var_ident, typ.clone()));
    Ok(())
}

