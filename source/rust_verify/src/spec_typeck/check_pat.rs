use crate::util::{
    err_span,
};
use crate::spec_typeck::State;
use vir::ast::{PatternX, Pattern, Typ, VirErr, VarIdent, TypX, Dt, Binder};
use rustc_hir::{PatKind, BindingMode, ByRef, Mutability, Pat};
use rustc_span::Span;
use crate::rust_to_vir_expr::handle_dot_dot;
use std::sync::Arc;
use vir::ast_util::mk_tuple_typ;
use air::ast_util::ident_binder;
use vir::def::positional_field_ident;

impl State<'_, '_> {
    /// Checks that the pattern matches the expected type, and adds bindings to the scope map

    pub fn check_pat<'tcx>(
        &mut self,
        pat: &Pat,
        typ: &Typ,
    ) -> Result<Pattern, VirErr>
    {
        let mut bindings = vec![];
        let pat = self.check_pat_rec(pat, typ, &mut bindings)?;

        for (var_ident, typ) in bindings.into_iter() {
            self.scope_map.insert(var_ident, typ).expect("scope_map insert");
        }

        Ok(pat)
    }

    fn check_pat_rec<'tcx>(
        &mut self,
        pat: &Pat<'tcx>,
        typ: &Typ,
        bindings: &mut Vec<(VarIdent, Typ)>,
    ) -> Result<Pattern, VirErr> {
        let bctx = self.bctx;
        let mk_pattern = |x| Ok(bctx.spanned_typed_new(pat.span, typ, x));

        match &pat.kind {
            PatKind::Wild => {
                mk_pattern(PatternX::Wildcard(false))
            }
            PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), hir_id, ident, None) => {
                let var_ident = crate::rust_to_vir_base::local_to_var(ident, hir_id.local_id);
                add_binding(pat.span, bindings, var_ident.clone(), typ)?;
                mk_pattern(PatternX::Var { name: var_ident, mutable: false })
            }
            PatKind::Tuple(pats, dot_dot_pos) => {
                let t = self.get_typ_with_concrete_head_if_possible(typ)?;
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
                        self.expect_exact(typ, &tup_typ)?;
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
                    let pattern = self.check_pat_rec(pat, &typs[actual_idx], bindings)?;
                    let binder = ident_binder(&positional_field_ident(actual_idx), &pattern);
                    binders.push(binder);
                }

                let variant_name = vir::def::prefix_tuple_variant(n);
                mk_pattern(PatternX::Constructor(Dt::Tuple(n), variant_name, Arc::new(binders)))
            }
            _ => todo!(),
        }
    }
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

