use crate::util::{
    err_span,
};
use crate::spec_typeck::State;
use vir::ast::{PatternX, Pattern, Typ, VirErr, VarIdent};
use rustc_hir::{PatKind, BindingMode, ByRef, Mutability, Pat};
use rustc_span::Span;

impl State<'_, '_> {
    /// Checks the pattern and adds bindings to the scope map
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
            PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), hir_id, ident, None) => {
                let var_ident = crate::rust_to_vir_base::local_to_var(ident, hir_id.local_id);
                add_binding(pat.span, bindings, var_ident.clone(), typ)?;
                mk_pattern(PatternX::Var { name: var_ident, mutable: false })
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

