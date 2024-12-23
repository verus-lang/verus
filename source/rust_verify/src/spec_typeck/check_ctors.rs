use crate::util::{err_span};
use crate::verus_items;
use crate::unsupported_err;
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs, FieldOpr, VariantCheck, UnaryOpr};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind, Body, PatKind, BindingMode, ByRef, Mutability, BinOpKind, FnRetTy, StmtKind, LetStmt, ExprField, PatField};
use std::sync::Arc;
use vir::ast_util::{unit_typ, int_typ, integer_typ, bool_typ, nat_typ, typ_to_diagnostic_str};
use crate::spec_typeck::check_ty::{integer_typ_of_int_ty, integer_typ_of_uint_ty};
use rustc_ast::ast::{LitKind, LitIntType};
use num_bigint::BigInt;
use rustc_span::Span;
use vir::def::{field_ident_from_rust, positional_field_ident};
use air::ast_util::{ident_binder, str_ident};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{AdtDef, VariantDef};
use std::collections::HashSet;
use rustc_hir::def::CtorKind;
use crate::verus_items::VerusItem;
use rustc_hir::QPath;
use rustc_hir::def::Res;

impl<'a, 'tcx> State<'a, 'tcx> {
    /* Some notes about how Rust / rustc works with variants:

    Any variant can optionally have a "constructor", which is either
    CtorKind::Const or CtorKind::Fn.

    enum Foo {
        VariantConst                  // Some(CtorKind::Const)
        VariantFn(bool)               // Some(CtorKind::Fn)
        VariantBraces { b: bool }     // None
    }

    struct StructConst;               // Some(CtorKind::Const)
    struct StructFn(bool);            // Some(CtorKind::Fn)
    struct StructBraces { b: bool }   // None

    Now, when writing a 'Struct' expression or pattern (with braces), any of these 3 kinds
    is acceptable. For const-style, it would be empty (StructConst { }) and for paren-style
    you would add numeric fields: (StructFn { 0: true }).

    When a variant shows up as a constant (or in a function call) however, it has
    to be a constructor.

    This is valid:
     - VariantConst
     - VariantFn(b)

    This is invalid:
     - VariantConst(b)

    Of course, rustc lets you use VariantFn on its own without calling it; it has function type.
    (But this isn't supported by us right now.)
    */

    /// Check if a 'braces-style construct' (e.g., `Foo { a, b, c }`) is valid
    /// for:
    ///  - structs and unions in expressions 
    ///  - structs in patterns
    /// Errors for enums.
    ///
    /// This checks if all field names are valid and that there are no duplicates.
    ///
    /// Caller should provide either `expr_fields` or `pat_fields`; put empty list []
    /// for the other.
    ///
    /// can_skip_fields: If true, you're allowed to skip fields, otherwise, you must
    /// provide all fields. For a struct, this should be true if a spread is provided,
    /// and for patterns, this should be true if a '..' is a provided.

    pub(crate) fn check_braces_struct_valid(
        &mut self,
        def_id: DefId,
        expr_fields: &'tcx [ExprField<'tcx>],
        pat_fields: &'tcx [PatField<'tcx>],
        can_skip_fields: bool,
        span: Span,
    ) -> Result<(Ident, &'tcx VariantDef), VirErr> {
        let adt_def = self.tcx.adt_def(def_id);
        if adt_def.is_struct() {
            let variant_def = adt_def.non_enum_variant();
            self.check_braces_variant_valid(&adt_def, variant_def, expr_fields, pat_fields, can_skip_fields, span)?;
            let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
            Ok((variant_name, variant_def))
        } else if adt_def.is_union() {
            todo!()
        } else if adt_def.is_enum() {
            return err_span(span, "this is an enum, so a variant must be provided");
        } else {
            unreachable!();
        }
    }

    pub(crate) fn check_braces_variant_valid(
        &mut self,
        adt_def: &AdtDef,
        variant_def: &'tcx VariantDef,
        expr_fields: &'tcx [ExprField<'tcx>],
        pat_fields: &'tcx [PatField<'tcx>],
        can_skip_fields: bool,
        span: Span,
    ) -> Result<(), VirErr> {
        let is_valid_field = |name: &str| variant_def.fields.iter().any(|f| f.ident(self.tcx).as_str() == name);

        let mut seen_fields = HashSet::<String>::new();

        let idents = expr_fields.iter().map(|f| (f.ident.as_str(), f.span))
               .chain(pat_fields.iter().map(|f| (f.ident.as_str(), f.span)));

        for (f_ident, span) in idents {
            if !is_valid_field(f_ident) {
                if adt_def.is_struct() {
                    return err_span(span,
                      format!("struct `{:}` has no field named `{:}`",
                        self.def_id_to_friendly(adt_def.did()), f_ident));
                } else if adt_def.is_enum() {
                    return err_span(span,
                      format!("variant `{:}::{:}` has no field named `{:}`",
                        self.def_id_to_friendly(adt_def.did()), variant_def.ident(self.tcx).as_str(), f_ident));
                } else {
                    unreachable!()
                }
            }
            
            let not_dupe = seen_fields.insert(f_ident.to_string());
            if !not_dupe {
                return err_span(span,
                  format!("field `{:}` specified more than once", f_ident));
            }
        }

        if !can_skip_fields && seen_fields.len() != variant_def.fields.len() {
            let mut unspecified_fields = vec![];
            for f in variant_def.fields.iter() {
                if !seen_fields.contains(f.ident(self.tcx).as_str()) {
                    unspecified_fields.push(format!("`{:}`", f.ident(self.tcx).as_str()));
                }
            }
            return err_span(span,
              format!("missing {:} {:} in initializer of `{:}`",
                  if unspecified_fields.len() != 1 { "fields" } else { "field" },
                  unspecified_fields.join(", "),
                  if adt_def.is_struct() {
                    self.def_id_to_friendly(adt_def.did())
                  } else if adt_def.is_enum() {
                    format!("{:}::{:}", self.def_id_to_friendly(adt_def.did()), variant_def.ident(self.tcx).as_str())
                  } else {
                    unreachable!()
                  }));
        }

        Ok(())
    }

    pub(crate) fn braces_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        fields: &'tcx [ExprField],
        spread_opt: Option<&'tcx Expr<'tcx>>,
        adt_def_id: DefId,
        variant_def: &VariantDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                            &self.bctx.ctxt.verus_items, adt_def_id);
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let vir_spread_opt = match spread_opt {
            Some(spread) => {
                let vir_spread = self.check_expr(spread)?;
                self.expect_exact(&vir_spread.typ, &typ)?;
                Some(vir_spread)
            }
            None => None,
        };
        let mut ident_binders = vec![];
        for field in fields.iter() {
            let ExprField { hir_id: _, ident, expr: field_expr, span: _, is_shorthand: _ } = field;
            let vir_field_expr = self.check_expr(field_expr)?;
            let field_typ = self.get_field_typ(field.span, variant_def, &typ_args, &ident.as_str())?;
            self.expect_allowing_coercion(&vir_field_expr.typ, &field_typ)?;

            let ident = field_ident_from_rust(ident.as_str());
            ident_binders.push(ident_binder(&ident, &vir_field_expr));
        }

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), vir_spread_opt);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }

    pub(crate) fn parens_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        args: &'tcx [Expr],
        variant_def: &VariantDef,
        adt_def: &AdtDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        if variant_def.ctor_kind() != Some(CtorKind::Fn) {
            return err_span(span, format!("this constructor is not a function-call constructor"));
        }
        if args.len() != variant_def.fields.len() {
            return err_span(span, format!("this construtor takes {:} argument{:} but {:} argument{:} were supplied",
                variant_def.fields.len(),
                if variant_def.fields.len() != 1 { "s" } else { "" },
                args.len(),
                if args.len() != 1 { "s" } else { "" }));
        }

        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
            &self.bctx.ctxt.verus_items, adt_def.did());
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let mut ident_binders = vec![];
        for (i, arg) in args.iter().enumerate() {
            let vir_arg = self.check_expr(arg)?;
            let field_typ = self.get_field_typ_positional(span, variant_def, &typ_args, i)?;
            self.expect_allowing_coercion(&vir_arg.typ, &field_typ)?;
            let ident = positional_field_ident(i);
            ident_binders.push(ident_binder(&ident, &vir_arg));
        }

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), None);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }

    pub(crate) fn const_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        variant_def: &VariantDef,
        adt_def: &AdtDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        if variant_def.ctor_kind() != Some(CtorKind::Const) {
            return err_span(span, format!("this constructor is not a const-style constructor"));
        }
        assert!(variant_def.fields.len() == 0);

        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
            &self.bctx.ctxt.verus_items, adt_def.did());
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let ident_binders = vec![];

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), None);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }
}
