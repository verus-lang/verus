use crate::{unsupported_err};
use crate::verus_items::{VerusItem, BuiltinTypeItem};
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{Typ, VirErr, TypX, Primitive, IntRange, Dt};
use vir::ast_util::{bool_typ, str_typ, integer_typ};
use rustc_hir::{Ty, TyKind, PrimTy};
use std::sync::Arc;
use rustc_ast::{UintTy, IntTy};

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_ty(
        &mut self,
        ty: &Ty<'tcx>,
    ) -> Result<Typ, VirErr> {
        match &ty.kind {
            TyKind::Slice(ty) => {
                let typ = self.check_ty(ty)?;
                let typs = Arc::new(vec![typ]);
                Ok(Arc::new(TypX::Primitive(Primitive::Slice, typs)))
            }
            TyKind::Array(_ty, _array_len) => {
                /*
                let typ = self.check_ty(ty)?;
                let len = self.check_const(array_len)?;
                let typs = Arc::new(vec![typ, len]);
                Ok(Arc::new(TypX::Primitive(Primitive::Slice, typs)))
                */
                todo!()
            }
            TyKind::Ptr(..) => todo!(),
            TyKind::Ref(..) => todo!(),
            TyKind::BareFn(..) => todo!(),
            TyKind::Never => todo!(),
            TyKind::Tup(types) => {
                let mut typs = vec![];
                for t in types.iter() {
                    typs.push(self.check_ty(t)?);
                }
                Ok(vir::ast_util::mk_tuple_typ(&Arc::new(typs)))
            }
            TyKind::Path(qpath) => {
                match self.check_qpath_for_type(qpath)? {
                    PathResolution::PrimTy(prim_ty)  => Ok(match prim_ty {
                        PrimTy::Int(int_ty) => integer_typ_of_int_ty(int_ty),
                        PrimTy::Uint(uint_ty) => integer_typ_of_uint_ty(uint_ty),
                        PrimTy::Str => str_typ(),
                        PrimTy::Bool => bool_typ(),
                        PrimTy::Char => integer_typ(IntRange::Char),
                        PrimTy::Float(_) => unsupported_err!(ty.span, "floating point types"),
                    }),
                    PathResolution::Datatype(def_id, typs) => {
                        let verus_item = self.bctx.ctxt.verus_items.id_to_name.get(&def_id);
                        if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Int)) = verus_item {
                            Ok(Arc::new(TypX::Int(IntRange::Int)))
                        } else if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Nat)) = verus_item {
                            Ok(Arc::new(TypX::Int(IntRange::Nat)))
                        } else {
                            if verus_item.is_some() { todo!() }
                            let rust_item = crate::verus_items::get_rust_item(self.tcx, def_id);
                            if rust_item.is_some() { todo!() }

                            let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                                &self.bctx.ctxt.verus_items, def_id);
                            let dt = Dt::Path(path);
                            Ok(Arc::new(TypX::Datatype(dt, typs.clone(), Arc::new(vec![]))))
                        }
                    }
                    _ => todo!(),
                }
            }
            TyKind::Infer => {
                Ok(self.new_unknown_typ())
            }
            TyKind::InferDelegation(_, _)
            | TyKind::AnonAdt(..)
            | TyKind::OpaqueDef(..)
            | TyKind::TraitObject(..)
            | TyKind::Typeof(..)
            | TyKind::Err(..)
            | TyKind::Pat(..)
            => {
                unsupported_err!(ty.span, format!("type: {:?}", ty));
            }
        }
    }
}

pub fn integer_typ_of_int_ty(int_ty: IntTy) -> Typ {
    match int_ty {
        IntTy::Isize => integer_typ(IntRange::ISize),
        IntTy::I8 => integer_typ(IntRange::I(8)),
        IntTy::I16 => integer_typ(IntRange::I(16)),
        IntTy::I32 => integer_typ(IntRange::I(32)),
        IntTy::I64 => integer_typ(IntRange::I(64)),
        IntTy::I128 => integer_typ(IntRange::I(128)),
    }
}

pub fn integer_typ_of_uint_ty(uint_ty: UintTy) -> Typ {
    match uint_ty {
        UintTy::Usize => integer_typ(IntRange::USize),
        UintTy::U8 => integer_typ(IntRange::U(8)),
        UintTy::U16 => integer_typ(IntRange::U(16)),
        UintTy::U32 => integer_typ(IntRange::U(32)),
        UintTy::U64 => integer_typ(IntRange::U(64)),
        UintTy::U128 => integer_typ(IntRange::U(128)),
    }
}
