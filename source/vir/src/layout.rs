use crate::{
    ast::{Typ, TypDecoration, VirErr},
    ast_visitor::map_typ_visitor,
    messages::{error, Span},
};

pub fn layout_of_typ_supported(typ: &Typ, span: &Span) -> Result<(), VirErr> {
    let _ = map_typ_visitor(typ, &|typ| match &**typ {
        crate::ast::TypX::Bool
        | crate::ast::TypX::Int(_)
        | crate::ast::TypX::Tuple(_)
        | crate::ast::TypX::Datatype(_, _, _)
        | crate::ast::TypX::Decorate(
            TypDecoration::Ref
            | TypDecoration::Rc
            | TypDecoration::Arc
            | TypDecoration::Box
            | TypDecoration::Tracked
            | TypDecoration::Ghost
            | TypDecoration::Never,
            None,
            _,
        )
        | crate::ast::TypX::Boxed(_)
        | crate::ast::TypX::ConstInt(_)
        | crate::ast::TypX::Primitive(_, _) => Ok(typ.clone()),

        crate::ast::TypX::SpecFn(_, _)
        | crate::ast::TypX::AnonymousClosure(_, _, _)
        | crate::ast::TypX::FnDef(..)
        | crate::ast::TypX::Decorate(_, _, _)
        | crate::ast::TypX::TypParam(_)
        | crate::ast::TypX::Projection { .. } => {
            return Err(error(span, "this type is not supported in global size_of / align_of"));
        }

        crate::ast::TypX::Air(_) | crate::ast::TypX::TypeId => {
            unreachable!()
        }
    })?;
    Ok(())
}
