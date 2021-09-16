use crate::ast::{DatatypeTransparency, Path};
use crate::context::Ctx;
use crate::def::{prefix_box, prefix_type_id, prefix_unbox};
use crate::sst_to_air::{path_to_air_ident, typ_to_air};
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::str_typ;
use std::sync::Arc;

fn datatype_to_air<'a>(ctx: &'a Ctx, datatype: &crate::ast::Datatype) -> air::ast::Datatype {
    Arc::new(air::ast::BinderX {
        name: path_to_air_ident(&datatype.x.path),
        a: Arc::new(
            datatype
                .x
                .variants
                .iter()
                .map(|variant| {
                    Arc::new(variant.map_a(|fields| {
                        Arc::new(
                            fields
                                .iter()
                                .map(|field| Arc::new(field.map_a(|(typ, _)| typ_to_air(ctx, typ))))
                                .collect::<Vec<_>>(),
                        )
                    }))
                })
                .collect::<Vec<_>>(),
        ),
    })
}

pub fn is_datatype_transparent(source_module: &Path, datatype: &crate::ast::Datatype) -> bool {
    match datatype.x.transparency {
        DatatypeTransparency::Never => false,
        DatatypeTransparency::WithinModule => match &datatype.x.visibility.owning_module {
            None => true,
            Some(target) if target.len() > source_module.len() => false,
            // Child can access private item in parent, so check if target is parent:
            Some(target) => target[..] == source_module[..target.len()],
        },
        DatatypeTransparency::Always => true,
    }
}

pub fn datatypes_to_air<'a>(
    ctx: &'a Ctx,
    source_module: &Path,
    datatypes: &crate::ast::Datatypes,
) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    let (transparent, opaque): (Vec<_>, Vec<_>) =
        datatypes.iter().partition(|datatype| is_datatype_transparent(source_module, *datatype));
    // Encode transparent types as air datatypes
    let transparent_air_datatypes: Vec<_> =
        transparent.iter().map(|datatype| datatype_to_air(ctx, datatype)).collect();
    commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Datatypes(Arc::new(
        transparent_air_datatypes,
    ))))));
    // Encode opaque types as air sorts
    for datatype in opaque.iter() {
        let decl_opaq_sort = Arc::new(air::ast::DeclX::Sort(path_to_air_ident(&datatype.x.path)));
        commands.push(Arc::new(CommandX::Global(decl_opaq_sort)));
    }
    for datatypes in &[transparent, opaque] {
        for datatype in datatypes.iter() {
            let decl_type_id = Arc::new(DeclX::Const(
                prefix_type_id(&path_to_air_ident(&datatype.x.path)),
                str_typ(crate::def::TYPE),
            ));
            commands.push(Arc::new(CommandX::Global(decl_type_id)));
        }
        for datatype in datatypes.iter() {
            let decl_box = Arc::new(DeclX::Fun(
                prefix_box(&path_to_air_ident(&datatype.x.path)),
                Arc::new(vec![str_typ(&path_to_air_ident(&datatype.x.path))]),
                str_typ(crate::def::POLY),
            ));
            let decl_unbox = Arc::new(DeclX::Fun(
                prefix_unbox(&path_to_air_ident(&datatype.x.path)),
                Arc::new(vec![str_typ(crate::def::POLY)]),
                str_typ(&path_to_air_ident(&datatype.x.path)),
            ));
            commands.push(Arc::new(CommandX::Global(decl_box)));
            commands.push(Arc::new(CommandX::Global(decl_unbox)));
        }
        for datatype in datatypes.iter() {
            let nodes = crate::prelude::datatype_box_axioms(&path_to_air_ident(&datatype.x.path));
            let axioms = air::parser::nodes_to_commands(&nodes)
                .expect("internal error: malformed datatype axioms");
            commands.extend(axioms.iter().cloned());
        }
    }
    Arc::new(commands)
}
