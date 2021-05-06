use crate::def::{prefix_box, prefix_type_id, prefix_unbox};
use crate::sst_to_air::typ_to_air;
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::str_typ;
use std::rc::Rc;

fn datatype_to_air(datatype: &crate::ast::Datatype) -> air::ast::Datatype {
    Rc::new(datatype.x.map_a(|variants| {
        Rc::new(
            variants
                .iter()
                .map(|variant| {
                    Rc::new(variant.map_a(|fields| {
                        Rc::new(
                            fields
                                .iter()
                                .map(|field| Rc::new(field.map_a(|(typ, _)| typ_to_air(typ))))
                                .collect::<Vec<_>>(),
                        )
                    }))
                })
                .collect::<Vec<_>>(),
        )
    }))
}

pub fn datatypes_to_air(datatypes: &crate::ast::Datatypes) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    let air_datatypes =
        datatypes.iter().map(|datatype| datatype_to_air(datatype)).collect::<Vec<_>>();
    commands.push(Rc::new(CommandX::Global(Rc::new(DeclX::Datatypes(Rc::new(air_datatypes))))));
    for datatype in datatypes.iter() {
        let decl_type_id =
            Rc::new(DeclX::Const(prefix_type_id(&datatype.x.name), str_typ(crate::def::TYPE)));
        commands.push(Rc::new(CommandX::Global(decl_type_id)));
    }
    for datatype in datatypes.iter() {
        let decl_box = Rc::new(DeclX::Fun(
            prefix_box(&datatype.x.name),
            Rc::new(vec![str_typ(&datatype.x.name)]),
            str_typ(crate::def::POLY),
        ));
        let decl_unbox = Rc::new(DeclX::Fun(
            prefix_unbox(&datatype.x.name),
            Rc::new(vec![str_typ(crate::def::POLY)]),
            str_typ(&datatype.x.name),
        ));
        commands.push(Rc::new(CommandX::Global(decl_box)));
        commands.push(Rc::new(CommandX::Global(decl_unbox)));
    }
    Rc::new(commands)
}
