use crate::sst_to_air::typ_to_air;
use air::ast::{CommandX, Commands, DeclX};
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
                                .map(|field| {
                                    Rc::new(field.map_a(|typ: &crate::ast::Typ| typ_to_air(typ)))
                                })
                                .collect::<Vec<_>>(),
                        )
                    }))
                })
                .collect::<Vec<_>>(),
        )
    }))
}

pub fn datatypes_to_air(datatypes: &crate::ast::Datatypes) -> Commands {
    let datatypes = datatypes.iter().map(|datatype| datatype_to_air(datatype)).collect::<Vec<_>>();
    Rc::new(vec![Rc::new(CommandX::Global(Rc::new(DeclX::Datatypes(Rc::new(datatypes)))))])
}
