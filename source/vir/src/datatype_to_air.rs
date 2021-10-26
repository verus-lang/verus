use crate::ast::{DatatypeTransparency, Field, Mode, Param, ParamX, Path, TypX};
use crate::ast_util::is_visible_to_of_owner;
use crate::context::Ctx;
use crate::def::{
    prefix_box, prefix_datatype_inv, prefix_type_id, prefix_unbox, suffix_local_id, Spanned,
};
use crate::func_to_air::{func_bind, func_bind_trig, func_def_args};
use crate::sst_to_air::{path_to_air_ident, typ_invariant, typ_to_air};
use crate::util::vec_map;
use air::ast::{Command, CommandX, Commands, DeclX, Expr, Span};
use air::ast_util::{ident_apply, ident_var, mk_and, mk_bind_expr, mk_implies, str_ident, str_typ};
use std::sync::Arc;

fn datatype_to_air(ctx: &Ctx, datatype: &crate::ast::Datatype) -> air::ast::Datatype {
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
        DatatypeTransparency::WithinModule => {
            is_visible_to_of_owner(&datatype.x.visibility.owning_module, source_module)
        }
        DatatypeTransparency::Always => true,
    }
}

fn field_to_param(span: &Span, f: &Field) -> Param {
    Spanned::new(span.clone(), ParamX { name: f.name.clone(), typ: f.a.0.clone(), mode: f.a.1 })
}

pub fn datatypes_to_air(ctx: &Ctx, datatypes: &crate::ast::Datatypes) -> Commands {
    let source_module = &ctx.module;
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
        // TYPE token
        for datatype in datatypes.iter() {
            let decl_type_id = Arc::new(DeclX::Const(
                prefix_type_id(&path_to_air_ident(&datatype.x.path)),
                str_typ(crate::def::TYPE),
            ));
            commands.push(Arc::new(CommandX::Global(decl_type_id)));
        }
        // box/unbox
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
        // invariant
        for datatype in datatypes.iter() {
            if ctx.datatypes_with_invariant.contains(&datatype.x.path) {
                let mut args = vec_map(&*datatype.x.typ_params, |_| str_typ(crate::def::TYPE));
                args.push(str_typ(&path_to_air_ident(&datatype.x.path)));
                let decl = Arc::new(DeclX::Fun(
                    prefix_datatype_inv(&datatype.x.path),
                    Arc::new(args),
                    air::ast_util::bool_typ(),
                ));
                commands.push(Arc::new(CommandX::Global(decl)));
            }
        }
        // box/unbox axioms
        for datatype in datatypes.iter() {
            let nodes = crate::prelude::datatype_box_axioms(&path_to_air_ident(&datatype.x.path));
            let axioms = air::parser::nodes_to_commands(&nodes)
                .expect("internal error: malformed datatype axioms");
            commands.extend(axioms.iter().cloned());
        }
        // constructor invariant axioms
        for datatype in datatypes.iter() {
            if ctx.datatypes_with_invariant.contains(&datatype.x.path) {
                for variant in datatype.x.variants.iter() {
                    // forall typs, arg1 ... argn. inv1 && ... && invn => inv(typs, ctor(arg1 ... argn))
                    // trigger on inv(ctor(arg1 ... argn), typs)
                    let params = vec_map(&*variant.a, |f| field_to_param(&datatype.span, f));
                    let params = Arc::new(params);
                    let ctor_args = func_def_args(&Arc::new(vec![]), &params);
                    let ctor = ident_apply(&variant.name, &ctor_args);
                    let mut inv_args = func_def_args(&datatype.x.typ_params, &Arc::new(vec![]));
                    inv_args.push(ctor);
                    let inv = ident_apply(&prefix_datatype_inv(&datatype.x.path), &inv_args);
                    let mut pre: Vec<Expr> = Vec::new();
                    for field in variant.a.iter() {
                        let (typ, _) = &field.a;
                        let name = suffix_local_id(&field.name);
                        if let Some(inv) = typ_invariant(ctx, typ, &ident_var(&name)) {
                            pre.push(inv);
                        }
                    }
                    let bind = func_bind(ctx, &datatype.x.typ_params, &params, &inv, false);
                    let imply = mk_implies(&mk_and(&pre), &inv);
                    let forall = mk_bind_expr(&bind, &imply);
                    let axiom = Arc::new(DeclX::Axiom(forall));
                    commands.push(Arc::new(CommandX::Global(axiom)));
                }
            }
        }
        // field invariant axioms
        for datatype in datatypes.iter() {
            if ctx.datatypes_with_invariant.contains(&datatype.x.path) {
                for variant in datatype.x.variants.iter() {
                    for field in variant.a.iter() {
                        let (typ, _) = &field.a;
                        let x = str_ident("x");
                        let x_var = ident_var(&suffix_local_id(&x));
                        let xfield = ident_apply(&field.name, &vec![x_var.clone()]);
                        if let Some(inv_f) = typ_invariant(ctx, typ, &xfield) {
                            // forall typs, x. inv(typs, x) => inv_f(x.f)
                            // trigger on x.f, inv(typs, x)
                            let dtyp =
                                Arc::new(TypX::Datatype(datatype.x.path.clone(), Arc::new(vec![])));
                            let paramx = ParamX { name: x.clone(), typ: dtyp, mode: Mode::Spec };
                            let param = Spanned::new(datatype.span.clone(), paramx);
                            let mut inv_args =
                                func_def_args(&datatype.x.typ_params, &Arc::new(vec![]));
                            inv_args.push(x_var);
                            let inv =
                                ident_apply(&prefix_datatype_inv(&datatype.x.path), &inv_args);
                            let trigs = vec![xfield.clone(), inv.clone()];
                            let bind = func_bind_trig(
                                ctx,
                                &datatype.x.typ_params,
                                &Arc::new(vec![param]),
                                &trigs,
                                false,
                            );
                            let imply = mk_implies(&inv, &inv_f);
                            let forall = mk_bind_expr(&bind, &imply);
                            let axiom = Arc::new(DeclX::Axiom(forall));
                            commands.push(Arc::new(CommandX::Global(axiom)));
                        }
                    }
                }
            }
        }
    }
    Arc::new(commands)
}
