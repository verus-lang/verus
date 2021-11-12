use crate::ast::{DatatypeTransparency, Field, Mode, Param, ParamX, Path, Typ, TypX};
use crate::ast_util::is_visible_to_of_owner;
use crate::context::Ctx;
use crate::def::{
    prefix_box, prefix_type_id, prefix_unbox, suffix_local_stmt_id, variant_field_ident,
    variant_ident, Spanned,
};
use crate::func_to_air::{func_bind, func_bind_trig, func_def_args};
use crate::sst_to_air::{datatype_has_type, path_to_air_ident, typ_invariant, typ_to_air};
use crate::util::vec_map;
use air::ast::{Command, CommandX, Commands, DeclX, Expr, Span};
use air::ast_util::{
    ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies, str_ident,
    str_typ,
};
use std::sync::Arc;

fn datatype_to_air(ctx: &Ctx, datatype: &crate::ast::Datatype) -> air::ast::Datatype {
    let mut variants: Vec<air::ast::Variant> = Vec::new();
    for variant in datatype.x.variants.iter() {
        let mut fields: Vec<air::ast::Field> = Vec::new();
        for field in variant.a.iter() {
            let id = variant_field_ident(&datatype.x.path, &variant.name, &field.name);
            fields.push(ident_binder(&id, &typ_to_air(ctx, &field.a.0)));
        }
        let id = variant_ident(&datatype.x.path, &variant.name);
        variants.push(ident_binder(&id, &Arc::new(fields)));
    }
    Arc::new(air::ast::BinderX { name: path_to_air_ident(&datatype.x.path), a: Arc::new(variants) })
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

    for datatype in datatypes.iter() {
        // TYPE token
        let decl_type_id = Arc::new(DeclX::fun_or_const(
            prefix_type_id(&datatype.x.path),
            Arc::new(vec_map(&*datatype.x.typ_params, |_| str_typ(crate::def::TYPE))),
            str_typ(crate::def::TYPE),
        ));
        commands.push(Arc::new(CommandX::Global(decl_type_id)));
    }

    for datatype in datatypes.iter() {
        let x = str_ident("x");
        let x_var = ident_var(&suffix_local_stmt_id(&x));
        let x_param = |typ: &Typ| {
            Spanned::new(
                datatype.span.clone(),
                ParamX { name: x.clone(), typ: typ.clone(), mode: Mode::Exec },
            )
        };
        let x_params = |typ: &Typ| Arc::new(vec![x_param(typ)]);
        let dtyp = str_typ(&path_to_air_ident(&datatype.x.path));
        let tparams = &datatype.x.typ_params;
        let typ_args = Arc::new(vec_map(&tparams, |t| Arc::new(TypX::TypParam(t.clone()))));
        let dpath = &datatype.x.path;
        let datatyp = Arc::new(TypX::Datatype(dpath.clone(), typ_args.clone()));
        let box_x = ident_apply(&prefix_box(&dpath), &vec![x_var.clone()]);
        let unbox_x = ident_apply(&prefix_unbox(&dpath), &vec![x_var.clone()]);
        let box_unbox_x = ident_apply(&prefix_box(&dpath), &vec![unbox_x.clone()]);
        let unbox_box_x = ident_apply(&prefix_unbox(&dpath), &vec![box_x.clone()]);
        let has = datatype_has_type(dpath, &typ_args, &x_var);
        let has_box = datatype_has_type(dpath, &typ_args, &box_x);
        let apolytyp = str_typ(crate::def::POLY);
        let vpolytyp = Arc::new(TypX::Boxed(datatyp.clone()));

        // box
        let decl_box = Arc::new(DeclX::Fun(
            prefix_box(&dpath),
            Arc::new(vec![dtyp.clone()]),
            apolytyp.clone(),
        ));
        commands.push(Arc::new(CommandX::Global(decl_box)));

        // unbox
        let decl_unbox = Arc::new(DeclX::Fun(
            prefix_unbox(&dpath),
            Arc::new(vec![apolytyp.clone()]),
            dtyp.clone(),
        ));
        commands.push(Arc::new(CommandX::Global(decl_unbox)));

        // box axiom:
        //   forall x. x == unbox(box(x))
        // trigger on box(x)
        let bind = func_bind(ctx, &Arc::new(vec![]), &x_params(&datatyp), &box_x, false);
        let forall = mk_bind_expr(&bind, &mk_eq(&x_var, &unbox_box_x));
        commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));

        // unbox axiom:
        //   forall typs, x. has_type(x, T(typs)) => x == box(unbox(x))
        // trigger on has_type(x, T(typs))
        let bind = func_bind(ctx, tparams, &x_params(&vpolytyp), &has, false);
        let forall = mk_bind_expr(&bind, &mk_implies(&has, &mk_eq(&x_var, &box_unbox_x)));
        commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));

        // constructor and field axioms
        if ctx.datatypes_with_invariant.contains(dpath) {
            for variant in datatype.x.variants.iter() {
                // constructor invariant axiom:
                //   forall typs, arg1 ... argn.
                //     inv1 && ... && invn => has_type(box(ctor(arg1 ... argn)), T(typs))
                // trigger on has_type(box(ctor(arg1 ... argn)), T(typs))
                let params = vec_map(&*variant.a, |f| field_to_param(&datatype.span, f));
                let params = Arc::new(params);
                let ctor_args = func_def_args(&Arc::new(vec![]), &params);
                let ctor = ident_apply(&variant_ident(&dpath, &variant.name), &ctor_args);
                let box_ctor = ident_apply(&prefix_box(&dpath), &vec![ctor]);
                let has_ctor = datatype_has_type(dpath, &typ_args, &box_ctor);
                let mut pre: Vec<Expr> = Vec::new();
                for field in variant.a.iter() {
                    let (typ, _) = &field.a;
                    let name = suffix_local_stmt_id(&field.name);
                    if let Some(inv) = typ_invariant(ctx, typ, &ident_var(&name)) {
                        pre.push(inv);
                    }
                }
                let bind = func_bind(ctx, tparams, &params, &has_ctor, false);
                let imply = mk_implies(&mk_and(&pre), &has_ctor);
                let forall = mk_bind_expr(&bind, &imply);
                let axiom = Arc::new(DeclX::Axiom(forall));
                commands.push(Arc::new(CommandX::Global(axiom)));
            }
            for variant in datatype.x.variants.iter() {
                for field in variant.a.iter() {
                    let (typ, _) = &field.a;
                    let xfield = ident_apply(
                        &variant_field_ident(&dpath, &variant.name, &field.name),
                        &vec![unbox_x.clone()],
                    );
                    if let Some(inv_f) = typ_invariant(ctx, typ, &xfield) {
                        // field invariant axiom:
                        //   forall typs, x. has_type(x, T(typs)) => inv_f(unbox(x).f)
                        // trigger on unbox(x).f, has_type(x, T(typs))
                        let trigs = vec![xfield.clone(), has.clone()];
                        let bind =
                            func_bind_trig(ctx, tparams, &x_params(&vpolytyp), &trigs, false);
                        let imply = mk_implies(&has, &inv_f);
                        let forall = mk_bind_expr(&bind, &imply);
                        let axiom = Arc::new(DeclX::Axiom(forall));
                        commands.push(Arc::new(CommandX::Global(axiom)));
                    }
                }
            }
        } else {
            // If there are no visible refinement types (e.g. no refinement type fields,
            // or type is completely abstract to us), then has_type always holds:
            //   forall typs, x. has_type(box(x), T(typs))
            // trigger on has_type(box(x), T(typs))
            let bind = func_bind(ctx, tparams, &x_params(&datatyp), &has_box, false);
            let forall = mk_bind_expr(&bind, &has_box);
            commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));
        }

        // height axiom
        if is_datatype_transparent(source_module, datatype) {
            for variant in datatype.x.variants.iter() {
                for field in variant.a.iter() {
                    let typ = &field.a.0;
                    match &**typ {
                        TypX::Datatype(path, _) => {
                            let node = crate::prelude::datatype_height_axiom(
                                &dpath,
                                &path,
                                &variant_field_ident(&dpath, &variant.name, &field.name),
                            );
                            let axiom = air::parser::node_to_command(&node)
                                .expect("internal error: malformed datatype axiom");
                            commands.push(axiom);
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    Arc::new(commands)
}
