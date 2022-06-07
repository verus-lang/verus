use crate::ast::{
    DatatypeTransparency, Field, GenericBoundX, Ident, Idents, Mode, Path, Typ, TypX, Variants,
};
use crate::ast_util::{is_visible_to_of_owner, path_as_rust_name};
use crate::context::Ctx;
use crate::def::{
    prefix_box, prefix_lambda_type, prefix_tuple_param, prefix_type_id, prefix_unbox,
    suffix_local_stmt_id, variant_field_ident, variant_field_ident_internal, variant_ident,
    Spanned,
};
use crate::func_to_air::{func_bind, func_bind_trig, func_def_args};
use crate::sst::{Par, ParPurpose, ParX};
use crate::sst_to_air::{
    datatype_has_type, datatype_id, expr_has_type, path_to_air_ident, typ_invariant, typ_to_air,
};
use crate::util::vec_map;
use air::ast::{Command, CommandX, Commands, DeclX, Expr, ExprX, Span};
use air::ast_util::{
    ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies, str_apply,
    str_ident, str_typ,
};
use std::sync::Arc;

fn datatype_to_air(ctx: &Ctx, datatype: &crate::ast::Datatype) -> air::ast::Datatype {
    let mut variants: Vec<air::ast::Variant> = Vec::new();
    for variant in datatype.x.variants.iter() {
        let mut fields: Vec<air::ast::Field> = Vec::new();
        for field in variant.a.iter() {
            let id =
                variant_field_ident_internal(&datatype.x.path, &variant.name, &field.name, true);
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

fn field_to_par(span: &Span, f: &Field) -> Par {
    Spanned::new(
        span.clone(),
        ParX {
            name: f.name.clone(),
            typ: f.a.0.clone(),
            mode: f.a.1,
            purpose: ParPurpose::Regular,
        },
    )
}

fn datatype_or_fun_to_air_commands(
    ctx: &Ctx,
    field_commands: &mut Vec<Command>,
    token_commands: &mut Vec<Command>,
    box_commands: &mut Vec<Command>,
    axiom_commands: &mut Vec<Command>,
    span: &Span,
    dpath: &Path,
    dtyp: &air::ast::Typ,
    dtyp_id: Option<Expr>,
    datatyp: Option<Typ>,
    tparams: &Idents,
    variants: &Variants,
    is_fun: bool,
    declare_box: bool,
    add_height: bool,
) {
    let x = str_ident("x");
    let x_var = ident_var(&suffix_local_stmt_id(&x));
    let apolytyp = str_typ(crate::def::POLY);

    if dtyp_id.is_none() {
        // datatype TYPE tokens
        let decl_type_id = Arc::new(DeclX::fun_or_const(
            prefix_type_id(dpath),
            Arc::new(vec_map(&*tparams, |_| str_typ(crate::def::TYPE))),
            str_typ(crate::def::TYPE),
        ));
        token_commands.push(Arc::new(CommandX::Global(decl_type_id)));
    }

    if declare_box {
        // box
        let decl_box = Arc::new(DeclX::Fun(
            prefix_box(&dpath),
            Arc::new(vec![dtyp.clone()]),
            apolytyp.clone(),
        ));
        box_commands.push(Arc::new(CommandX::Global(decl_box)));

        // unbox
        let decl_unbox = Arc::new(DeclX::Fun(
            prefix_unbox(&dpath),
            Arc::new(vec![apolytyp.clone()]),
            dtyp.clone(),
        ));
        box_commands.push(Arc::new(CommandX::Global(decl_unbox)));
    }

    // datatype axioms
    let x_param = |typ: &Typ| {
        Spanned::new(
            span.clone(),
            ParX {
                name: x.clone(),
                typ: typ.clone(),
                mode: Mode::Exec,
                purpose: ParPurpose::Regular,
            },
        )
    };
    let x_params = |typ: &Typ| Arc::new(vec![x_param(typ)]);
    let typ_args = Arc::new(vec_map(&tparams, |t| Arc::new(TypX::TypParam(t.clone()))));
    let datatyp = if let Some(datatyp) = &datatyp {
        datatyp.clone()
    } else {
        Arc::new(TypX::Datatype(dpath.clone(), typ_args.clone()))
    };
    let box_x = ident_apply(&prefix_box(&dpath), &vec![x_var.clone()]);
    let unbox_x = ident_apply(&prefix_unbox(&dpath), &vec![x_var.clone()]);
    let box_unbox_x = ident_apply(&prefix_box(&dpath), &vec![unbox_x.clone()]);
    let unbox_box_x = ident_apply(&prefix_unbox(&dpath), &vec![box_x.clone()]);
    let id = if let Some(dtyp_id) = dtyp_id { dtyp_id } else { datatype_id(dpath, &typ_args) };
    let has = expr_has_type(&id, &x_var);
    let has_box = expr_has_type(&id, &box_x);
    let vpolytyp = Arc::new(TypX::Boxed(datatyp.clone()));

    if declare_box {
        // box axiom:
        //   forall x. x == unbox(box(x))
        // trigger on box(x)
        let name = format!("{}_box_axiom", path_as_rust_name(dpath));
        let bind = func_bind(ctx, name, &Arc::new(vec![]), &x_params(&datatyp), &box_x, false);
        let forall = mk_bind_expr(&bind, &mk_eq(&x_var, &unbox_box_x));
        axiom_commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));

        // unbox axiom:
        //   forall typs, x. has_type(x, T(typs)) => x == box(unbox(x))
        // trigger on has_type(x, T(typs))
        let name = format!("{}_unbox_axiom", path_as_rust_name(dpath));
        let bind = func_bind(ctx, name, tparams, &x_params(&vpolytyp), &has, false);
        let forall = mk_bind_expr(&bind, &mk_implies(&has, &mk_eq(&x_var, &box_unbox_x)));
        axiom_commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));
    }

    // function axiom
    if is_fun {
        let mut params: Vec<Par> = Vec::new();
        let mut args: Vec<Expr> = Vec::new();
        let mut pre: Vec<Expr> = Vec::new();
        for i in 0..tparams.len() - 1 {
            let name = prefix_tuple_param(i);
            let arg = ident_var(&suffix_local_stmt_id(&name));
            if let Some(inv) = typ_invariant(ctx, &typ_args[i], &arg) {
                pre.push(inv);
            }
            args.push(arg);
            let parx = ParX {
                name,
                typ: vpolytyp.clone(),
                mode: Mode::Exec,
                purpose: ParPurpose::Regular,
            };
            params.push(Spanned::new(span.clone(), parx));
        }
        let tparamret = typ_args.last().expect("return type").clone();
        let app = Arc::new(ExprX::ApplyLambda(apolytyp.clone(), x_var.clone(), Arc::new(args)));
        let has_app = typ_invariant(ctx, &tparamret, &app).expect("return invariant");

        // Lambda constructor axiom:
        // forall typ1 ... typn, tret, x: Fun.
        //   (forall arg1: Poly ... argn: Poly.
        //     has_type1 && ... && has_typen ==> has_type(apply(x, args), tret)) ==>
        //   has_type(box(mk_fun(x)), FUN(typ1...typn, tret))
        // trigger on has_type(box(mk_fun(x)), FUN(typ1...typn, tret))
        let inner_trigs = vec![has_app.clone()];
        let name = format!("{}_constructor_inner", path_as_rust_name(dpath));
        let inner_bind = func_bind_trig(
            ctx,
            name,
            &Arc::new(vec![]),
            &Arc::new(params.clone()),
            &inner_trigs,
            false,
        );
        let inner_imply = mk_implies(&mk_and(&pre), &has_app);
        let inner_forall = mk_bind_expr(&inner_bind, &inner_imply);
        let mk_fun = str_apply(crate::def::MK_FUN, &vec![x_var.clone()]);
        let box_mk_fun = ident_apply(&prefix_box(&dpath), &vec![mk_fun]);
        let has_box_mk_fun = expr_has_type(&id, &box_mk_fun);
        let trigs = vec![has_box_mk_fun.clone()];
        let name = format!("{}_constructor", path_as_rust_name(dpath));
        let bind =
            func_bind_trig(ctx, name, tparams, &Arc::new(vec![x_param(&datatyp)]), &trigs, false);
        let imply = mk_implies(&inner_forall, &has_box_mk_fun);
        let forall = mk_bind_expr(&bind, &imply);
        let axiom = Arc::new(DeclX::Axiom(forall));
        axiom_commands.push(Arc::new(CommandX::Global(axiom)));

        // Lambda apply axiom:
        // forall typ1 ... typn, tret, arg1: Poly ... argn: Poly, x: Fun.
        //   has_type_f && has_type1 && ... && has_typen => has_type(apply(x, args), tret)
        // trigger on apply(x, args), has_type_f
        params.push(x_param(&datatyp));
        pre.insert(0, has_box.clone());
        let trigs = vec![app, has_box.clone()];
        let name = format!("{}_apply", path_as_rust_name(dpath));
        let bind = func_bind_trig(ctx, name, tparams, &Arc::new(params), &trigs, false);
        let imply = mk_implies(&mk_and(&pre), &has_app);
        let forall = mk_bind_expr(&bind, &imply);
        let axiom = Arc::new(DeclX::Axiom(forall));
        axiom_commands.push(Arc::new(CommandX::Global(axiom)));
    }

    // constructor and field axioms
    for variant in variants.iter() {
        if ctx.datatypes_with_invariant.contains(dpath) {
            // constructor invariant axiom:
            //   forall typs, arg1 ... argn.
            //     inv1 && ... && invn => has_type(box(ctor(arg1 ... argn)), T(typs))
            // trigger on has_type(box(ctor(arg1 ... argn)), T(typs))
            let params = vec_map(&*variant.a, |f| field_to_par(span, f));
            let params = Arc::new(params);
            let ctor_args = func_def_args(&Arc::new(vec![]), &params);
            let ctor = ident_apply(&variant_ident(&dpath, &variant.name), &ctor_args);
            let box_ctor = ident_apply(&prefix_box(&dpath), &vec![ctor]);
            let has_ctor = datatype_has_type(dpath, &typ_args, &box_ctor);
            let mut pre: Vec<Expr> = Vec::new();
            for field in variant.a.iter() {
                let (typ, _, _) = &field.a;
                let name = suffix_local_stmt_id(&field.name);
                if let Some(inv) = typ_invariant(ctx, typ, &ident_var(&name)) {
                    pre.push(inv);
                }
            }
            let name = format!("{}_constructor", &variant_ident(&dpath, &variant.name));
            let bind = func_bind(ctx, name, tparams, &params, &has_ctor, false);
            let imply = mk_implies(&mk_and(&pre), &has_ctor);
            let forall = mk_bind_expr(&bind, &imply);
            let axiom = Arc::new(DeclX::Axiom(forall));
            axiom_commands.push(Arc::new(CommandX::Global(axiom)));
        }
        for field in variant.a.iter() {
            let id = variant_field_ident(&dpath, &variant.name, &field.name);
            let internal_id =
                variant_field_ident_internal(&dpath, &variant.name, &field.name, true);
            let (typ, _, _) = &field.a;
            let xfield = ident_apply(&id, &vec![x_var.clone()]);
            let xfield_internal = ident_apply(&internal_id, &vec![x_var.clone()]);
            let xfield_unbox = ident_apply(&id, &vec![unbox_x.clone()]);

            // Create a wrapper function to access the field,
            // because it seems to be dangerous to trigger directly on e.f,
            // because Z3 seems to introduce e.f internally,
            // which can unexpectedly trigger matching loops creating e.f.f.f.f...
            //   function f(x:datatyp):typ
            //   axiom forall x. f(x) = x.f
            let decl_field = Arc::new(DeclX::Fun(
                id.clone(),
                Arc::new(vec![dtyp.clone()]),
                typ_to_air(ctx, typ),
            ));
            field_commands.push(Arc::new(CommandX::Global(decl_field)));
            let trigs = vec![xfield.clone()];
            let name = format!("{}_accessor", id);
            let bind =
                func_bind_trig(ctx, name, &Arc::new(vec![]), &x_params(&datatyp), &trigs, false);
            let eq = mk_eq(&xfield, &xfield_internal);
            let forall = mk_bind_expr(&bind, &eq);
            let axiom = Arc::new(DeclX::Axiom(forall));
            axiom_commands.push(Arc::new(CommandX::Global(axiom)));

            if ctx.datatypes_with_invariant.contains(dpath) {
                if let Some(inv_f) = typ_invariant(ctx, typ, &xfield_unbox) {
                    // field invariant axiom:
                    //   forall typs, x. has_type(x, T(typs)) => inv_f(unbox(x).f)
                    // trigger on unbox(x).f, has_type(x, T(typs))
                    let trigs = vec![xfield_unbox.clone(), has.clone()];
                    let name = format!("{}_invariant", id);
                    let bind =
                        func_bind_trig(ctx, name, tparams, &x_params(&vpolytyp), &trigs, false);
                    let imply = mk_implies(&has, &inv_f);
                    let forall = mk_bind_expr(&bind, &imply);
                    let axiom = Arc::new(DeclX::Axiom(forall));
                    axiom_commands.push(Arc::new(CommandX::Global(axiom)));
                }
            }
        }
    }

    if !ctx.datatypes_with_invariant.contains(dpath) && declare_box && !is_fun {
        // If there are no visible refinement types (e.g. no refinement type fields,
        // or type is completely abstract to us), then has_type always holds:
        //   forall typs, x. has_type(box(x), T(typs))
        // trigger on has_type(box(x), T(typs))
        let name = format!("{}_has_type_always", path_as_rust_name(dpath));
        let bind = func_bind(ctx, name, tparams, &x_params(&datatyp), &has_box, false);
        let forall = mk_bind_expr(&bind, &has_box);
        axiom_commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(forall)))));
    }

    // height axiom
    // (make sure that this stays in sync with recursive_types::check_well_founded)
    if add_height {
        for variant in variants.iter() {
            for field in variant.a.iter() {
                let typ = &field.a.0;
                match &**typ {
                    TypX::Datatype(path, _) if ctx.datatype_is_transparent[path] => {
                        let node = crate::prelude::datatype_height_axiom(
                            &dpath,
                            &path,
                            &variant_field_ident(&dpath, &variant.name, &field.name),
                        );
                        let axiom = air::parser::Parser::new()
                            .node_to_command(&node)
                            .expect("internal error: malformed datatype axiom");
                        axiom_commands.push(axiom);
                    }
                    _ => {}
                }
            }
        }
    }
}

pub fn datatypes_to_air(ctx: &Ctx, datatypes: &crate::ast::Datatypes) -> Commands {
    let source_module = &ctx.module;
    let mut transparent_air_datatypes: Vec<air::ast::Datatype> = Vec::new();
    let mut opaque_sort_commands: Vec<Command> = Vec::new();
    let mut token_commands: Vec<Command> = Vec::new();
    let mut box_commands: Vec<Command> = Vec::new();
    let mut field_commands: Vec<Command> = Vec::new();
    let mut axiom_commands: Vec<Command> = Vec::new();

    for lambda_n_params in &ctx.lambda_types {
        let tparams: Vec<Ident> =
            (0..*lambda_n_params + 1).into_iter().map(prefix_tuple_param).collect();
        datatype_or_fun_to_air_commands(
            ctx,
            &mut field_commands,
            &mut token_commands,
            &mut box_commands,
            &mut axiom_commands,
            &ctx.global.no_span,
            &prefix_lambda_type(*lambda_n_params),
            &Arc::new(air::ast::TypX::Lambda),
            None,
            Some(Arc::new(TypX::Lambda(Arc::new(vec![]), Arc::new(TypX::Bool)))),
            &Arc::new(tparams),
            &Arc::new(vec![]),
            true,
            true,
            false,
        );
    }

    for monotyp in &ctx.mono_abstract_datatypes {
        // Encode concrete instantiations of abstract types as AIR sorts
        let dpath = crate::sst_to_air::monotyp_to_path(monotyp);
        let sort = Arc::new(air::ast::DeclX::Sort(path_to_air_ident(&dpath)));
        opaque_sort_commands.push(Arc::new(CommandX::Global(sort)));

        datatype_or_fun_to_air_commands(
            ctx,
            &mut field_commands,
            &mut token_commands,
            &mut box_commands,
            &mut axiom_commands,
            &ctx.global.no_span,
            &dpath,
            &str_typ(&path_to_air_ident(&dpath)),
            Some(crate::sst_to_air::monotyp_to_id(monotyp)),
            Some(crate::poly::monotyp_to_typ(monotyp)),
            &Arc::new(vec![]),
            &Arc::new(vec![]),
            false,
            true,
            false,
        );
    }

    for datatype in datatypes.iter() {
        let dpath = &datatype.x.path;
        let is_transparent = is_datatype_transparent(source_module, datatype);

        if is_transparent {
            // Encode transparent types as AIR datatypes
            transparent_air_datatypes.push(datatype_to_air(ctx, datatype));
        }

        let mut tparams: Vec<Ident> = Vec::new();
        for (name, bound, _strict_pos) in datatype.x.typ_params.iter() {
            match &**bound {
                GenericBoundX::Traits(ts) if ts.len() == 0 => {}
                _ => panic!("datatype type parameter bounds"),
            }
            tparams.push(name.clone());
        }

        datatype_or_fun_to_air_commands(
            ctx,
            &mut field_commands,
            &mut token_commands,
            &mut box_commands,
            &mut axiom_commands,
            &datatype.span,
            dpath,
            &str_typ(&path_to_air_ident(dpath)),
            None,
            None,
            &Arc::new(tparams),
            &datatype.x.variants,
            false,
            is_transparent,
            is_transparent,
        );
    }
    let mut commands: Vec<Command> = Vec::new();
    commands.append(&mut opaque_sort_commands);
    commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Datatypes(Arc::new(
        transparent_air_datatypes,
    ))))));
    commands.append(&mut field_commands);
    commands.append(&mut token_commands);
    commands.append(&mut box_commands);
    commands.append(&mut axiom_commands);
    Arc::new(commands)
}
