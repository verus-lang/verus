use crate::ast::{
    DatatypeTransparency, Field, Ident, Idents, Mode, Path, Typ, TypX, VarIdent, Variants,
};
use crate::ast_util::{
    air_unique_var, is_visible_to_of_owner, path_as_friendly_rust_name, LowerUniqueVar,
};
use crate::context::Ctx;
use crate::def::{
    is_variant_ident, prefix_box, prefix_spec_fn_type, prefix_tuple_param, prefix_type_id,
    prefix_unbox, variant_field_ident, variant_field_ident_internal, variant_ident, Spanned,
    QID_ACCESSOR, QID_APPLY, QID_BOX_AXIOM, QID_CONSTRUCTOR, QID_CONSTRUCTOR_INNER,
    QID_HAS_TYPE_ALWAYS, QID_INVARIANT, QID_UNBOX_AXIOM,
};
use crate::messages::Span;
use crate::sst::{Par, ParPurpose, ParX};
use crate::sst_to_air::{
    datatype_id, expr_has_type, monotyp_to_path, path_to_air_ident, typ_invariant, typ_to_air,
};
use crate::sst_to_air_func::{func_bind, func_bind_trig, func_def_args};
use crate::util::vec_map;
use air::ast::{Command, CommandX, Commands, DeclX, Expr, ExprX};
use air::ast_util::{
    ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies,
    mk_unnamed_axiom, str_apply, str_ident, str_typ,
};
use std::sync::Arc;

fn datatype_to_air(ctx: &Ctx, datatype: &crate::ast::Datatype) -> air::ast::Datatype {
    let mut variants: Vec<air::ast::Variant> = Vec::new();
    for variant in datatype.x.variants.iter() {
        let mut fields: Vec<air::ast::Field> = Vec::new();
        for field in variant.fields.iter() {
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
    match &datatype.x.transparency {
        DatatypeTransparency::Never => false,
        DatatypeTransparency::WhenVisible(vis) => {
            is_visible_to_of_owner(&vis.restricted_to, source_module)
        }
    }
}

fn field_to_par(span: &Span, f: &Field) -> Par {
    let dis = crate::ast::VarIdentDisambiguate::Field;
    Spanned::new(
        span.clone(),
        ParX {
            name: crate::ast_util::str_unique_var(&("_".to_string() + &f.name), dis),
            typ: f.a.0.clone(),
            mode: f.a.1,
            is_mut: false,
            purpose: ParPurpose::Regular,
        },
    )
}

fn uses_ext_equal(ctx: &Ctx, typ: &Typ) -> bool {
    match &**typ {
        TypX::Int(_) => false,
        TypX::Bool => false,
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::SpecFn(_, _) => true,
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::Datatype(path, _, _) => ctx.datatype_map[path].x.ext_equal,
        TypX::Decorate(_, _, t) => uses_ext_equal(ctx, t),
        TypX::Boxed(typ) => uses_ext_equal(ctx, typ),
        TypX::TypParam(_) => true,
        TypX::Projection { .. } => true,
        TypX::TypeId => panic!("internal error: uses_ext_equal of TypeId"),
        TypX::ConstInt(_) => false,
        TypX::Air(_) => panic!("internal error: uses_ext_equal of Air"),
        TypX::Primitive(crate::ast::Primitive::Array, _) => true,
        TypX::Primitive(crate::ast::Primitive::Slice, _) => true,
        TypX::Primitive(crate::ast::Primitive::StrSlice, _) => false,
        TypX::Primitive(crate::ast::Primitive::Ptr, _) => false,
        TypX::Primitive(crate::ast::Primitive::Global, _) => false,
        TypX::FnDef(..) => false,
    }
}

enum DTypId {
    Expr(Expr),
    Primitive(crate::ast::Primitive),
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
    dtyp_id: Option<DTypId>,
    datatyp: Option<Typ>,
    tparams: &Idents,
    variants: &Variants,
    is_fun: bool,
    is_array: bool,
    declare_box: bool,
    add_height: bool,
    add_ext_equal: bool,
) {
    use crate::def::QID_EXT_EQUAL;
    let x = air_unique_var("x");
    let x_var = ident_var(&x.lower());
    let apolytyp = str_typ(crate::def::POLY);

    if dtyp_id.is_none() {
        // datatype TYPE identifiers
        let mut args: Vec<air::ast::Typ> = Vec::new();
        for _ in tparams.iter() {
            args.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }
        let decl_type_id = Arc::new(DeclX::fun_or_const(
            prefix_type_id(dpath),
            Arc::new(args),
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
    let var_param = |x: VarIdent, typ: &Typ| {
        Spanned::new(
            span.clone(),
            ParX {
                name: x.clone(),
                typ: typ.clone(),
                mode: Mode::Exec,
                is_mut: false,
                purpose: ParPurpose::Regular,
            },
        )
    };
    let x_param = |typ: &Typ| var_param(x.clone(), typ);
    let x_params = |typ: &Typ| Arc::new(vec![x_param(typ)]);
    let typ_args = Arc::new(vec_map(&tparams, |t| Arc::new(TypX::TypParam(t.clone()))));
    let datatyp = if let Some(datatyp) = &datatyp {
        datatyp.clone()
    } else {
        Arc::new(TypX::Datatype(dpath.clone(), typ_args.clone(), Arc::new(vec![])))
    };
    let box_x = ident_apply(&prefix_box(&dpath), &vec![x_var.clone()]);
    let unbox_x = ident_apply(&prefix_unbox(&dpath), &vec![x_var.clone()]);
    let box_unbox_x = ident_apply(&prefix_box(&dpath), &vec![unbox_x.clone()]);
    let unbox_box_x = ident_apply(&prefix_unbox(&dpath), &vec![box_x.clone()]);
    let id = match dtyp_id {
        Some(DTypId::Expr(e)) => e,
        Some(DTypId::Primitive(p)) => crate::sst_to_air::primitive_id(&p, &typ_args),
        None => datatype_id(dpath, &typ_args),
    };
    let has = expr_has_type(&x_var, &id);
    let has_box = expr_has_type(&box_x, &id);
    let vpolytyp = Arc::new(TypX::Boxed(datatyp.clone()));

    if declare_box {
        // box axiom:
        //   forall x. x == unbox(box(x))
        // trigger on box(x)
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_BOX_AXIOM);
        let bind = func_bind(ctx, name, &Arc::new(vec![]), &x_params(&datatyp), &box_x, false);
        let forall = mk_bind_expr(&bind, &mk_eq(&x_var, &unbox_box_x));
        axiom_commands.push(Arc::new(CommandX::Global(mk_unnamed_axiom(forall))));

        // unbox axiom:
        //   forall typs, x. has_type(x, T(typs)) => x == box(unbox(x))
        // trigger on has_type(x, T(typs))
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_UNBOX_AXIOM);
        let bind = func_bind(ctx, name, tparams, &x_params(&vpolytyp), &has, false);
        let forall = mk_bind_expr(&bind, &mk_implies(&has, &mk_eq(&x_var, &box_unbox_x)));
        axiom_commands.push(Arc::new(CommandX::Global(mk_unnamed_axiom(forall))));
    }

    // function axiom
    let mut fun_args: Option<Arc<Vec<Expr>>> = None;
    let mut fun_params: Option<Vec<Par>> = None;
    let mut fun_has: Option<Expr> = None;
    if is_fun {
        let mut params: Vec<Par> = Vec::new();
        let mut args: Vec<Expr> = Vec::new();
        let mut pre: Vec<Expr> = Vec::new();
        for i in 0..tparams.len() - 1 {
            let name = crate::ast_util::typ_unique_var(prefix_tuple_param(i));
            let arg = ident_var(&name.lower());
            if let Some(inv) = typ_invariant(ctx, &typ_args[i], &arg) {
                pre.push(inv);
            }
            args.push(arg);
            let parx = ParX {
                name,
                typ: vpolytyp.clone(),
                mode: Mode::Exec,
                is_mut: false,
                purpose: ParPurpose::Regular,
            };
            params.push(Spanned::new(span.clone(), parx));
        }
        let args = Arc::new(args);
        fun_args = Some(args.clone());
        fun_params = Some(params.clone());
        let tparamret = typ_args.last().expect("return type").clone();
        let app = Arc::new(ExprX::ApplyFun(apolytyp.clone(), x_var.clone(), args));
        let has_app = typ_invariant(ctx, &tparamret, &app).expect("return invariant");

        // SpecFn constructor axiom:
        // forall typ1 ... typn, tret, x: Fun.
        //   (forall arg1: Poly ... argn: Poly.
        //     has_type1 && ... && has_typen ==> has_type(apply(x, args), tret)) ==>
        //   has_type(box(mk_fun(x)), FUN(typ1...typn, tret))
        // trigger on has_type(box(mk_fun(x)), FUN(typ1...typn, tret))
        let inner_trigs = vec![has_app.clone()];
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_CONSTRUCTOR_INNER);
        let inner_bind = func_bind_trig(
            ctx,
            name,
            &Arc::new(vec![]),
            &Arc::new(params.clone()),
            &inner_trigs,
            false,
        );
        let inner_pre = mk_and(&pre);
        fun_has = Some(inner_pre.clone());
        let inner_imply = mk_implies(&inner_pre, &has_app);
        let inner_forall = mk_bind_expr(&inner_bind, &inner_imply);
        let mk_fun = str_apply(crate::def::MK_FUN, &vec![x_var.clone()]);
        let box_mk_fun = ident_apply(&prefix_box(&dpath), &vec![mk_fun]);
        let has_box_mk_fun = expr_has_type(&box_mk_fun, &id);
        let trigs = vec![has_box_mk_fun.clone()];
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_CONSTRUCTOR);
        let bind =
            func_bind_trig(ctx, name, tparams, &Arc::new(vec![x_param(&datatyp)]), &trigs, false);
        let imply = mk_implies(&inner_forall, &has_box_mk_fun);
        let forall = mk_bind_expr(&bind, &imply);
        let axiom = mk_unnamed_axiom(forall);
        axiom_commands.push(Arc::new(CommandX::Global(axiom)));

        // SpecFn apply axiom:
        // forall typ1 ... typn, tret, arg1: Poly ... argn: Poly, x: Fun.
        //   has_type_f && has_type1 && ... && has_typen => has_type(apply(x, args), tret)
        // trigger on apply(x, args), has_type_f
        params.push(x_param(&datatyp));
        pre.insert(0, has_box.clone());
        let trigs = vec![app.clone(), has_box.clone()];
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_APPLY);
        let aparams = Arc::new(params.clone());
        let bind = func_bind_trig(ctx, name, tparams, &aparams, &trigs, false);
        let imply = mk_implies(&mk_and(&pre), &has_app);
        let forall = mk_bind_expr(&bind, &imply);
        let axiom = mk_unnamed_axiom(forall);
        axiom_commands.push(Arc::new(CommandX::Global(axiom)));

        // SpecFn height axiom:
        // forall typ1 ... typn, tret, arg1: Poly ... argn: Poly, x: Fun.
        //   has_type_f && has_type1 && ... && has_typen ==>
        //     height_lt(height(apply(x, args)), height(box(mk_fun(x))))
        // trigger on height(apply(x, args)), has_type_f
        let height_app = str_apply(crate::def::HEIGHT, &vec![app]);
        let from_rec_fun = str_apply(crate::def::HEIGHT_REC_FUN, &vec![box_mk_fun]);
        let height_fun = str_apply(crate::def::HEIGHT, &vec![from_rec_fun]);
        let height_lt = str_apply(crate::def::HEIGHT_LT, &vec![height_app.clone(), height_fun]);
        let trigs = vec![height_app, has_box.clone()];
        let name =
            format!("{}_{}", path_as_friendly_rust_name(dpath), crate::def::QID_HEIGHT_APPLY);
        let bind = func_bind_trig(ctx, name, tparams, &aparams, &trigs, false);
        let imply = mk_implies(&mk_and(&pre), &height_lt);
        let forall = mk_bind_expr(&bind, &imply);
        let axiom = mk_unnamed_axiom(forall);
        axiom_commands.push(Arc::new(CommandX::Global(axiom)));
    }

    // constructor and field axioms
    for variant in variants.iter() {
        if ctx.datatypes_with_invariant.contains(dpath) {
            // constructor invariant axiom:
            //   forall typs, arg1 ... argn.
            //     inv1 && ... && invn => has_type(box(ctor(arg1 ... argn)), T(typs))
            // trigger on has_type(box(ctor(arg1 ... argn)), T(typs))
            let params = vec_map(&*variant.fields, |f| field_to_par(span, f));
            let params = Arc::new(params);
            let ctor_args = func_def_args(&Arc::new(vec![]), &params);
            let ctor = ident_apply(&variant_ident(&dpath, &variant.name), &ctor_args);
            let box_ctor = ident_apply(&prefix_box(&dpath), &vec![ctor]);
            let has_ctor = expr_has_type(&box_ctor, &datatype_id(&dpath, &typ_args));
            let mut pre: Vec<Expr> = Vec::new();
            for field in variant.fields.iter() {
                let (typ, _, _) = &field.a;
                let dis = crate::ast::VarIdentDisambiguate::Field;
                let name = crate::ast_util::str_unique_var(&("_".to_string() + &field.name), dis);
                if let Some(inv) = typ_invariant(ctx, typ, &ident_var(&name.lower())) {
                    pre.push(inv);
                }
            }
            let name = format!("{}_{}", &variant_ident(&dpath, &variant.name), QID_CONSTRUCTOR);
            let bind = func_bind(ctx, name, tparams, &params, &has_ctor, false);
            let imply = mk_implies(&mk_and(&pre), &has_ctor);
            let forall = mk_bind_expr(&bind, &imply);
            let axiom = mk_unnamed_axiom(forall);
            axiom_commands.push(Arc::new(CommandX::Global(axiom)));
        }
        for field in variant.fields.iter() {
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
            let name = format!("{}_{}", id, QID_ACCESSOR);
            let bind =
                func_bind_trig(ctx, name, &Arc::new(vec![]), &x_params(&datatyp), &trigs, false);
            let eq = mk_eq(&xfield, &xfield_internal);
            let forall = mk_bind_expr(&bind, &eq);
            let axiom = mk_unnamed_axiom(forall);
            axiom_commands.push(Arc::new(CommandX::Global(axiom)));

            if ctx.datatypes_with_invariant.contains(dpath) {
                if let Some(inv_f) = typ_invariant(ctx, typ, &xfield_unbox) {
                    // field invariant axiom:
                    //   forall typs, x. has_type(x, T(typs)) => inv_f(unbox(x).f)
                    // trigger on unbox(x).f, has_type(x, T(typs))
                    let trigs = vec![xfield_unbox.clone(), has.clone()];
                    let name = format!("{}_{}", id, QID_INVARIANT);
                    let bind =
                        func_bind_trig(ctx, name, tparams, &x_params(&vpolytyp), &trigs, false);
                    let imply = mk_implies(&has, &inv_f);
                    let forall = mk_bind_expr(&bind, &imply);
                    let axiom = mk_unnamed_axiom(forall);
                    axiom_commands.push(Arc::new(CommandX::Global(axiom)));
                }
            }
        }
    }

    if !ctx.datatypes_with_invariant.contains(dpath) && declare_box && !is_fun && !is_array {
        // If there are no visible refinement types (e.g. no refinement type fields,
        // or type is completely abstract to us), then has_type always holds:
        //   forall typs, x. has_type(box(x), T(typs))
        // trigger on has_type(box(x), T(typs))
        let name = format!("{}_{}", path_as_friendly_rust_name(dpath), QID_HAS_TYPE_ALWAYS);
        let bind = func_bind(ctx, name, tparams, &x_params(&datatyp), &has_box, false);
        let forall = mk_bind_expr(&bind, &has_box);
        axiom_commands.push(Arc::new(CommandX::Global(mk_unnamed_axiom(forall))));
    }

    // height axiom
    // (make sure that this stays in sync with recursive_types::check_well_founded)
    if add_height {
        for variant in variants.iter() {
            for field in variant.fields.iter() {
                use crate::recursive_types::TypNode;
                let typ = &field.a.0;
                let mut recursion_or_tparam = |t: &Typ| match &**t {
                    TypX::Datatype(path, _, _)
                        if ctx.global.datatype_graph.in_same_scc(
                            &TypNode::Datatype(path.clone()),
                            &TypNode::Datatype(dpath.clone()),
                        ) =>
                    {
                        Err(())
                    }
                    TypX::TypParam(_) => Err(()),
                    _ => Ok(()),
                };
                let has_recursion_or_tparam =
                    crate::ast_visitor::typ_visitor_check(typ, &mut recursion_or_tparam).is_err();
                if !has_recursion_or_tparam {
                    continue;
                }
                let typ = crate::ast_util::undecorate_typ(typ);
                let field_box_path = match &*typ {
                    TypX::SpecFn(typs, _) => Some(prefix_spec_fn_type(typs.len())),
                    TypX::Datatype(..) => crate::sst_to_air::datatype_box_prefix(ctx, &typ),
                    TypX::Boxed(_) => None,
                    TypX::TypParam(_) => None,
                    _ => continue,
                };
                let unboxed = if let TypX::Boxed(t) = &*typ { t } else { &*typ };
                let fun_or_map_ret = {
                    match unboxed {
                        TypX::SpecFn(_, ret) => Some(ret),
                        TypX::Datatype(d, targs, _)
                            if crate::ast_util::path_as_vstd_name(d)
                                == Some("map::Map".to_string())
                                && targs.len() == 2 =>
                        {
                            // HACK special case for the infinite map::Map type,
                            // which is like a FnSpec type
                            Some(&targs[1])
                        }
                        _ => None,
                    }
                };
                let recursive_function_field = if let Some(ret) = fun_or_map_ret {
                    // REVIEW: this is inspired by https://github.com/FStarLang/FStar/pull/2954 ,
                    // which restricts decreases on FnSpec applications or Map lookups
                    // to the case where the FnSpec or Map is a field of a recursive datatype
                    // and the application or lookup returns a value of the recursive datatype.
                    // It's not clear that we need this restriction, since we don't have F*'s
                    // universes, but let's err on the side of cautious for now.
                    // We define recursive_function_field to be true when all of these hold:
                    // 1) the field is a FnSpec or Map type
                    // 2) the only use of type parameters in the FnSpec/Map return type
                    //    is to instantiate the datatype with exactly its original parameters
                    // For example, recursive_function_field is true for field f here:
                    //   struct S<A, B> { a: A, b: B, f: FnSpec(int) -> Option<S<A, B>> }
                    // but is false for field f here:
                    //   struct S<A, B> { a: A, b: B, f: FnSpec(int) -> Option<(A, B)> }
                    // because A and B appear in the return type, but not as part of S<A, B>
                    // This suppresses decreases for a wrapper around a FnSpec or infinite Map:
                    //   struct MyFun<A, B>(FnSpec(A) -> B);
                    // TODO: allow recursive_function_field across mutually recursive datatypes
                    // that have type parameters (e.g. by inlining the recursive types).
                    let our_typ =
                        Arc::new(TypX::Datatype(dpath.clone(), typ_args.clone(), Arc::new(vec![])));
                    use crate::visitor::VisitorControlFlow;
                    let mut visitor = |t: &Typ| -> VisitorControlFlow<()> {
                        if crate::ast_util::types_equal(t, &our_typ) {
                            VisitorControlFlow::Return
                        } else if let TypX::TypParam(_) = &**t {
                            VisitorControlFlow::Stop(())
                        } else {
                            VisitorControlFlow::Recurse
                        }
                    };
                    let visit = crate::ast_visitor::typ_visitor_dfs(ret, &mut visitor);
                    visit == VisitorControlFlow::Recurse
                } else {
                    false
                };
                let nodes = crate::prelude::datatype_height_axioms(
                    &dpath,
                    &field_box_path,
                    &is_variant_ident(dpath, &*variant.name),
                    &variant_field_ident(&dpath, &variant.name, &field.name),
                    recursive_function_field,
                );
                let axioms =
                    air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
                        .nodes_to_commands(&nodes)
                        .expect("internal error: malformed datatype axiom");
                axiom_commands.extend(axioms.iter().cloned());
            }
        }
    }

    // ext_equal axiom for datatypes
    if add_ext_equal {
        let deep = air_unique_var("deep");
        let deep_var = ident_var(&deep.lower());
        let deep_param = var_param(deep, &Arc::new(TypX::Bool));
        let has_x = has;
        let y = str_ident("y");
        let y_var = ident_var(&y);
        let y_param = |typ: &Typ| var_param(air_unique_var(&y), typ);
        let unbox_y = ident_apply(&prefix_unbox(&dpath), &vec![y_var.clone()]);
        let has_y = expr_has_type(&y_var, &id);
        let eq_command = |s_name: &str, pre: &Vec<Expr>| {
            let params = Arc::new(vec![deep_param.clone(), x_param(&vpolytyp), y_param(&vpolytyp)]);
            let name = format!("{}_{}", &s_name, QID_EXT_EQUAL);
            let mut args = vec![deep_var.clone()];
            args.push(id.clone());
            args.push(x_var.clone());
            args.push(y_var.clone());
            let ext_eq_xy = str_apply(crate::def::EXT_EQ, &args);
            let bind = func_bind(ctx, name, tparams, &params, &ext_eq_xy, false);
            let imply = mk_implies(&mk_and(pre), &ext_eq_xy);
            let forall = mk_bind_expr(&bind, &imply);
            let axiom = mk_unnamed_axiom(forall);
            Arc::new(CommandX::Global(axiom))
        };
        for variant in variants.iter() {
            // per-variant ext_equal axiom:
            //   forall typs, deep: bool, x: Poly, y: Poly.
            //     has_x && has_y && veq && feq1 && ... && feqn ==> ext_eq(deep, typ, x, y)
            //   trigger on ext_eq(deep, typ, x, y)
            // where:
            //   veq is true for variants.len() == 1 or:
            //   - is_variant(x) && is_variant(y)
            //   feqk is one of:
            //   - x.fk == y.fk
            //   - ext_eq(deep, typk, x.fk, y.fk)
            let mut pre: Vec<Expr> = vec![has_x.clone(), has_y.clone()];
            if variants.len() > 1 {
                let vid = is_variant_ident(dpath, &*variant.name);
                pre.push(ident_apply(&vid, &vec![unbox_x.clone()]));
                pre.push(ident_apply(&vid, &vec![unbox_y.clone()]));
            }
            for field in variant.fields.iter() {
                use crate::recursive_types::TypNode;
                let (typ, _, _) = &field.a;
                let mut is_recursive = |t: &Typ| match &**t {
                    TypX::Datatype(path, _, _)
                        if ctx.global.datatype_graph.in_same_scc(
                            &TypNode::Datatype(path.clone()),
                            &TypNode::Datatype(dpath.clone()),
                        ) =>
                    {
                        Err(())
                    }
                    _ => Ok(()),
                };
                let uses_ext = uses_ext_equal(ctx, typ)
                    // to avoid trigger matching loops, use ==, not ext_equal, for recursive fields:
                    && !crate::ast_visitor::typ_visitor_check(typ, &mut is_recursive).is_err();
                let fid = variant_field_ident(&dpath, &variant.name, &field.name);
                let xfield = ident_apply(&fid, &vec![unbox_x.clone()]);
                let yfield = ident_apply(&fid, &vec![unbox_y.clone()]);
                let eq = if uses_ext {
                    let xfield = crate::sst_to_air::as_box(ctx, xfield, typ);
                    let yfield = crate::sst_to_air::as_box(ctx, yfield, typ);
                    let ftids = crate::sst_to_air::typ_to_id(typ);
                    let mut args = vec![deep_var.clone()];
                    args.push(ftids);
                    args.push(xfield);
                    args.push(yfield);
                    str_apply(crate::def::EXT_EQ, &args)
                } else {
                    mk_eq(&xfield, &yfield)
                };
                pre.push(eq);
            }
            axiom_commands.push(eq_command(&variant_ident(&dpath, &variant.name), &pre));
        }
        if is_fun {
            // SpecFn ext_equal axiom:
            //   forall typ1 ... typn, tret, deep: bool, x: Poly, y: Poly.
            //     has_typex && has_typey &&
            //     (forall arg1: Poly ... argn: Poly.
            //       has_type1 && ... && has_typen ==>
            //       ext_eq(deep, t1, apply(x, args), apply(y, args))
            //     ==> ext_eq(deep, t_lambda, x, y)
            //   trigger on ext_eq(deep, t_lambda, x, y)
            let mut pre: Vec<Expr> = vec![has_x.clone(), has_y.clone()];
            let args = fun_args.unwrap();
            let params = fun_params.unwrap().clone();
            let inner_has = fun_has.unwrap();
            let xapp = Arc::new(ExprX::ApplyFun(apolytyp.clone(), unbox_x.clone(), args.clone()));
            let yapp = Arc::new(ExprX::ApplyFun(apolytyp.clone(), unbox_y.clone(), args.clone()));
            let tparamret = typ_args.last().expect("return type").clone();
            let ret_ids = crate::sst_to_air::typ_to_id(&tparamret);
            let mut args = vec![deep_var.clone()];
            args.push(ret_ids);
            args.push(xapp);
            args.push(yapp);
            let ext_eq = str_apply(crate::def::EXT_EQ, &args);
            let imply = mk_implies(&inner_has, &ext_eq);
            let bind = func_bind_trig(
                ctx,
                format!("{}_inner_{}", path_as_friendly_rust_name(dpath), QID_EXT_EQUAL),
                &Arc::new(vec![]),
                &Arc::new(params.clone()),
                &vec![ext_eq.clone()],
                false,
            );
            pre.push(mk_bind_expr(&bind, &imply));
            axiom_commands.push(eq_command(&path_as_friendly_rust_name(dpath), &pre));
        }
    }
}

pub fn datatypes_and_primitives_to_air(ctx: &Ctx, datatypes: &crate::ast::Datatypes) -> Commands {
    let source_module = &ctx.module;
    let mut transparent_air_datatypes: Vec<air::ast::Datatype> = Vec::new();
    let mut opaque_sort_commands: Vec<Command> = Vec::new();
    let mut token_commands: Vec<Command> = Vec::new();
    let mut box_commands: Vec<Command> = Vec::new();
    let mut field_commands: Vec<Command> = Vec::new();
    let mut axiom_commands: Vec<Command> = Vec::new();

    for spec_fn_n_params in &ctx.spec_fn_types {
        let tparams: Vec<Ident> =
            (0..*spec_fn_n_params + 1).into_iter().map(prefix_tuple_param).collect();
        datatype_or_fun_to_air_commands(
            ctx,
            &mut field_commands,
            &mut token_commands,
            &mut box_commands,
            &mut axiom_commands,
            &ctx.global.no_span,
            &prefix_spec_fn_type(*spec_fn_n_params),
            &Arc::new(air::ast::TypX::Fun),
            None,
            Some(Arc::new(TypX::SpecFn(Arc::new(vec![]), Arc::new(TypX::Bool)))),
            &Arc::new(tparams),
            &Arc::new(vec![]),
            true,
            false,
            true,
            false,
            true,
        );
    }

    if ctx.uses_array {
        datatype_or_fun_to_air_commands(
            ctx,
            &mut field_commands,
            &mut token_commands,
            &mut box_commands,
            &mut axiom_commands,
            &ctx.global.no_span,
            &crate::def::array_type(),
            &Arc::new(air::ast::TypX::Fun),
            Some(DTypId::Primitive(crate::ast::Primitive::Array)),
            Some(Arc::new(TypX::Primitive(crate::ast::Primitive::Array, Arc::new(vec![])))),
            &Arc::new(vec![Arc::new("T".to_string()), Arc::new("N".to_string())]),
            &Arc::new(vec![]),
            false,
            true,
            true,
            false,
            true,
        );
    }

    for monotyp in &ctx.mono_types {
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
            Some(DTypId::Expr(crate::sst_to_air::monotyp_to_id(monotyp).last().unwrap().clone())),
            Some(crate::poly::monotyp_to_typ(monotyp)),
            &Arc::new(vec![]),
            &Arc::new(vec![]),
            false,
            false,
            true,
            false,
            false,
        );
    }

    for datatype in datatypes.iter() {
        let dpath = &datatype.x.path;
        let is_transparent = is_datatype_transparent(&source_module.x.path, datatype);

        if is_transparent {
            // Encode transparent types as AIR datatypes
            transparent_air_datatypes.push(datatype_to_air(ctx, datatype));
        }

        let mut tparams: Vec<Ident> = Vec::new();
        for (name, _strict_pos) in datatype.x.typ_params.iter() {
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
            false,
            is_transparent,
            is_transparent,
            is_transparent && datatype.x.ext_equal,
        );
    }

    for fun in &ctx.fndef_types {
        let func = ctx.func_map.get(fun).expect("expected fndef function in pruned crate");
        let tparams = &func.x.typ_params;
        let mut args: Vec<air::ast::Typ> = Vec::new();
        for _ in tparams.iter() {
            args.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }
        let decl_type_id = Arc::new(DeclX::fun_or_const(
            crate::def::prefix_fndef_type_id(fun),
            Arc::new(args),
            str_typ(crate::def::TYPE),
        ));
        token_commands.push(Arc::new(CommandX::Global(decl_type_id)));
    }

    let array_commands = if ctx.uses_array {
        let nodes = crate::prelude::array_functions(&prefix_box(&crate::def::array_type()));
        let cmds = air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .expect("internal error: malformed strslice functions");
        (*cmds).clone()
    } else {
        vec![]
    };

    let strslice_monotyp = Arc::new(crate::poly::MonoTypX::Primitive(
        crate::ast::Primitive::StrSlice,
        Arc::new(vec![]),
    ));
    let strslice_commands = if ctx.mono_types.contains(&strslice_monotyp) {
        let strslice_name = path_to_air_ident(&monotyp_to_path(&strslice_monotyp));
        let nodes = crate::prelude::strslice_functions(strslice_name.as_str());
        let cmds = air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .expect("internal error: malformed strslice functions");
        (*cmds).clone()
    } else {
        vec![]
    };

    let mut commands: Vec<Command> = Vec::new();
    commands.append(&mut opaque_sort_commands);
    commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Datatypes(Arc::new(
        transparent_air_datatypes,
    ))))));
    commands.append(&mut field_commands);
    commands.append(&mut token_commands);
    commands.append(&mut box_commands);
    commands.append(&mut axiom_commands);
    commands.extend(array_commands);
    commands.extend(strslice_commands);
    Arc::new(commands)
}
