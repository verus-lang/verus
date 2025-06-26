use crate::ast::{GenericBoundX, Opaquetype, TypX};
use crate::ast_util::LowerUniqueVar;
use crate::ast_util::path_as_friendly_rust_name;
use crate::check_ast_flavor::ident_binder;
use crate::context::Ctx;
use crate::def::new_internal_qid;
use crate::def::prefix_type_id;
use crate::sst_to_air::typ_to_ids;
use crate::traits::{const_typ_bound_to_air, typ_equality_bound_to_air};
use air::ast::BindX;
use air::ast::Triggers;
use air::ast::{Command, CommandX, Commands, DeclX};
use air::ast_util::{ident_apply, mk_bind_expr, mk_unnamed_axiom, str_typ};
use core::panic;
use std::sync::Arc;

pub fn opaque_types_to_air(ctx: &Ctx, opaque_types: &Vec<Opaquetype>) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    for opaque_type in opaque_types {
        let mut args_typ = Vec::new();
        for _ in opaque_type.x.typ_params.iter() {
            args_typ.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }

        let decl_dcr_id = Arc::new(DeclX::fun_or_const(
            crate::def::prefix_dcr_id(&opaque_type.x.name),
            Arc::new(args_typ.clone()),
            str_typ(crate::def::DECORATION),
        ));
        let decl_type_id = Arc::new(DeclX::fun_or_const(
            prefix_type_id(&opaque_type.x.name),
            Arc::new(args_typ.clone()),
            str_typ(crate::def::TYPE),
        ));

        commands.push(Arc::new(CommandX::Global(decl_dcr_id.clone())));
        commands.push(Arc::new(CommandX::Global(decl_type_id.clone())));

        let mut type_params = Vec::new();
        let mut args = Vec::new();
        for param in opaque_type.x.typ_params.iter() {
            args.extend(typ_to_ids(ctx, param));
            if let TypX::TypParam(id) = &**param {
                type_params.push(id.clone());
            } else {
                panic!()
            }
        }

        if opaque_type.x.typ_params.len() != 0 {
            let self_dcr = ident_apply(&crate::def::prefix_dcr_id(&opaque_type.x.name), &args);
            let self_type = ident_apply(&crate::def::prefix_type_id(&opaque_type.x.name), &args);

            let name: String = format!(
                "{}_{}",
                path_as_friendly_rust_name(&opaque_type.x.name),
                crate::def::QID_OPAQUE_TYPE_BOUND
            );

            let bind = {
                let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
                for typ_param in type_params.iter() {
                    for (x, t) in crate::def::suffix_typ_param_ids_types(&typ_param) {
                        binders.push(ident_binder(&x.lower(), &str_typ(t)));
                    }
                }
                // for param in params.iter() {
                //     let name = if matches!(param.x.purpose, ParPurpose::MutPre) {
                //         prefix_pre_var(&param.x.name.lower())
                //     } else {
                //         param.x.name.lower()
                //     };
                //     binders.push(ident_binder(&name, &typ_to_air(ctx, &param.x.typ)));
                // }
                let triggers: Triggers =
                    Arc::new(vec![Arc::new(vec![self_dcr]), Arc::new(vec![self_type])]);
                let qid = new_internal_qid(ctx, name);
                Arc::new(BindX::Quant(air::ast::Quant::Forall, Arc::new(binders), triggers, qid))
            };
            // crate::sst_to_air_func::func_bind_trig(
            //     ctx,
            //     name,
            //     &Arc::new(type_params),
            //     &Arc::new(vec![]),
            //     &vec![self_dcr, self_type],
            //     false,
            // );
            let mut bound_exprs: Vec<air::ast::Expr> = Vec::new();
            for bound in opaque_type.x.typ_bounds.iter() {
                match &**bound {
                    GenericBoundX::Trait(path, typ_args) => {
                        if let Some(bound) = crate::traits::trait_bound_to_air(ctx, path, typ_args)
                        {
                            bound_exprs.push(bound);
                        }
                    }
                    GenericBoundX::TypEquality(path, typ_args, name, typ) => {
                        bound_exprs.push(typ_equality_bound_to_air(ctx, path, typ_args, name, typ));
                    }
                    GenericBoundX::ConstTyp(c, t) => {
                        bound_exprs.push(const_typ_bound_to_air(ctx, c, t));
                    }
                }
            }
            let and = air::ast_util::mk_and(&bound_exprs);
            let forall = mk_bind_expr(&bind, &and);
            let axiom = mk_unnamed_axiom(forall);
            commands.push(Arc::new(CommandX::Global(axiom)));
        } else {
            let mut bound_exprs: Vec<air::ast::Expr> = Vec::new();
            for bound in opaque_type.x.typ_bounds.iter() {
                match &**bound {
                    GenericBoundX::Trait(path, typ_args) => {
                        if let Some(bound) = crate::traits::trait_bound_to_air(ctx, path, typ_args)
                        {
                            bound_exprs.push(bound);
                        }
                    }
                    GenericBoundX::TypEquality(path, typ_args, name, typ) => {
                        bound_exprs.push(typ_equality_bound_to_air(ctx, path, typ_args, name, typ));
                    }
                    GenericBoundX::ConstTyp(c, t) => {
                        bound_exprs.push(const_typ_bound_to_air(ctx, c, t));
                    }
                }
            }
            let and = air::ast_util::mk_and(&bound_exprs);
            let axiom = mk_unnamed_axiom(and);
            commands.push(Arc::new(CommandX::Global(axiom)));
        }
    }

    Arc::new(commands)
}
