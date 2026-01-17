use crate::ast::{GenericBoundX, OpaqueType, TypX};
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
use air::ast_util::{ident_apply, mk_bind_expr, mk_unnamed_axiom, str_typ, str_var};
use core::panic;
use std::sync::Arc;

/// Each OpaqueType is named using its VIR path (generated from DefId)
/// For each OpaqueType (definition of opaque type), we generate the following air commands:
/// First, we define two functions: DCR%path and TYPE%path:
/// They can take arguments and return the decoration and type of the opaque type.
/// Second, we define a range of axioms to encode the trait bounds and the associate types.
pub fn opaque_types_to_air(ctx: &Ctx, opaque_types: &Vec<OpaqueType>) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    for opaque_type in opaque_types {
        // The arguments needed to instantiate the OpaqueType
        let mut args_typ = Vec::new();
        for _ in opaque_type.x.typ_params.iter() {
            args_typ.extend(crate::def::types().iter().map(|s| str_typ(s)));
        }

        // DCR%path function
        let decl_dcr_id = Arc::new(DeclX::fun_or_const(
            crate::def::prefix_dcr_id(&opaque_type.x.name),
            Arc::new(args_typ.clone()),
            str_typ(crate::def::DECORATION),
        ));
        // TYPE%path function
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

        // Axioms for trait bounds and associate types
        if opaque_type.x.typ_params.len() != 0 {
            // The OpaqueType takes some arguments to instantiate. Use functions
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
                let triggers: Triggers = Arc::new(vec![
                    Arc::new(vec![self_dcr.clone()]),
                    Arc::new(vec![self_type.clone()]),
                ]);
                let qid = new_internal_qid(ctx, name);
                Arc::new(BindX::Quant(air::ast::Quant::Forall, Arc::new(binders), triggers, qid))
            };
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

            if let Some(external_opaque_type) = &opaque_type.x.external_fn_opaque_type {
                let external_axiom_name: String = format!(
                    "{}_{}",
                    path_as_friendly_rust_name(&opaque_type.x.name),
                    crate::def::QID_EXTERNAL_OPAQUE_TYPE_EQUAL
                );
                let external_dcr =
                    ident_apply(&crate::def::prefix_dcr_id(&external_opaque_type.x.name), &args);
                let external_type =
                    ident_apply(&crate::def::prefix_type_id(&external_opaque_type.x.name), &args);

                let external_axiom_bind = {
                    let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
                    for typ_param in type_params.iter() {
                        for (x, t) in crate::def::suffix_typ_param_ids_types(&typ_param) {
                            binders.push(ident_binder(&x.lower(), &str_typ(t)));
                        }
                    }
                    let triggers: Triggers = Arc::new(vec![
                        Arc::new(vec![self_dcr.clone()]),
                        Arc::new(vec![self_type.clone()]),
                        Arc::new(vec![external_dcr.clone()]),
                        Arc::new(vec![external_type.clone()]),
                    ]);
                    let qid = new_internal_qid(ctx, external_axiom_name);
                    Arc::new(BindX::Quant(
                        air::ast::Quant::Forall,
                        Arc::new(binders),
                        triggers,
                        qid,
                    ))
                };
                let dcr_eq = air::ast_util::mk_eq(&self_dcr, &external_dcr);
                let type_eq = air::ast_util::mk_eq(&self_type, &external_type);
                let external_and = air::ast_util::mk_and(&vec![dcr_eq, type_eq]);
                let external_forall = mk_bind_expr(&external_axiom_bind, &external_and);
                let external_axiom = mk_unnamed_axiom(external_forall);
                commands.push(Arc::new(CommandX::Global(external_axiom)));
            }
        } else {
            // The OpaqueType takes no argument to instantiate. Use const.
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

            if let Some(external_opaque_type) = &opaque_type.x.external_fn_opaque_type {
                let self_dcr = str_var(&crate::def::prefix_dcr_id(&opaque_type.x.name));
                let self_type = str_var(&crate::def::prefix_type_id(&opaque_type.x.name));

                let external_dcr =
                    str_var(&crate::def::prefix_dcr_id(&external_opaque_type.x.name));
                let external_type =
                    str_var(&crate::def::prefix_type_id(&external_opaque_type.x.name));

                let dcr_eq = air::ast_util::mk_eq(&self_dcr, &external_dcr);
                let type_eq = air::ast_util::mk_eq(&self_type, &external_type);

                let and = air::ast_util::mk_and(&vec![dcr_eq, type_eq]);
                let axiom = mk_unnamed_axiom(and);
                commands.push(Arc::new(CommandX::Global(axiom)));
            }
        }
    }

    Arc::new(commands)
}
