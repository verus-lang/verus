//! Example:
//!   trait View { type V; }
//!   impl View for u8 { type V = u8; }
//!   impl<A> View for Vec<u8> { type V = Seq<A> }
//! We need to compute type ids for View::V.
//! In the SMT encoding, we write a function that computes View::V as a function of the self type
//! (and also possibly any trait type parameters):
//!   (declare-fun View::V (Type) Type)
//! where we generate axioms that say, for example:
//!   (View::V u8) == u8
//!   (View::V (Vec A)) == (Seq (View::V A))

use crate::ast::{AssocTypeImpl, AssocTypeImplX, Trait};
use crate::context::Ctx;
use crate::def::QID_ASSOC_TYPE_IMPL;
use crate::sst_to_air::typ_to_ids;
use crate::sst_to_air_func::func_bind_trig;
use air::ast::{Command, CommandX, Commands, DeclX, Expr};
use air::ast_util::{ident_apply, mk_bind_expr, mk_eq, mk_unnamed_axiom, str_typ};
use std::sync::Arc;

pub fn assoc_type_decls_to_air(_ctx: &Ctx, traits: &Vec<Trait>) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    for tr in traits {
        for name in tr.x.assoc_typs.iter() {
            let mut push_command = |decoration: bool, index: usize| {
                let projector = crate::def::projection(decoration, &tr.x.name, name);
                let mut typs: Vec<air::ast::Typ> = Vec::new();
                let n = 1 + tr.x.typ_params.len(); // self type + type arguments
                for _ in 0..n {
                    typs.extend(crate::def::types().iter().map(|s| str_typ(s)));
                }
                let ret = str_typ(crate::def::types()[index]);
                let declx = DeclX::Fun(projector, Arc::new(typs), ret);
                commands.push(Arc::new(CommandX::Global(Arc::new(declx))));
            };
            if crate::context::DECORATE {
                push_command(true, 0);
                push_command(false, 1);
            } else {
                push_command(false, 0);
            }
        }
    }
    Arc::new(commands)
}

pub fn assoc_type_impls_to_air(ctx: &Ctx, assocs: &Vec<AssocTypeImpl>) -> Commands {
    let mut commands: Vec<Command> = Vec::new();
    for assoc in assocs {
        let AssocTypeImplX {
            name,
            impl_path: _,
            typ_params,
            typ_bounds: _,
            trait_path,
            trait_typ_args,
            typ,
            impl_paths: _,
        } = &assoc.x;
        // forall typ_params. trait_path/name(decoration, trait_typ_args) == typ
        // Note: we assume here that the typ_params appear in trait_typ_args,
        // so that trait_path/name(decoration, trait_typ_args) works as a trigger.
        // Example:
        //   impl<A> T<u8, u16> for S<A> { type X = bool; }
        //   forall A. T/X(decoration, S<A>, u8, u16) == bool
        let (trait_typ_args, holes) = crate::traits::hide_projections(trait_typ_args);
        let (typ_params, eqs) = crate::sst_to_air_func::hide_projections_air(typ_params, holes);
        let eqs = air::ast_util::mk_and(&eqs);
        let mut push_command = |decoration: bool, index: usize| {
            let projector = crate::def::projection(decoration, trait_path, name);
            let mut args: Vec<Expr> = Vec::new();
            for arg in trait_typ_args.iter() {
                args.extend(typ_to_ids(arg));
            }
            let projection = ident_apply(&projector, &args);
            let typ_id = typ_to_ids(typ)[index].clone();
            let eq = mk_eq(&projection, &typ_id);
            let qname = format!("{}_{}_{}", projector, QID_ASSOC_TYPE_IMPL, decoration);
            let bind = func_bind_trig(
                ctx,
                qname,
                &typ_params,
                &Arc::new(vec![]),
                &vec![projection],
                false,
            );
            let imply = air::ast_util::mk_implies(&eqs, &eq);
            let forall = mk_bind_expr(&bind, &imply);
            commands.push(Arc::new(CommandX::Global(mk_unnamed_axiom(forall))));
        };
        if crate::context::DECORATE {
            push_command(true, 0);
            push_command(false, 1);
        } else {
            push_command(false, 0);
        }
    }
    Arc::new(commands)
}
