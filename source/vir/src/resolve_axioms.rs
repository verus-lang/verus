use crate::ast::{
    Datatype, Dt, FieldOpr, Krate, Mode, Path, Primitive, SpannedTyped, Typ, TypDecoration, TypX,
    UnaryOpr, VarBinder, VarBinderX, VarIdentDisambiguate,
};
use crate::ast_util::QUANT_FORALL;
use crate::context::Ctx;
use crate::def::*;
use crate::sst::{BndX, ExpX};
use crate::sst_to_air::{ExprCtxt, ExprMode};
use crate::sst_util::{sst_conjoin, sst_implies};
use air::ast::{Axiom, Command, CommandX, DeclX};
use air::ast_util::str_ident;
use air::node;
use air::printer::{macro_push_node, str_to_node};
use sise::Node;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum ResolvableType {
    Datatype(Dt),
    Decoration(TypDecoration),
    MutRef,
    Slice,
    Array,
}

pub struct ResolvedTypeCollection {
    module: Path,
    datatype_map: HashMap<Dt, Datatype>,

    worklist: Vec<ResolvableType>,
    set: HashSet<ResolvableType>,
}

impl ResolvedTypeCollection {
    pub fn new(module: &Path, krate: &Krate) -> Self {
        let mut datatype_map = HashMap::<Dt, Datatype>::new();
        for d in krate.datatypes.iter() {
            datatype_map.insert(d.x.name.clone(), d.clone());
        }
        ResolvedTypeCollection {
            module: module.clone(),
            datatype_map,
            worklist: vec![],
            set: HashSet::new(),
        }
    }

    pub fn visit_type(&mut self, typ: &Typ) {
        match &**typ {
            TypX::Datatype(dt, args, _) => {
                let datatype = &self.datatype_map[dt];
                if crate::ast_util::is_transparent_to(&datatype.x.transparency, &self.module) {
                    self.append(ResolvableType::Datatype(dt.clone()));
                }
                for arg in args.iter() {
                    self.visit_type(arg);
                }
            }
            TypX::MutRef(_t) => {
                self.append(ResolvableType::MutRef);
            }
            TypX::Primitive(Primitive::Slice, args) => {
                self.append(ResolvableType::Slice);
                self.visit_type(&args[0]);
            }
            TypX::Primitive(Primitive::Array, args) => {
                self.append(ResolvableType::Array);
                self.visit_type(&args[0]);
            }
            TypX::Primitive(Primitive::StrSlice | Primitive::Ptr | Primitive::Global, _) => {
                // trivial resolve
            }
            TypX::Decorate(dec, _, t) => {
                match dec {
                    TypDecoration::Ref
                    | TypDecoration::MutRef
                    | TypDecoration::Rc
                    | TypDecoration::Arc
                    | TypDecoration::Ghost
                    | TypDecoration::Never
                    | TypDecoration::ConstPtr => {
                        // trivial resolve
                    }

                    TypDecoration::Box | TypDecoration::Tracked => {
                        self.append(ResolvableType::Decoration(*dec));
                        self.visit_type(t);
                    }
                }
            }
            TypX::Bool
            | TypX::Int(_)
            | TypX::Real
            | TypX::Float(_)
            | TypX::SpecFn(..)
            | TypX::AnonymousClosure(..)
            | TypX::FnDef(..)
            | TypX::Boxed(_)
            | TypX::TypParam(_)
            | TypX::Projection { .. }
            | TypX::PointeeMetadata(_)
            | TypX::TypeId
            | TypX::ConstInt(_)
            | TypX::ConstBool(_)
            | TypX::Air(_)
            | TypX::Opaque { .. } => {
                // trivial resolve
            }
        }
    }

    fn append(&mut self, rt: ResolvableType) {
        if self.set.insert(rt.clone()) {
            self.worklist.push(rt);
        }
    }

    fn visit_datatype_fields(&mut self, dt: Dt) {
        let datatype = self.datatype_map[&dt].clone();
        for variant in datatype.x.variants.iter() {
            for field in variant.fields.iter() {
                self.visit_type(&field.a.0);
            }
        }
    }

    pub fn finish(self) -> Vec<ResolvableType> {
        let mut s = self;
        let mut idx = 0;
        while idx < s.worklist.len() {
            if let ResolvableType::Datatype(dt) = s.worklist[idx].clone() {
                s.visit_datatype_fields(dt);
            }
            idx += 1;
        }
        s.worklist
    }
}

pub fn resolve_mut_ref_axiom() -> Node {
    let decoration = str_to_node(DECORATION);
    let typ = str_to_node(TYPE);
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    let has_type = str_to_node(HAS_TYPE);
    let type_id_mut_ref = str_to_node(TYPE_ID_MUT_REF);
    let resolved = str_to_node(HAS_RESOLVED);
    let decorate_nil_sized = str_to_node(DECORATE_NIL_SIZED);
    let mut_ref_current = str_to_node(MUT_REF_CURRENT);
    let mut_ref_future = str_to_node(MUT_REF_FUTURE);

    node!(
        (axiom (forall ((d [decoration]) (t [typ]) (x [Poly])) (!
            (=>
                (and
                    ([has_type] x ([type_id_mut_ref] d t))
                    ([resolved] [decorate_nil_sized] ([type_id_mut_ref] d t) x)
                )
                (= ([mut_ref_current] x) ([mut_ref_future] x))
            )
            :pattern (([resolved] [decorate_nil_sized] ([type_id_mut_ref] d t) x))
            :qid prelude_resolved_mut_ref
            :skolemid skolem_prelude_resolved_mut_ref
        )))
    )
}

pub fn resolve_decoration_axiom(dec: &TypDecoration) -> Node {
    let decoration = str_to_node(DECORATION);

    let typ = str_to_node(TYPE);
    #[allow(non_snake_case)]
    let Poly = str_to_node(POLY);
    let has_type = str_to_node(HAS_TYPE);
    let resolved = str_to_node(HAS_RESOLVED);

    let decorate_tracked = str_to_node(DECORATE_TRACKED);
    let decorate_box = str_to_node(DECORATE_BOX);

    match dec {
        TypDecoration::Tracked => {
            node!(
                (axiom (forall ((d [decoration]) (t [typ]) (x [Poly])) (!
                    (=>
                        (and
                            ([has_type] x t)
                            ([resolved] ([decorate_tracked] d) t x)
                        )
                        ([resolved] d t x)
                    )
                    :pattern (([resolved] ([decorate_tracked] d) t x))
                    :qid prelude_resolved_tracked_decoration
                    :skolemid skolem_prelude_resolved_tracked_decoration
                )))
            )
        }
        TypDecoration::Box => {
            node!(
              (axiom (forall ((d1 [decoration]) (t1 [typ]) (d [decoration]) (t [typ]) (x [Poly])) (!
                    (=>
                        (and
                            ([has_type] x t)
                            ([resolved] ([decorate_box] d1 t1 d) t x)
                        )
                        ([resolved] d t x)
                    )
                    :pattern (([resolved] ([decorate_box] d1 t1 d) t x))
                    :qid prelude_resolved_tracked_decoration
                    :skolemid skolem_prelude_resolved_tracked_decoration
                )))
            )
        }
        _ => unreachable!(),
    }
}

fn resolve_datatype_axiom(ctx: &Ctx, dt: &Dt) -> Vec<Command> {
    let datatype = &ctx.datatype_map[dt];
    if !crate::ast_util::is_transparent_to(&datatype.x.transparency, &ctx.module.x.path) {
        return vec![];
    }
    if datatype.x.destructor {
        return vec![];
    }

    let span = &datatype.span;

    let mut decl_commands = vec![];

    for variant in datatype.x.variants.iter() {
        for field in variant.fields.iter() {
            if matches!(&field.a.1, Mode::Spec) {
                continue;
            }

            // forall |typ_args..., x: Dt<typ_args...>|
            //        has_resolved(x, Dt<typ_args>)
            //          && is_variant(x, variant)
            //        ==> has_resolved(x.field)
            // trigger on ( has_resolved(x), x.field )

            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for p in datatype.x.typ_params.iter() {
                let typ = Arc::new(TypX::TypeId);
                let bind = VarBinderX { name: crate::ast_util::typ_unique_var(&p.0), a: typ };
                binders.push(Arc::new(bind));
            }
            let x_name =
                crate::ast::VarIdent(str_ident("x"), VarIdentDisambiguate::VirExprNoNumber);
            let typ_args = datatype
                .x
                .typ_params
                .iter()
                .map(|p| Arc::new(TypX::TypParam(p.0.clone())))
                .collect::<Vec<Typ>>();
            let x_typ = Arc::new(TypX::Datatype(dt.clone(), Arc::new(typ_args), Arc::new(vec![])));
            binders.push(Arc::new(VarBinderX { name: x_name.clone(), a: x_typ.clone() }));

            let xvar_x = ExpX::Var(x_name);
            let xvar = SpannedTyped::new(span, &x_typ, xvar_x);

            let x_has_resolvedx =
                ExpX::UnaryOpr(UnaryOpr::HasResolved(x_typ.clone()), xvar.clone());
            let x_has_resolved = SpannedTyped::new(span, &Arc::new(TypX::Bool), x_has_resolvedx);

            let x_is_variant = if datatype.x.variants.len() == 1 {
                None
            } else {
                let x_is_variantx = ExpX::UnaryOpr(
                    UnaryOpr::IsVariant { datatype: dt.clone(), variant: variant.name.clone() },
                    xvar.clone(),
                );
                Some(SpannedTyped::new(span, &Arc::new(TypX::Bool), x_is_variantx))
            };

            let field_typ = &field.a.0;

            let x_fieldx = ExpX::UnaryOpr(
                UnaryOpr::Field(FieldOpr {
                    datatype: dt.clone(),
                    variant: variant.name.clone(),
                    field: field.name.clone(),
                    get_variant: false,
                    check: crate::ast::VariantCheck::None,
                }),
                xvar,
            );
            let x_field = SpannedTyped::new(span, &field_typ, x_fieldx);

            let x_field_has_resolvedx =
                ExpX::UnaryOpr(UnaryOpr::HasResolved(field_typ.clone()), x_field.clone());
            let x_field_has_resolved =
                SpannedTyped::new(span, &Arc::new(TypX::Bool), x_field_has_resolvedx);

            let trig = Arc::new(vec![x_has_resolved.clone(), x_field]);
            let triggers = Arc::new(vec![trig]);

            let hyps = match x_is_variant {
                None => vec![x_has_resolved],
                Some(x_is_variant) => vec![x_has_resolved, x_is_variant],
            };
            let hyp = sst_conjoin(span, &hyps);

            let impli = sst_implies(span, &hyp, &x_field_has_resolved);

            let bndx = BndX::Quant(QUANT_FORALL, Arc::new(binders), triggers, None);
            let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), impli.clone());

            let forall: Arc<SpannedTyped<ExpX>> =
                SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);

            let forall = crate::poly::visit_exp_native_for_pure_exp(ctx, &forall);

            let expr_ctxt = ExprCtxt::new_mode(ExprMode::Spec);
            let expr = crate::sst_to_air::exp_to_expr(ctx, &forall, &expr_ctxt).unwrap();

            let axiom = Arc::new(DeclX::Axiom(Axiom { named: None, expr: expr }));

            decl_commands.push(Arc::new(CommandX::Global(axiom)));
        }
    }

    decl_commands
}

pub fn resolve_axioms(ctx: &Ctx) -> Vec<Command> {
    let mut nodes = vec![];
    let mut commands: Vec<Command> = vec![];
    for r in ctx.resolved_typs.iter() {
        match r {
            ResolvableType::Datatype(dt) => {
                commands.append(&mut resolve_datatype_axiom(ctx, dt));
            }
            ResolvableType::MutRef => {
                nodes.push(resolve_mut_ref_axiom());
            }
            ResolvableType::Decoration(dec) => {
                nodes.push(resolve_decoration_axiom(dec));
            }
            ResolvableType::Slice | ResolvableType::Array => {
                // TODO(new_mut_ref)
            }
        }
    }

    let cmds = air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
        .nodes_to_commands(&nodes)
        .expect("internal error: malformed has_resolved axioms");
    let mut cmds = (*cmds).clone();
    cmds.append(&mut commands);

    cmds
}
