use rustc_hir::{ExprKind, OwnerInfo, BodyId, Expr, Closure};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use crate::rustc_hir::intravisit::Visitor;

pub(crate) struct SpecHir<'tcx> {
    pub bodies: HashMap<BodyId, &'tcx rustc_hir::Expr<'tcx>>,
}

impl<'tcx> SpecHir<'tcx> {
    pub(crate) fn new() -> Self {
        SpecHir { bodies: HashMap::new() }
    }

    pub(crate) fn update_owner(
        &mut self,
        tcx: TyCtxt<'tcx>,
        owner_info: &'tcx OwnerInfo<'tcx>,
        main_body_id: &BodyId,
    ) -> &'tcx OwnerInfo<'tcx> {
        let body_ids_to_cut = get_relevant_closure_ids(tcx, owner_info, main_body_id);
        if body_ids_to_cut.len() == 0 {
            return owner_info;
        }

        let mut bodies = owner_info.nodes.bodies.clone();

        let my_owner_id = owner_info.node().def_id();
        for body_id in body_ids_to_cut.iter() {
            assert!(body_id.hir_id.owner == my_owner_id);
            let old_body = &owner_info.nodes.bodies[&body_id.hir_id.local_id];
            let expr = tcx.hir_arena.alloc(rustc_hir::Expr {
                hir_id: old_body.value.hir_id,
                kind: rustc_hir::ExprKind::Tup(&[]),
                span: old_body.value.span,
            });
            let new_body = tcx.hir_arena.alloc(rustc_hir::Body {
                params: old_body.params,
                value: expr,
            });
            bodies[&body_id.hir_id.local_id] = new_body;
        }

        let nodes: rustc_hir::OwnerNodes<'tcx> = rustc_hir::OwnerNodes {
            opt_hash_including_bodies: owner_info
                .nodes
                .opt_hash_including_bodies,
            nodes: owner_info.nodes.nodes.clone(),
            bodies,
        };
        let attrs: rustc_hir::AttributeMap<'tcx> =
            rustc_hir::AttributeMap {
                map: owner_info.attrs.map.clone(),
                opt_hash: owner_info.attrs.opt_hash,
            };
        tcx.hir_arena.alloc(rustc_hir::OwnerInfo {
            nodes,
            parenting: owner_info.parenting.clone(),
            attrs,
            trait_map: owner_info
                .trait_map
                .items()
                .map(|(&id, traits)| {
                    (
                        id,
                        traits
                            .iter()
                            .map(|trait_| rustc_hir::TraitCandidate {
                                def_id: trait_.def_id,
                                import_ids: trait_.import_ids.clone(),
                            })
                            .collect(),
                    )
                })
                .collect(),
        })
    }
}

fn get_relevant_closure_ids<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_info: &'tcx OwnerInfo<'tcx>,
    main_body_id: &BodyId,
) -> Vec<BodyId>
{
    let mut v = VisitMod { tcx, ids: vec![] };
    v.visit_body(&owner_info.nodes.bodies[&main_body_id.hir_id.local_id]);
    return dbg!(v.ids);
}

struct VisitMod<'tcx> {
    tcx: TyCtxt<'tcx>,
    ids: Vec<BodyId>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitMod<'tcx> {
    type Map = rustc_middle::hir::map::Map<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = &ex.kind {
            if is_spec_code_wrapper(callee) {
                assert!(args.len() == 1);

                if let ExprKind::Closure(Closure { body, .. }) = &args[0].kind {
                    self.ids.push(*body);
                } else {
                    panic!("get_relevant_closure_ids: expected Closure");
                }
            }
        }
        crate::rustc_hir::intravisit::walk_expr(self, ex);
    }
}

fn is_spec_code_wrapper<'tcx>(callee: &'tcx Expr<'tcx>) -> bool {
    /*match &callee.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => 
    }*/
    dbg!(callee);
    todo!();
}
