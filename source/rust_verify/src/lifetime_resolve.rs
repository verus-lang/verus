// In functions executed through the lifetime rustc driver, use `ldbg!` for debug output.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::BorrowCheckResult, ty::TyCtxt};

use crate::lifetime::leprintln;

pub(crate) fn check_resolves<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    _borrow_check_result: &BorrowCheckResult<'tcx>,
) {
    let opts = rustc_borrowck::consumers::ConsumerOptions::RegionInferenceContext;
    let body_with_facts =
        rustc_borrowck::consumers::get_body_with_borrowck_facts(tcx, def_id, opts);
    let body = &body_with_facts.body;
    let borrow_set = &body_with_facts.borrow_set;
    let borrows_out_of_scope =
        rustc_borrowck::consumers::calculate_borrows_out_of_scope_at_location(
            &body_with_facts.body,
            &body_with_facts.region_inference_context,
            &borrow_set,
        );
    let mut resolved_at = std::collections::HashSet::new();
    for (bb, bbd) in rustc_middle::mir::traversal::reachable(&body) {
        if let Some(terminator) = &bbd.terminator {
            match &terminator.kind {
                rustc_middle::mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    call_source,
                    fn_span,
                } => {
                    if let rustc_middle::ty::TyKind::FnDef(fn_def_id, _) =
                        func.ty(&body.local_decls, tcx).kind()
                    {
                        if tcx.is_diagnostic_item(
                            rustc_span::Symbol::intern("verus::lifetime::resolve"),
                            *fn_def_id,
                        ) {
                            let rustc_middle::mir::Operand::Move(resolve_place) = &args[0] else {
                                panic!("invalid resolve");
                            };
                            if let Some(target) = target {
                                for (i, s) in body[*target].statements.iter().enumerate() {
                                    if matches!(s.kind, rustc_middle::mir::StatementKind::StorageDead(p) if p == resolve_place.local)
                                    {
                                        let loc = rustc_middle::mir::Location {
                                            block: *target,
                                            statement_index: i,
                                        };
                                        resolved_at.insert(loc);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }
    for (i, bw) in body_with_facts.borrow_set.location_map.iter().enumerate() {
        let local_span = body.local_decls[bw.1.borrowed_place.local].source_info.span;
        let borrowed_local_info =
            &**body.local_decls[bw.1.borrowed_place.local].local_info.as_ref().assert_crate_local();
        if let rustc_middle::mir::LocalInfo::User(local_binding_form) = &borrowed_local_info {
            let out_of_scope_at: Vec<_> = borrows_out_of_scope
                .iter()
                .filter_map(|bos| bos.1.iter().find(|bi| bi.as_usize() == i).map(|_| bos.0))
                .filter(|loc| !body[loc.block].is_cleanup)
                .collect();
            fn span_to_diagnostic_span(
                tcx: TyCtxt<'_>,
                span: rustc_span::Span,
            ) -> crate::lifetime::DiagnosticSpan {
                let lo = tcx.sess.source_map().lookup_char_pos(span.lo());
                let hi = tcx.sess.source_map().lookup_char_pos(span.hi());
                crate::lifetime::DiagnosticSpan {
                    line_start: lo.line,
                    column_start: lo.col.0,
                    line_end: hi.line,
                    column_end: hi.col.0,
                }
            }
            for loc in out_of_scope_at.iter() {
                if loc.block != bw.0.block && !resolved_at.contains(loc) {
                    let mut spans = vec![span_to_diagnostic_span(tcx, local_span)];
                    if let Some(terminator) = &body[bw.1.reserve_location.block].terminator {
                        spans.push(span_to_diagnostic_span(tcx, terminator.source_info.span));
                    }
                    let d = crate::lifetime::Diagnostic {
                        message: format!(
                            "a mutable borrow that lives more than a single statement was not explicitly resolved"
                        ),
                        level: format!("error"),
                        spans,
                    };
                    eprintln!(
                        "{}",
                        serde_json::to_string(&d).expect("cannot serialize resolve diagnostic")
                    );
                }
            }
        }
    }

    if cfg!(any()) {
        let mut debug_output = String::new();
        use std::fmt::Write;
        writeln!(&mut debug_output, "mir for {:?}", def_id).unwrap();

        for (bb, bbd) in rustc_middle::mir::traversal::reachable(&body) {
            if bbd.is_cleanup {
                writeln!(&mut debug_output, "{:?} (cleanup)", &bb).unwrap();
                continue;
            }
            writeln!(&mut debug_output, "{:?}", &bb).unwrap();
            let mut loc = bb.start_location();
            for (s, statement) in bbd.statements.iter().enumerate() {
                writeln!(&mut debug_output, "    [{}] {:?}", &s, &statement).unwrap();
                loc = loc.successor_within_block();
            }
            writeln!(&mut debug_output, "    {:?}", &bbd.terminator().kind).unwrap();
        }

        leprintln!(&debug_output);
    }
}
