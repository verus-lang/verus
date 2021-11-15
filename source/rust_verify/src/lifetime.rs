//! Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables

use rustc_hir::{AssocItemKind, ItemKind};

pub(crate) fn check<'tcx>(queries: &'tcx rustc_interface::Queries<'tcx>) {
    queries.global_ctxt().expect("global_ctxt").peek_mut().enter(|tcx| {
        let hir = tcx.hir();
        let krate = hir.krate();
        for (_id, item) in &krate.items {
            match &item.kind {
                rustc_hir::ItemKind::Fn(..) => {
                    tcx.ensure().mir_borrowck(item.def_id);
                }
                ItemKind::Impl(impll) => {
                    for item in impll.items {
                        match item.kind {
                            AssocItemKind::Fn { .. } => {
                                tcx.ensure().mir_borrowck(item.id.def_id);
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    });
}
