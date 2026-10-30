//! The observers `-V observer=<name>` can select. A new observer is registered here: an arm in
//! `create_observer`, and in `emit_observer_summaries` if it reports a summary.

use vir::messages::{ToAny, note_bare};

/// The observer registered under `name`, with a handle per trait it implements; `None` if
/// no observer has that name.
pub(crate) fn create_observer(name: &str) -> Option<vir::vir_observer::Observers> {
    use std::cell::RefCell;
    use std::rc::Rc;
    match name {
        "test" => {
            let o = Rc::new(RefCell::new(crate::test_observer::TestObserver::new()));
            let vir: Rc<RefCell<dyn vir::vir_observer::VirObserver>> = o.clone();
            let air: Rc<RefCell<dyn air::air_observer::AirObserver>> = o.clone();
            let query_result: Rc<RefCell<dyn air::query_result_observer::QueryResultObserver>> =
                o.clone();
            Some(vir::vir_observer::Observers {
                vir: Some(vir),
                air: Some(air),
                query_result: Some(query_result),
                span_resolver: None,
            })
        }
        // Dedicated single-trait observers: each populates only its own slot,
        // proving a consumer couples nothing it does not implement.
        "air-only" => {
            let o = Rc::new(RefCell::new(crate::test_observer::AirOnlyObserver::new()));
            let air: Rc<RefCell<dyn air::air_observer::AirObserver>> = o;
            Some(vir::vir_observer::Observers { air: Some(air), ..Default::default() })
        }
        "query-result-only" => {
            let o = Rc::new(RefCell::new(crate::test_observer::QueryResultOnlyObserver::new()));
            let qr: Rc<RefCell<dyn air::query_result_observer::QueryResultObserver>> = o;
            Some(vir::vir_observer::Observers { query_result: Some(qr), ..Default::default() })
        }
        "vir-only" => {
            let o = Rc::new(RefCell::new(crate::test_observer::VirOnlyObserver::new()));
            let vir: Rc<RefCell<dyn vir::vir_observer::VirObserver>> = o;
            Some(vir::vir_observer::Observers { vir: Some(vir), ..Default::default() })
        }
        _ => None,
    }
}

/// The observer named by `-V observer=`, if any.
pub(crate) fn create_observer_from_args(
    name: Option<&str>,
) -> Result<vir::vir_observer::Observers, String> {
    match name {
        None => Ok(Default::default()),
        Some(name) => create_observer(name).ok_or_else(|| format!("unknown observer `{name}`")),
    }
}

pub(crate) fn emit_observer_summaries(
    any: &dyn std::any::Any,
    reporter: &impl air::messages::Diagnostics,
) {
    if let Some(o) = any.downcast_ref::<crate::test_observer::TestObserver>() {
        reporter.report(&note_bare(&o.summary_json()).to_any());
    } else if let Some(o) = any.downcast_ref::<crate::test_observer::AirOnlyObserver>() {
        reporter.report(&note_bare(&o.summary_json()).to_any());
    } else if let Some(o) = any.downcast_ref::<crate::test_observer::QueryResultOnlyObserver>() {
        reporter.report(&note_bare(&o.summary_json()).to_any());
    } else if let Some(o) = any.downcast_ref::<crate::test_observer::VirOnlyObserver>() {
        reporter.report(&note_bare(&o.summary_json()).to_any());
    }
}
