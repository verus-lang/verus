//! `mcdc delta`: what new records add to a base set.

use super::*;
use crate::instrument::manifest::Decision;
use std::collections::{BTreeMap, BTreeSet};

/// What `new` covers that `base` does not: decisions reached, decision outcomes, condition-covered
/// atoms and MC/DC atoms of the union `base + new`. Returns the report lines and the summary line.
pub fn delta(man: &[Decision], base: &Data, new: &Data) -> Vec<String> {
    let by_id: BTreeMap<u32, &Decision> = man.iter().map(|d| (d.id, d)).collect();
    let (mut newdec, mut newatoms, mut newcond, mut newout, mut reached) = (0, 0, 0, 0, 0);
    let mut lines = Vec::new();
    let empty = BTreeSet::new();
    for (id, nv) in new {
        let Some(d) = by_id.get(id) else { continue };
        reached += 1;
        let bv = base.get(id).unwrap_or(&empty);
        let union: BTreeSet<(bool, u128)> = bv.union(nv).copied().collect();
        let cb = if bv.is_empty() { Coverage::default() } else { analyze(d.n(), bv) };
        let cu = analyze(d.n(), &union);
        let loc = d.loc();
        let text = trunc(&d.text, 150);
        if bv.is_empty() {
            newdec += 1;
            lines.push(format!(
                "NEW-DECISION {} id={} (never reached by baseline) `{}`",
                loc, id, text
            ));
        }
        for o in cu.outcomes.difference(&cb.outcomes) {
            newout += 1;
            lines.push(format!(
                "NEW-OUTCOME  {} id={} outcome={} `{}`",
                loc,
                id,
                if *o { 'T' } else { 'F' },
                text
            ));
        }
        for i in cu.cond().difference(&cb.cond()) {
            newcond += 1;
            lines.push(format!(
                "NEW-COND     {} id={} atom {} `{}` now seen true and false",
                loc,
                id,
                i,
                trunc(&d.atoms[*i].text, 100)
            ));
        }
        for i in cu.mcdc.difference(&cb.mcdc) {
            newatoms += 1;
            lines.push(format!(
                "NEW-MCDC     {} id={} atom {} `{}` independence shown (decision `{}`)",
                loc,
                id,
                i,
                trunc(&d.atoms[*i].text, 100),
                text
            ));
        }
    }
    lines.push(format!(
        "summary: decisions reached by program: {}; newly reached decisions: {}; new decision outcomes: {}; \
         new condition-covered atoms: {}; new MC/DC atoms: {}",
        reached, newdec, newout, newcond, newatoms
    ));
    lines
}
