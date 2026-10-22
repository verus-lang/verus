//! `mcdc report`: decisions.tsv, per-file.tsv and summary.md.

use super::*;
use crate::instrument::manifest::Decision;
use std::collections::BTreeMap;
use std::path::Path;

/// Writes decisions.tsv, per-file.tsv and summary.md to `out`; returns the summary text (per-crate
/// totals, the priority-file total and the overall total, then the priority files).
pub fn report(man: &[Decision], data: &Data, out: &Path) -> Result<String, String> {
    let rules = Rules::new();
    std::fs::create_dir_all(out).map_err(|e| format!("{}: {}", out.display(), e))?;
    let mut f = create(&out.join("decisions.tsv"))?;
    w!(f, "id\tfile:line\tkind\tatoms\tmcdc_covered\tcond_covered\toutcomes\tvectors\ttext\n");
    let mut by_file: BTreeMap<&str, Summary> = BTreeMap::new();
    let mut by_crate: BTreeMap<&str, Summary> = BTreeMap::new();
    let mut prio = Summary { label: "PRIORITY FILES".into(), ..Default::default() };
    let mut all = Summary { label: "ALL".into(), ..Default::default() };
    for d in man {
        let c = coverage_of(d, data);
        let nvec = data.get(&d.id).map_or(0, |v| v.len());
        let reached = nvec > 0;
        w!(
            f,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            d.id,
            d.loc(),
            d.kind,
            d.n(),
            c.mcdc.len(),
            c.cond().len(),
            outcomes_str(&c.outcomes),
            nvec,
            trunc(&d.text, 200)
        );
        let fs = by_file
            .entry(&d.file)
            .or_insert_with(|| Summary { label: d.file.clone(), ..Default::default() });
        fs.add(d, reached, &c);
        let cr = d.file.split('/').next().unwrap_or("");
        let cs = by_crate
            .entry(cr)
            .or_insert_with(|| Summary { label: cr.to_string(), ..Default::default() });
        cs.add(d, reached, &c);
        if rules.is_priority(&d.file) {
            prio.add(d, reached, &c);
        }
        all.add(d, reached, &c);
    }
    std::io::Write::flush(&mut f).map_err(|e| e.to_string())?;
    let mut pf = create(&out.join("per-file.tsv"))?;
    w!(pf, "{}\n", SUMMARY_COLS);
    for s in by_file.values() {
        w!(pf, "{}\n", s.cells().join("\t"));
    }
    std::io::Write::flush(&mut pf).map_err(|e| e.to_string())?;
    let mut tot: Vec<Summary> = by_crate.values().cloned().collect();
    tot.push(prio);
    tot.push(all);
    let prio_files: Vec<Summary> =
        by_file.values().filter(|s| rules.is_priority(&s.label)).cloned().collect();
    let txt = format!("{}\nPriority files:\n\n{}", md_table(&tot), md_table(&prio_files));
    std::fs::write(out.join("summary.md"), &txt).map_err(|e| e.to_string())?;
    Ok(txt)
}
