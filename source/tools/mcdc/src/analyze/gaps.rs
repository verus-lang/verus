//! `mcdc gaps`: GAPS.tsv and GAPS.md.

use super::*;
use crate::instrument::manifest::Decision;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

const GAPS_HEADER: &str = "\
# MC/DC gaps

One section per decision with at least one atom that has no independence pair in the recorded
evaluations, ranked by score (soundness-related words in the decision and the code it guards,
plus a per-file weight; +10 for priority files; -3 for decisions never reached, which line
coverage already reports). GAPS.tsv has every uncovered atom; this file has the first 400
decisions.

Pair notation: one letter per atom in source order, `T` true, `F` false, `-` not evaluated
(short-circuited), then `=>` and the decision outcome. `TT-=>T vs TF-=>F` means: an evaluation
with atoms 0 and 1 true and atom 2 not evaluated, outcome true, and one with atom 1 false,
outcome false. \"new vector needed\" is the side of the pair that no recorded evaluation matches
(`both` when neither does). The pair is computed from the decision structure alone; correlated
atoms can make it infeasible.

";

/// Writes GAPS.tsv and GAPS.md; returns (decisions with gaps, rows, priority-file decisions with
/// gaps).
pub fn gaps(
    man: &[Decision],
    data: &Data,
    out: &Path,
    hints: &BTreeMap<String, String>,
) -> Result<(usize, usize, usize), String> {
    let rules = Rules::new();
    let empty = BTreeSet::new();
    let mut gl = Vec::new();
    for d in man {
        let c = coverage_of(d, data);
        if c.mcdc.len() == d.n() {
            continue;
        }
        let (mut sc, hits) = rules.score(d);
        if rules.is_priority(&d.file) {
            sc += 10;
        }
        let vecs = data.get(&d.id).unwrap_or(&empty);
        if vecs.is_empty() {
            sc -= 3;
        }
        gl.push((sc, d, vecs, c, hits));
    }
    gl.sort_by(|a, b| {
        b.0.cmp(&a.0).then_with(|| a.1.file.cmp(&b.1.file)).then(a.1.line.cmp(&b.1.line))
    });
    std::fs::create_dir_all(out).map_err(|e| format!("{}: {}", out.display(), e))?;
    let mut tsv = create(&out.join("GAPS.tsv"))?;
    w!(
        tsv,
        "rank\tscore\tpriority_file\tfile:line\tid\tkind\tfn\treached\toutcomes_seen\tatoms_covered/total\t\
         uncovered_atom\tatom_text\tneeded_pair (atom order; T/F/- not evaluated; =>outcome)\tnew_vector_needed\t\
         decision_text\tsoundness_tags\thint\n"
    );
    let mut md = String::from(GAPS_HEADER);
    let mut nrows = 0;
    let mut nprio = 0;
    for (k, (sc, d, vecs, c, hits)) in gl.iter().enumerate() {
        let rank = k + 1;
        let loc = d.loc();
        let prio = rules.is_priority(&d.file);
        nprio += prio as usize;
        let hint = hints
            .get(&loc)
            .or_else(|| hints.get(&d.id.to_string()))
            .cloned()
            .unwrap_or_else(|| rules.auto_hint(d));
        let mut ostr = outcomes_str(&c.outcomes);
        if ostr.is_empty() {
            ostr = "none".into();
        }
        let tree = parse_tree(&d.tree).map_err(|e| format!("{} tree {:?}: {}", loc, d.tree, e))?;
        let mut mdl = Vec::new();
        for i in (0..d.n()).filter(|i| !c.mcdc.contains(i)) {
            let (pair, need) = match needed_pair(&tree, d.n(), vecs, i) {
                None => (
                    "no independence pair exists in the decision structure (or n>18)".to_string(),
                    "-".to_string(),
                ),
                Some(p) => (format!("{} vs {}", p.with_true, p.with_false), p.needed().to_string()),
            };
            let atext = &d.atoms[i].text;
            w!(
                tsv,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}/{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                rank,
                sc,
                prio as u8,
                loc,
                d.id,
                d.kind,
                d.func,
                if vecs.is_empty() { "False" } else { "True" },
                ostr,
                c.mcdc.len(),
                d.n(),
                i,
                trunc(atext, 200),
                pair,
                need,
                trunc(&d.text, 300),
                hits.join(","),
                hint
            );
            nrows += 1;
            mdl.push(format!(
                "  - atom {} `{}`: pair `{}`; new vector needed: `{}`",
                i,
                trunc(atext, 120),
                pair,
                need
            ));
        }
        if rank <= 400 {
            let _ = writeln!(
                md,
                "### {}. `{}` (score {}, {}, fn `{}`, MC/DC {}/{}, outcomes seen: {})\n",
                rank,
                loc,
                sc,
                d.kind,
                d.func,
                c.mcdc.len(),
                d.n(),
                ostr
            );
            let _ = writeln!(md, "`{}`\n", trunc(&d.text, 400));
            let tags = if hits.is_empty() { "none".to_string() } else { hits.join(", ") };
            let _ = writeln!(md, "Structure (atom indices): `{}`. Tags: {}.\n", d.tree, tags);
            for l in mdl {
                let _ = writeln!(md, "{}", l);
            }
            let _ = writeln!(md, "  - hint: {}\n", hint);
        }
    }
    std::io::Write::flush(&mut tsv).map_err(|e| e.to_string())?;
    std::fs::write(out.join("GAPS.md"), md).map_err(|e| e.to_string())?;
    Ok((gl.len(), nrows, nprio))
}

/// Reads a hints file: `file:line<TAB>hint` or `id<TAB>hint` per line; `#` starts a comment line.
pub fn read_hints(path: &Path) -> Result<BTreeMap<String, String>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path.display(), e))?;
    let mut m = BTreeMap::new();
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some((k, v)) = line.split_once('\t') {
            m.insert(k.to_string(), v.to_string());
        }
    }
    Ok(m)
}
