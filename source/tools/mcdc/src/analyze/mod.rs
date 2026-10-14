//! Coverage analysis of recorded evaluations: record files (`records`), the MC/DC criterion
//! (`criterion`), and the `report`, `gaps` and `delta` outputs.

pub mod criterion;
pub mod records;

pub use criterion::*;
pub use records::*;

use crate::instrument::manifest::Decision;
use regex::Regex;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::Path;

/// Files whose checks decide what Verus accepts (mode checking, well-formedness, erasure, lowering
/// to SST/AIR). The report has a separate total for them and `gaps` ranks them first.
pub(crate) const PRIORITY: &[&str] = &[
    r"^vir/src/(well_formed|modes|safe_api|traits|erase[^/]*|resolution_inference|prune|recursion|ast_to_sst|sst_to_air|interpreter|poly|ast_simplify)\.rs$",
    r"^rust_verify/src/(rust_to_vir[^/]*|erase|lifetime[^/]*|verifier|fn_call_to_vir)\.rs$",
    r"^builtin_macros/src/syntax\.rs$",
];

/// Patterns over the decision text and the code it guards; each match adds its weight to the gap
/// score.
pub(crate) const SOUND_PATTERNS: &[(i64, &str)] = &[
    (
        6,
        r"\b(err_str|err_string|error\(|Err\(|return Err|internal_error|unsupported_err|err_span|crate::messages::error|\.error\(|user_error|VirErr)",
    ),
    (
        5,
        r"\b(assume|axiom|Assume|admit|external_body|trusted|unsafe|erase|Erase|ghost|Ghost|tracked|Tracked|Mode::(Spec|Proof|Exec)|mode)",
    ),
    (
        4,
        r"\b(check|Check|requires|ensures|decreases|recommends|well_formed|invariant|termination|opaque|reveal|broadcast|trigger)",
    ),
    (2, r"\b(panic!|unreachable!|assert!)"),
];

/// Per-file weight added to the gap score (first match).
pub(crate) const FILE_WEIGHT: &[(&str, i64)] = &[
    (
        r"^vir/src/(well_formed|modes|safe_api|traits|erase[^/]*|resolution_inference|recursion)\.rs$",
        6,
    ),
    (r"^rust_verify/src/(erase|lifetime[^/]*)\.rs$", 6),
    (r"^vir/src/(prune|ast_to_sst|sst_to_air|interpreter|poly|ast_simplify)\.rs$", 5),
    (r"^rust_verify/src/(rust_to_vir[^/]*|verifier|fn_call_to_vir)\.rs$", 5),
    (r"^builtin_macros/src/syntax\.rs$", 5),
];

pub(crate) struct Rules {
    priority: Vec<Regex>,
    sound: Vec<(i64, Regex)>,
    file_weight: Vec<(Regex, i64)>,
    hint: Regex,
}

impl Rules {
    pub(crate) fn new() -> Rules {
        Rules {
            priority: PRIORITY.iter().map(|p| Regex::new(p).unwrap()).collect(),
            sound: SOUND_PATTERNS.iter().map(|(w, p)| (*w, Regex::new(p).unwrap())).collect(),
            file_weight: FILE_WEIGHT.iter().map(|(p, w)| (Regex::new(p).unwrap(), *w)).collect(),
            hint: Regex::new(
                r"(return Err\([^;]{0,120}|err_str\([^;]{0,120}|error\([^;]{0,120}|Err\([^;]{0,120}|panic!\([^;]{0,100}|unsupported_err!\([^;]{0,100})",
            )
            .unwrap(),
        }
    }
    pub(crate) fn is_priority(&self, file: &str) -> bool {
        self.priority.iter().any(|r| r.is_match(file))
    }
    /// Score from the decision text, the guarded code and the file; also returns the matched words.
    pub(crate) fn score(&self, d: &Decision) -> (i64, Vec<String>) {
        let ctx = format!("{} {}", d.guarded, d.text);
        let mut s = 0;
        let mut hits = Vec::new();
        for (w, r) in &self.sound {
            if let Some(m) = r.find(&ctx) {
                s += w;
                hits.push(m.as_str().trim_matches(|c| c == '(' || c == ':').to_string());
            }
        }
        if let Some((_, w)) = self.file_weight.iter().find(|(r, _)| r.is_match(&d.file)) {
            s += w;
        }
        (s, hits)
    }
    pub(crate) fn auto_hint(&self, d: &Decision) -> String {
        let g = &d.guarded;
        let tgt = match self.hint.find(g) {
            Some(m) => m.as_str().to_string(),
            None => g.chars().take(120).collect(),
        };
        let lead = match d.kind.as_str() {
            "if" => "then-branch",
            "while" => "loop body",
            "guard" => "arm body",
            k => k,
        };
        format!("in fn {}; {}: {}", d.func, lead, tgt)
    }
}

pub(crate) fn trunc(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

pub(crate) fn outcomes_str(o: &BTreeSet<bool>) -> String {
    // F before T
    o.iter().map(|b| if *b { 'T' } else { 'F' }).collect()
}

pub(crate) fn coverage_of(d: &Decision, data: &Data) -> Coverage {
    match data.get(&d.id) {
        Some(v) if !v.is_empty() => analyze(d.n(), v),
        _ => Coverage::default(),
    }
}

pub(crate) fn pct(a: usize, b: usize) -> String {
    if b == 0 { "n/a".to_string() } else { format!("{:.1}%", 100.0 * a as f64 / b as f64) }
}

#[derive(Default, Clone)]
pub struct Summary {
    pub label: String,
    pub decisions: usize,
    pub reached: usize,
    pub full_mcdc: usize,
    pub atoms: usize,
    pub mcdc_atoms: usize,
    pub cond_atoms: usize,
    pub dec_outcomes: usize,
}

pub const SUMMARY_COLS: &str = "label\tdecisions\treached\tfull_mcdc\tatoms\tmcdc_atoms\tmcdc\tcond_atoms\tcond\tdec_outcomes\tdec";

impl Summary {
    pub(crate) fn add(&mut self, d: &Decision, reached: bool, c: &Coverage) {
        self.decisions += 1;
        self.reached += reached as usize;
        self.full_mcdc += (c.mcdc.len() == d.n()) as usize;
        self.atoms += d.n();
        self.mcdc_atoms += c.mcdc.len();
        self.cond_atoms += c.cond().len();
        self.dec_outcomes += c.outcomes.len();
    }
    pub(crate) fn cells(&self) -> Vec<String> {
        vec![
            self.label.clone(),
            self.decisions.to_string(),
            self.reached.to_string(),
            self.full_mcdc.to_string(),
            self.atoms.to_string(),
            self.mcdc_atoms.to_string(),
            pct(self.mcdc_atoms, self.atoms),
            self.cond_atoms.to_string(),
            pct(self.cond_atoms, self.atoms),
            self.dec_outcomes.to_string(),
            pct(self.dec_outcomes, 2 * self.decisions),
        ]
    }
}

pub(crate) fn md_table(rows: &[Summary]) -> String {
    let cols: Vec<&str> = SUMMARY_COLS.split('\t').collect();
    let mut s = format!("| {} |\n|{}\n", cols.join(" | "), "---|".repeat(cols.len()));
    for r in rows {
        let _ = writeln!(s, "| {} |", r.cells().join(" | "));
    }
    s
}

pub(crate) fn create(path: &Path) -> Result<std::io::BufWriter<std::fs::File>, String> {
    std::fs::File::create(path)
        .map(std::io::BufWriter::new)
        .map_err(|e| format!("{}: {}", path.display(), e))
}

macro_rules! w {
    ($f:expr, $($t:tt)*) => {
        std::io::Write::write_fmt(&mut $f, format_args!($($t)*)).map_err(|e| e.to_string())?
    };
}

mod delta;
mod gaps;
mod report;

pub use delta::delta;
pub use gaps::{gaps, read_hints};
pub use report::report;
