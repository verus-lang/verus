//! The mutant map (mutants.tsv), the decision table (decisions.tsv), mutant selection and the
//! bitset file that the mutant runtime reads from MUTANT_BITSET.
//!
//! mutants.tsv: first line `# commit=<40 hex> count=<n>`, second line the header, then one line per
//! mutant with the columns of `COLUMNS`. Its FNV-1a 64 digest is the map digest that the runtime and
//! every bitset carry.
//!
//! Bitset: 8 bytes magic `VMUTBS01`, 40 bytes commit (ASCII), u32 LE mutant count, u64 LE map
//! digest, then ceil((count + 1) / 8) bytes where bit i (least significant bit first) selects mutant i.

use super::rewrite::{MutDecision, Mutant};
use std::collections::BTreeSet;

pub const COLUMNS: &str = "id\tpoint\tcrate\tfile\tfn\trange\top\tclass\tdecision\tdecision_loc\tguards\tatom\torig\tmutated";
pub const MAGIC: &[u8; 8] = b"VMUTBS01";

/// Operator group of each operator.
pub fn class_of(op: &str) -> &'static str {
    match op {
        "cond-true" | "cond-false" | "cond-negate" | "while-false" | "decision-negate"
        | "and-or-swap" => "condition",
        "delete-stmt" | "skip-err-return" => "datapath-delete",
        "err-to-ok" | "drop-try" => "datapath-error",
        "ret-negate" | "ret-true" | "ret-false" => "datapath-return",
        "vec-remove" => "datapath-vec",
        "rel-boundary" | "eq-flip" => "datapath-compare",
        "const-plus1" | "const-minus1" | "index-plus1" | "index-minus1" => "datapath-const",
        "option-get-none" | "option-some-none" | "option-unwrap-or-default" => "option",
        "enum-variant" => "enum",
        _ => "container",
    }
}

pub fn fnv(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in data {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

pub fn splitmix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E3779B97F4A7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
    x ^ (x >> 31)
}

fn one_line(s: &str, n: usize) -> String {
    let s = s.replace('\t', " ").split_whitespace().collect::<Vec<_>>().join(" ");
    if s.chars().count() <= n { s } else { s.chars().take(n - 3).collect::<String>() + "..." }
}

/// The text of mutants.tsv.
pub fn mutants_tsv(mutants: &[Mutant], commit: &str) -> String {
    let mut o = format!("# commit={} count={}\n{}\n", commit, mutants.len(), COLUMNS);
    for m in mutants {
        let (dec, loc) = match (m.atom_decision, m.guards.last()) {
            (Some((d, l)), _) => (d.to_string(), format!("{}:{}", m.file, l)),
            (None, Some((d, oc, f, l))) => (format!("{}:{}", d, oc), format!("{}:{}", f, l)),
            (None, None) => ("-".into(), "-".into()),
        };
        let guards =
            m.guards.iter().map(|(d, oc, _, _)| format!("{}:{}", d, oc)).collect::<Vec<_>>();
        let fields = [
            m.id.to_string(),
            m.point.to_string(),
            m.krate.clone(),
            m.file.clone(),
            m.func.clone(),
            format!("{}:{}-{}:{}", m.line, m.col, m.end_line, m.end_col),
            m.op.to_string(),
            class_of(m.op).to_string(),
            dec,
            loc,
            if guards.is_empty() { "-".into() } else { guards.join(",") },
            m.atom.map_or("-".into(), |a| a.to_string()),
            one_line(&m.orig, 160),
            one_line(&m.mutated, 160),
        ];
        o.push_str(&fields.join("\t"));
        o.push('\n');
    }
    o
}

/// The text of decisions.tsv.
pub fn decisions_tsv(decs: &[MutDecision]) -> String {
    let mut o = String::from("id\tmcdc\tkind\tfile\tline\tcol\tfn\tnarms\tnatoms\ttext\n");
    for d in decs {
        o.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            d.id,
            d.mcdc,
            d.kind,
            d.file,
            d.line,
            d.col,
            d.func,
            d.narms,
            d.natoms,
            one_line(&d.text, 200)
        ));
    }
    o
}

/// The build constants included by the runtime.
pub fn build_consts(commit: &str, count: usize, digest: u64, mutants_on: bool) -> String {
    format!(
        "pub const BUILD_COMMIT: &str = {:?};\npub const BUILD_COUNT: u32 = {};\npub const BUILD_DIGEST: u64 = 0x{:016x};\npub const BUILD_MUTANTS: bool = {};\n",
        commit, count, digest, mutants_on
    )
}

#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    pub id: u32,
    pub file: String,
    pub func: String,
    pub line: usize,
    pub op: String,
    pub class: String,
}

pub struct Map {
    pub commit: String,
    pub count: u32,
    pub digest: u64,
    pub rows: Vec<Row>,
}

/// Parses mutants.tsv.
pub fn parse_map(data: &[u8]) -> Result<Map, String> {
    let digest = fnv(data);
    let text = std::str::from_utf8(data).map_err(|e| format!("map is not UTF-8: {}", e))?;
    let mut lines = text.lines();
    let head = lines.next().unwrap_or("");
    let (mut commit, mut count) = (String::new(), 0u32);
    for kv in head.trim_start_matches('#').split_whitespace() {
        if let Some(v) = kv.strip_prefix("commit=") {
            commit = v.to_string()
        }
        if let Some(v) = kv.strip_prefix("count=") {
            count = v.parse().unwrap_or(0)
        }
    }
    if commit.len() != 40 {
        return Err("map header must be `# commit=<40 hex> count=<n>`".into());
    }
    let hdr: Vec<&str> = lines.next().unwrap_or("").split('\t').collect();
    let col = |n: &str| hdr.iter().position(|h| *h == n).ok_or(format!("map has no column {}", n));
    let (ci, cf, cfn, cr, cop, ccl) =
        (col("id")?, col("file")?, col("fn")?, col("range")?, col("op")?, col("class")?);
    let mut rows = Vec::new();
    for (k, l) in lines.enumerate() {
        let f: Vec<&str> = l.split('\t').collect();
        let bad = || format!("map line {}: malformed", k + 3);
        if f.len() < hdr.len() {
            return Err(bad());
        }
        rows.push(Row {
            id: f[ci].parse().map_err(|_| bad())?,
            file: f[cf].to_string(),
            func: f[cfn].to_string(),
            line: f[cr].split(':').next().unwrap_or("").parse().map_err(|_| bad())?,
            op: f[cop].to_string(),
            class: f[ccl].to_string(),
        });
    }
    if rows.len() != count as usize {
        return Err(format!("map header says {} mutants, found {}", count, rows.len()));
    }
    Ok(Map { commit, count, digest, rows })
}

/// Mutant selection. Selectors (ids, files, fns, locs) are united; with none, every mutant is
/// selected. Filters then apply in order: classes, random sample.
#[derive(Default, Clone, Debug)]
pub struct Selection {
    pub ids: Vec<u32>,
    pub files: Vec<String>,
    pub fns: Vec<String>,
    pub locs: Vec<(String, usize)>,
    /// Operator names or classes; `datapath` matches every `datapath-*` class; `all` matches all.
    pub classes: Vec<String>,
    /// Keep a mutant when splitmix64(seed ^ splitmix64(id)) falls below rate * 2^64.
    pub random: Option<(u64, f64)>,
}

fn fn_match(full: &str, pat: &str) -> bool {
    full == pat || full.ends_with(&format!("::{}", pat))
}

pub fn select(map: &Map, s: &Selection) -> Result<BTreeSet<u32>, String> {
    for i in &s.ids {
        if *i == 0 || *i > map.count {
            return Err(format!("id {} not in 1..={}", i, map.count));
        }
    }
    let any = !(s.ids.is_empty() && s.files.is_empty() && s.fns.is_empty() && s.locs.is_empty());
    let ids: BTreeSet<u32> = s.ids.iter().copied().collect();
    let mut out = BTreeSet::new();
    for r in &map.rows {
        let mut keep = !any
            || ids.contains(&r.id)
            || s.files.iter().any(|f| *f == r.file)
            || s.fns.iter().any(|p| fn_match(&r.func, p))
            || s.locs.iter().any(|(f, l)| *f == r.file && *l == r.line);
        if keep && !s.classes.is_empty() {
            keep = s.classes.iter().any(|c| {
                c == "all"
                    || *c == r.op
                    || *c == r.class
                    || (c == "datapath" && r.class.starts_with("datapath"))
            });
        }
        if keep {
            if let Some((seed, rate)) = s.random {
                let h = splitmix(seed ^ splitmix(r.id as u64));
                keep = (h as f64) < rate * (u64::MAX as f64);
            }
        }
        if keep {
            out.insert(r.id);
        }
    }
    Ok(out)
}

/// The bitset file for `ids`.
pub fn bitset(map: &Map, ids: &BTreeSet<u32>) -> Vec<u8> {
    let mut b = Vec::new();
    b.extend_from_slice(MAGIC);
    b.extend_from_slice(map.commit.as_bytes());
    b.extend_from_slice(&map.count.to_le_bytes());
    b.extend_from_slice(&map.digest.to_le_bytes());
    let mut bits = vec![0u8; (map.count as usize + 1 + 7) / 8];
    for i in ids {
        bits[*i as usize / 8] |= 1 << (*i % 8);
    }
    b.extend_from_slice(&bits);
    b
}

/// Decodes a bitset file: (commit, count, digest, selected ids). Same checks as the runtime.
pub fn read_bitset(data: &[u8]) -> Result<(String, u32, u64, BTreeSet<u32>), String> {
    if data.len() < 60 || &data[0..8] != MAGIC {
        return Err("bad magic".into());
    }
    let commit = String::from_utf8_lossy(&data[8..48]).to_string();
    let count = u32::from_le_bytes(data[48..52].try_into().unwrap());
    let digest = u64::from_le_bytes(data[52..60].try_into().unwrap());
    let bits = &data[60..];
    if bits.len() < (count as usize + 1 + 7) / 8 {
        return Err("truncated".into());
    }
    let ids = (1..=count).filter(|i| (bits[*i as usize / 8] >> (*i % 8)) & 1 == 1).collect();
    Ok((commit, count, digest, ids))
}
