//! Record files. A record is 20 little-endian bytes: u32 key = id << 1 | outcome, then u128 vec,
//! with 2 bits per atom i: bit 2i = evaluated, bit 2i+1 = value.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub const REC: usize = 20;

/// Distinct (outcome, vec) pairs per decision id.
pub type Data = BTreeMap<u32, BTreeSet<(bool, u128)>>;

/// Expands directories to their `.mcdc` and `.bin` files (sorted); keeps files as given.
fn input_files(inputs: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut out = Vec::new();
    for p in inputs {
        if p.is_dir() {
            let mut v: Vec<PathBuf> = std::fs::read_dir(p)
                .map_err(|e| format!("{}: {}", p.display(), e))?
                .filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|q| q.extension().map_or(false, |x| x == "mcdc" || x == "bin"))
                .collect();
            v.sort();
            out.extend(v);
        } else if p.exists() {
            out.push(p.clone());
        } else {
            return Err(format!("{}: no such file or directory", p.display()));
        }
    }
    Ok(out)
}

/// Distinct raw records of all inputs. A truncated record at the end of a file (a process killed
/// during a write) is dropped.
pub fn load_raw(inputs: &[PathBuf]) -> Result<BTreeSet<[u8; REC]>, String> {
    let mut raw = BTreeSet::new();
    for path in input_files(inputs)? {
        let b = std::fs::read(&path).map_err(|e| format!("{}: {}", path.display(), e))?;
        for c in b.chunks_exact(REC) {
            raw.insert(<[u8; REC]>::try_from(c).unwrap());
        }
    }
    Ok(raw)
}

pub fn decode(r: &[u8; REC]) -> (u32, bool, u128) {
    let k = u32::from_le_bytes(r[0..4].try_into().unwrap());
    let v = u128::from_le_bytes(r[4..20].try_into().unwrap());
    (k >> 1, k & 1 == 1, v)
}

pub fn encode(id: u32, outcome: bool, vec: u128) -> [u8; REC] {
    let mut r = [0u8; REC];
    r[0..4].copy_from_slice(&((id << 1) | outcome as u32).to_le_bytes());
    r[4..20].copy_from_slice(&vec.to_le_bytes());
    r
}

pub fn load(inputs: &[PathBuf]) -> Result<Data, String> {
    let mut d = Data::new();
    for r in load_raw(inputs)? {
        let (id, o, v) = decode(&r);
        d.entry(id).or_default().insert((o, v));
    }
    Ok(d)
}

/// Merges inputs into one file of distinct records, sorted. Returns the record count.
pub fn compact(out: &Path, inputs: &[PathBuf]) -> Result<usize, String> {
    let raw = load_raw(inputs)?;
    let tmp = out.with_extension("tmp");
    let mut buf = Vec::with_capacity(raw.len() * REC);
    for r in &raw {
        buf.extend_from_slice(r);
    }
    std::fs::write(&tmp, buf).map_err(|e| format!("{}: {}", tmp.display(), e))?;
    std::fs::rename(&tmp, out).map_err(|e| format!("{}: {}", out.display(), e))?;
    Ok(raw.len())
}
