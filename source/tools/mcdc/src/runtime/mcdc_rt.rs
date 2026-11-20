// MC/DC runtime. `mcdc instrument` writes this file as src/__mcdc_rt.rs next to each instrumented
// crate root and appends to the root
//   #[allow(dead_code, unused)] mod __mcdc { include!("__mcdc_rt.rs"); }
// Every instrumented decision calls `rec(id, vec, outcome)` once per completed evaluation.
// `vec` packs 2 bits per atom i at bits 2i (evaluated) and 2i+1 (value).
// Records are deduplicated per process in sharded hash sets. New records are appended to
// $MCDC_DIR/<crate>-<pid>-<nonce>.mcdc as 20-byte little-endian records:
//   u32 (id << 1 | outcome), u128 vec.
// Flushes happen every 4096 new records, at most every 2 s on a new record, and at exit (atexit).
// If MCDC_DIR is unset, `rec` returns after one OnceLock read.
// This file must compile under editions 2018, 2021 and 2024 (air and builtin_macros use 2018).

use std::collections::HashSet;
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

const SHARDS: usize = 64;

struct Shard {
    seen: HashSet<(u32, u128)>,
    pending: Vec<(u32, u128)>,
}

struct State {
    path: Option<std::path::PathBuf>,
    shards: Vec<Mutex<Shard>>,
    new_count: AtomicU64,
    flush_lock: Mutex<Instant>,
}

static STATE: OnceLock<State> = OnceLock::new();
static NONCE: u8 = 0;

unsafe extern "C" {
    fn atexit(cb: extern "C" fn()) -> i32;
}

extern "C" fn at_exit() {
    let _ = std::panic::catch_unwind(|| flush(true));
}

fn init() -> State {
    let path = match std::env::var_os("MCDC_DIR") {
        Some(d) if !d.is_empty() => {
            let d = std::path::PathBuf::from(d);
            let _ = std::fs::create_dir_all(&d);
            let krate = option_env!("CARGO_CRATE_NAME").unwrap_or("unknown");
            let nonce = (&NONCE as *const u8 as usize) as u64
                ^ std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|x| x.as_nanos() as u64)
                    .unwrap_or(0);
            Some(d.join(format!("{}-{}-{:016x}.mcdc", krate, std::process::id(), nonce)))
        }
        _ => None,
    };
    if path.is_some() {
        unsafe {
            atexit(at_exit);
        }
    }
    State {
        path,
        shards: (0..SHARDS)
            .map(|_| Mutex::new(Shard { seen: HashSet::new(), pending: Vec::new() }))
            .collect(),
        new_count: AtomicU64::new(0),
        flush_lock: Mutex::new(Instant::now()),
    }
}

#[inline]
pub fn rec(id: u32, vec: u128, outcome: bool) {
    let st = STATE.get_or_init(init);
    if st.path.is_none() {
        return;
    }
    let key = (id << 1) | (outcome as u32);
    let h = (id as usize).wrapping_mul(0x9E37_79B9) ^ (vec as usize) ^ ((vec >> 64) as usize);
    let inserted = {
        let mut sh = match st.shards[h % SHARDS].lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        if sh.seen.insert((key, vec)) {
            sh.pending.push((key, vec));
            true
        } else {
            false
        }
    };
    if inserted {
        let n = st.new_count.fetch_add(1, Ordering::Relaxed) + 1;
        if n % 4096 == 0 {
            flush(false);
        } else if let Ok(last) = st.flush_lock.try_lock() {
            let due = last.elapsed().as_secs() >= 2;
            drop(last);
            if due {
                flush(false);
            }
        }
    }
}

fn flush(at_exit: bool) {
    let Some(st) = STATE.get() else { return };
    let Some(path) = &st.path else { return };
    let mut guard = if at_exit {
        // another thread may hold the lock forever at exit; try for ~200 ms
        let mut g = None;
        for _ in 0..200 {
            if let Ok(x) = st.flush_lock.try_lock() {
                g = Some(x);
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        match g {
            Some(g) => g,
            None => return,
        }
    } else {
        match st.flush_lock.try_lock() {
            Ok(g) => g,
            Err(_) => return,
        }
    };
    let mut buf: Vec<u8> = Vec::new();
    for s in st.shards.iter() {
        let taken = if at_exit {
            let mut got = None;
            for _ in 0..50 {
                if let Ok(mut g) = s.try_lock() {
                    got = Some(std::mem::take(&mut g.pending));
                    break;
                }
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            got.unwrap_or_default()
        } else {
            match s.lock() {
                Ok(mut g) => std::mem::take(&mut g.pending),
                Err(p) => std::mem::take(&mut p.into_inner().pending),
            }
        };
        for (k, v) in taken {
            buf.extend_from_slice(&k.to_le_bytes());
            buf.extend_from_slice(&v.to_le_bytes());
        }
    }
    if !buf.is_empty() {
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = f.write_all(&buf);
        }
    }
    *guard = Instant::now();
}

/// Let-chain decisions (`if A && let P = e && B`): bit 127 marks that evaluation started. For a false
/// outcome where no atom recorded false, the failing atom is the first one without a record (a `let`
/// whose pattern did not match), which is set to evaluated-false.
pub fn rec_chain(id: u32, vec: u128, outcome: bool) {
    if vec >> 127 == 0 {
        return;
    }
    let mut v = vec & !(1u128 << 127);
    if !outcome {
        let mut any_false = false;
        let mut first_unrec = None;
        for i in 0..63 {
            let b = (v >> (2 * i)) & 3;
            if b == 1 {
                any_false = true;
            }
            if b == 0 && first_unrec.is_none() {
                first_unrec = Some(i);
            }
        }
        if !any_false {
            if let Some(i) = first_unrec {
                v |= 1u128 << (2 * i);
            }
        }
    }
    rec(id, v, outcome);
}

// Let-chain decisions in match guards (`P if A && let Q = e && B => ..`). A guard cannot be wrapped
// in a block that declares the vector, so the vector of the pending evaluation is kept per thread:
// `g_start` begins an evaluation (ending a pending one of the same decision as false), `g_atom`
// records atom i, and `g_end` (at the start of every arm body of the match) ends the pending
// evaluation, with outcome true in the guarded arm and false in the others.
thread_local! {
    static GUARDS: std::cell::RefCell<Vec<(u32, u128)>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub fn g_start(id: u32) {
    g_end(id, false);
    GUARDS.with(|g| g.borrow_mut().push((id, 1u128 << 127)));
}

pub fn g_atom(id: u32, i: u32, v: bool) {
    GUARDS.with(|g| {
        if let Some(e) = g.borrow_mut().iter_mut().rev().find(|e| e.0 == id) {
            e.1 |= if v { 3u128 << (2 * i) } else { 1u128 << (2 * i) };
        }
    });
}

pub fn g_end(id: u32, outcome: bool) {
    let v = GUARDS.with(|g| {
        let mut g = g.borrow_mut();
        let k = g.iter().rposition(|e| e.0 == id)?;
        Some(g.remove(k).1)
    });
    if let Some(v) = v {
        rec_chain(id, v, outcome);
    }
}
