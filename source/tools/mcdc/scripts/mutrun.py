#!/usr/bin/env python3
"""Mutation pass over Verus test programs with the builds of tools/mcdc/scripts/build.sh.

Builds and map (options or environment variables):
  --build-a  MCDC_BUILD_A  verus binary of build A (`build.sh mcdc`): original semantics
  --build-b  MCDC_BUILD_B  verus binary of build B (`build.sh mutants`): MC/DC + mutant schemata
  --plain    MCDC_PLAIN    optional verus binary of an uninstrumented build, for the equivalence check
  --map      MCDC_MAP      map directory written by `mcdc mutate` (mutants.tsv, decisions.tsv)
  --mcdc     MCDC_BIN      mcdc binary (default: source/target-verus/release/mcdc)
  --data     MCDC_DATA     output directory (default: mutrun-data)
  --jobs N                 runs in flight (default 1)
  --timeout S              timeout of a baseline run (default 300); mutant runs use 10x the baseline time,
                           at least 20 s

A test is a .rs program with header lines:
  // expected: verifies | rejected: <message prefix> | crash
  // verus-args: <args>         (default: --crate-type=lib)
  // env: K=V ...
  // target: id=D atoms i,j (..=>T|F)   MC/DC targets (decision D of the manifest, atoms, side)

Commands:
  tests DIR...               inventory of the programs under DIR (recursive) -> DATA/tests.jsonl
  baseline [--only RE]       each test on build B with MUTANT_LOG and no mutant (reach, infection, path log),
                             and on build A and the plain build: verdicts must agree -> DATA/baseline.jsonl,
                             DATA/logs/<test>.gz
  mutants IDS OUT [--cap N]  for each mutant id in the file IDS: its infecting tests (from the baseline),
                             fastest first, until one kills it (at most N, default 4) -> OUT (jsonl) and
                             DATA/matrix.jsonl (one line per test and mutant run)
  report [RESULTS...]        status of every mutant (KILLED, SURVIVED, SURVIVED-CAPPED, NOT-INFECTED,
                             NOT-REACHED, NOT-RUN) and counts per class and operator
  index                      cone index from the static guard chains (mutants.tsv) and the baseline path
                             logs -> DATA/cone.jsonl, DATA/cone_atoms.jsonl
  check TEST.rs [--target D:I:O ...] [--cap N]
                             the test's in-cone mutants that its run reaches with the target guard on the
                             stack and infects, each run under its bitset; prints the survivors
  vet TEST.rs [--target ...] check 1 on build A: verdict matches `// expected:`, and a verified program with
                             a non-empty `fn main` compiles and its binary exits 0; check 2: `check`
  suite TREE --test T [--name F] --ids 1,2,..
                             rust_verify_test under each mutant: `vargo test --release -p rust_verify_test
                             --test T F` in TREE (build B's source/ dir) with MUTANT_BITSET; prints the tests
                             whose result differs from the run without a mutant

  rvt-baseline TREE [--only RE]
                             every non-ignored rust_verify_test test of TREE (build B's source/ dir, tests
                             built with `vargo test --release -p rust_verify_test --no-run`), one test per
                             process, with MUTANT_LOG and no mutant: result, time, reach and infection sets
                             -> DATA/rvt-baseline.jsonl
  rvt-mutants TREE IDS OUT [--tests RE] [--budget S]
                             for each mutant id in IDS: the passing tests that infect it in the baseline
                             (matching RE), fastest first, in batches, under MUTANT_ID, until one fails or
                             times out (killed), all pass (survived) or S seconds of runs are spent
                             (survived-capped) -> OUT (jsonl)
  rvt-report IDS OUT...      status of each mutant of IDS over the OUT files (killed in any of them counts),
                             counts per class and operator
  --wrap CMD                 command prefix of each test process (for example a global job limiter)

Kill oracle: a mutant run differs from the run of the same program on build B without a mutant in exit
status, verified/error counts, the set of error messages or the panic location, or (for a verified program
with a non-empty `fn main`) in the compiled binary's exit status or output. A hang or panic is not a kill when
the run without the mutant panics too.
"""
import argparse, collections, concurrent.futures as cf, gzip, json, os, re, shlex, shutil, subprocess, sys
import tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCE = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
O = None  # parsed options


def opt(name, env, default=None):
    return getattr(O, name) or os.environ.get(env) or default


def data(*p):
    d = opt("data", "MCDC_DATA", "mutrun-data")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, *p)


def build(which):
    v = {"A": opt("build_a", "MCDC_BUILD_A"), "B": opt("build_b", "MCDC_BUILD_B"),
         "plain": opt("plain", "MCDC_PLAIN")}[which]
    if which != "plain" and not v:
        sys.exit("missing build %s (--build-%s or MCDC_BUILD_%s)" % (which, which.lower(), which))
    return v


def map_dir():
    m = opt("map", "MCDC_MAP")
    if not m:
        sys.exit("missing --map / MCDC_MAP")
    return m


def tsv(path, skip):
    with open(path) as f:
        lines = f.read().splitlines()[skip:]
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, l.split("\t"))) for l in lines[1:] if l]


_muts = None


def mutants_map():
    """id -> row of mutants.tsv, with parsed line, guards [(d, o)], atom decision and index."""
    global _muts
    if _muts is None:
        _muts = {}
        for r in tsv(os.path.join(map_dir(), "mutants.tsv"), 1):
            r["id"], r["point"] = int(r["id"]), int(r["point"])
            r["line"] = int(r["range"].split(":")[0])
            r["guards"] = [] if r["guards"] == "-" else [tuple(map(int, g.split(":"))) for g in r["guards"].split(",")]
            r["atom"] = None if r["atom"] == "-" else int(r["atom"])
            r["atom_decision"] = int(r["decision"]) if r["atom"] is not None else None
            _muts[r["id"]] = r
    return _muts


# ---- running Verus ----

ERR = re.compile(r"^error(\[E\d+\])?: (.*)$")
SUM = re.compile(r"verification results:: (\d+) verified, (\d+) errors")
PANIC = re.compile(r"panicked at ([^\s:]+:\d+)")


def signature(rc, out):
    errs = sorted(set(ERR.match(l).group(2).strip() for l in out.splitlines() if ERR.match(l)))
    errs = [e for e in errs if not e.startswith("aborting due to")]
    summ = [list(map(int, x)) for x in SUM.findall(out)]
    timeout = rc in (124, 137, 143, -9, -15) and not summ
    return {"exit": rc, "sum": summ, "errs": errs, "panic": sorted(set(PANIC.findall(out))), "timeout": timeout}


def run_verus(t, verus, env_extra=None, timeout=300, compile_run=False):
    """Returns (signature, seconds, output)."""
    d = tempfile.mkdtemp(prefix="mutrun")
    env = dict(os.environ)
    for k in ("MUTANT_ID", "MUTANT_BITSET", "MUTANT_LOG", "MCDC_DIR"):
        env.pop(k, None)
    env.update(t.get("env", {}))
    env.update(env_extra or {})
    args = list(t["args"])
    if compile_run:
        args = [a for a in args if a != "--no-verify"] + ["--compile", "-o", os.path.join(d, "bin")]
    t0 = time.time()
    try:
        p = subprocess.run([verus, t["path"]] + args, cwd=d, env=env, capture_output=True, text=True,
                           errors="replace", timeout=timeout, start_new_session=True)
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        rc, out = 124, ""
    dt = time.time() - t0
    sig = signature(rc, out)
    if compile_run:
        b = os.path.join(d, "bin")
        sig["run"] = None
        if rc == 0 and os.path.exists(b):
            try:
                q = subprocess.run([b], cwd=d, capture_output=True, text=True, errors="replace", timeout=20)
                sig["run"] = [q.returncode, q.stdout[-2000:]]
            except subprocess.TimeoutExpired:
                sig["run"] = ["timeout", ""]
    shutil.rmtree(d, ignore_errors=True)
    return sig, dt, out


def has_main(src):
    return re.search(r"fn main\s*\(\s*\)\s*\{[^}]*\S", src) is not None


def verified(sig):
    return sig["exit"] == 0 and bool(sig["sum"]) and sig["sum"][-1][1] == 0


_bitset_lock = threading.Lock()


def bitset(mid):
    p = data("bitsets", "m%d.bin" % mid)
    with _bitset_lock:
        if not os.path.exists(p):
            os.makedirs(os.path.dirname(p), exist_ok=True)
            mcdc = opt("mcdc", "MCDC_BIN", os.path.join(SOURCE, "target-verus", "release", "mcdc"))
            subprocess.run([mcdc, "mutgen", "--map", os.path.join(map_dir(), "mutants.tsv"), "--id", str(mid),
                            "--out", p], check=True, capture_output=True)
    return p


def read_log(d):
    """Merges the per-process path-log files of MUTANT_LOG=d into sorted lines
    `R point hash`, `I id hash`, `S hash stack`, `D decision outcome depth`."""
    raw = set()
    for f in os.listdir(d):
        tag = {"reach": "R", "inf": "I", "stacks": "S", "dec": "D"}.get(f.rsplit(".", 1)[-1])
        if tag:
            for l in open(os.path.join(d, f)):
                if l.strip():
                    raw.add(tag + " " + l.strip())
    return sorted(raw)


def parse_log(lines):
    reach, inf, stacks = collections.defaultdict(set), collections.defaultdict(set), {"0": []}
    for l in lines:
        f = l.split()
        if f[0] == "R":
            reach[int(f[1])].add(f[2])
        elif f[0] == "I":
            inf[int(f[1])].add(f[2])
        elif f[0] == "S":
            stacks[f[1]] = [tuple(map(int, x.split(":"))) for x in f[2].split(",")] if len(f) > 2 else []
    return reach, inf, stacks


def logged_run(t, timeout):
    d = tempfile.mkdtemp(prefix="mutlog")
    sig, dt, out = run_verus(t, build("B"), {"MUTANT_LOG": d}, timeout)
    lines = read_log(d)
    shutil.rmtree(d, ignore_errors=True)
    return sig, dt, lines


def killed(base, sig):
    if base == sig:
        return False
    if base["panic"] and (sig["timeout"] or sig["panic"]):
        return False
    return True


def pool(fn, items):
    jobs = int(O.jobs or 1)
    with cf.ThreadPoolExecutor(jobs) as ex:
        for i, r in enumerate(ex.map(fn, items)):
            yield i, r


# ---- tests ----

def parse_test(path):
    src = open(path, errors="replace").read()
    h = lambda k: (re.search(r"^// %s:(.*)$" % k, src, re.M) or [None, None])[1]
    env = {}
    for kv in shlex.split(h("env") or ""):
        if "=" in kv:
            k, v = kv.split("=", 1)
            env[k] = v
    args = shlex.split(h("verus-args")) if h("verus-args") else ["--crate-type=lib"]
    return {"path": os.path.abspath(path), "args": args, "env": env, "expected": (h("expected") or "").strip(),
            "runtime": has_main(src) and "--crate-type=lib" not in args and "lib" not in args}


def cmd_tests(dirs):
    out = []
    for d in dirs:
        for root, _, fs in os.walk(d):
            for f in sorted(fs):
                if f.endswith(".rs"):
                    p = os.path.join(root, f)
                    t = parse_test(p)
                    t["name"] = os.path.relpath(p, d) if len(dirs) == 1 else p
                    out.append(t)
    with open(data("tests.jsonl"), "w") as f:
        for t in out:
            f.write(json.dumps(t) + "\n")
    print("%d tests -> %s" % (len(out), data("tests.jsonl")))


def tests():
    return {t["name"]: t for t in map(json.loads, open(data("tests.jsonl")))}


def key(name):
    return name.replace("/", "__") + ".gz"


def cmd_baseline(only):
    outp = data("baseline.jsonl")
    done = set(json.loads(l)["name"] for l in open(outp)) if os.path.exists(outp) else set()
    todo = [t for n, t in tests().items() if n not in done and (not only or re.search(only, n))]
    os.makedirs(data("logs"), exist_ok=True)
    lock = threading.Lock()

    def one(t):
        to = int(O.timeout or 300)
        sb, dtb, lines = logged_run(t, to)
        with gzip.open(data("logs", key(t["name"])), "wt") as g:
            g.write("\n".join(lines) + "\n")
        sa, dta, _ = run_verus(t, build("A"), {}, to)
        rec = {"name": t["name"], "sig": sb, "sig_a": sa, "b_eq_a": sa == sb, "secs": min(dta, dtb)}
        if build("plain"):
            sp, _, _ = run_verus(t, build("plain"), {}, to)
            rec["sig_plain"], rec["a_eq_plain"] = sp, sp == sa
        reach, inf, _ = parse_log(lines)
        rec["reach"], rec["inf"] = sorted(reach), sorted(inf)
        if t["runtime"] and verified(sb):
            rec["rt"] = run_verus(t, build("B"), {}, max(120, 10 * dtb), compile_run=True)[0]["run"]
            rec["rt_a"] = run_verus(t, build("A"), {}, max(120, 10 * dtb), compile_run=True)[0]["run"]
        rec["flaky"] = not rec["b_eq_a"] or rec.get("a_eq_plain") is False or rec.get("rt") != rec.get("rt_a")
        with lock:
            with open(outp, "a") as f:
                f.write(json.dumps(rec) + "\n")
        return rec

    n_eq = n = 0
    for i, r in pool(one, todo):
        n += 1
        n_eq += not r["flaky"]
        print("%d/%d %s %s" % (i + 1, len(todo), r["name"], "same" if not r["flaky"] else "DIFFERS"), flush=True)
    print("baseline: %d tests, %d with equal verdicts on A, B%s" % (n, n_eq, " and plain" if build("plain") else ""))


def baseline():
    return {r["name"]: r for r in map(json.loads, open(data("baseline.jsonl")))}


def cmd_mutants(idfile, outp, cap):
    bl, tl = baseline(), tests()
    inf_by = collections.defaultdict(list)
    for n, b in bl.items():
        if not b["flaky"]:
            for i in b["inf"]:
                inf_by[i].append(n)
    ids = [int(x) for x in open(idfile).read().split()]
    done = set(json.loads(l)["id"] for l in open(outp)) if os.path.exists(outp) else set()
    ids = [i for i in ids if i not in done]
    lock = threading.Lock()

    def one(mid):
        cands = sorted(inf_by.get(mid, []), key=lambda n: bl[n]["secs"])
        rec = {"id": mid, "infecting": len(cands), "ran": [], "killed_by": None}
        for n in cands[:cap]:
            t, b = tl[n], bl[n]
            env = {"MUTANT_BITSET": bitset(mid)}
            sig, _, _ = run_verus(t, build("B"), env, max(20, 10 * b["secs"]))
            k, how = killed(b["sig"], sig), "verdict"
            if not k and b.get("rt") is not None and sig == b["sig"]:
                rs = run_verus(t, build("B"), env, max(120, 10 * b["secs"]), compile_run=True)[0]
                k, how = rs["run"] != b["rt"], "runtime"
            rec["ran"].append(n)
            with lock:
                with open(data("matrix.jsonl"), "a") as f:
                    f.write(json.dumps({"test": n, "mid": mid, "killed": k}) + "\n")
            if k:
                rec.update(killed_by=n, how=how, sig=sig, base_sig=b["sig"])
                break
        with lock:
            with open(outp, "a") as f:
                f.write(json.dumps(rec) + "\n")
        return rec

    for i, r in pool(one, ids):
        print("%d/%d mutant %d: %s" % (i + 1, len(ids), r["id"], "killed by " + r["killed_by"] if r["killed_by"]
                                       else "survived (%d of %d infecting tests run)" % (len(r["ran"]), r["infecting"])),
              flush=True)


def cmd_report(results, cap):
    muts, bl = mutants_map(), baseline()
    reach, inf = set(), set()
    for b in bl.values():
        if not b["flaky"]:
            reach |= set(b["reach"])
            inf |= set(b["inf"])
    res = {}
    for p in results:
        for l in open(p):
            r = json.loads(l)
            res[r["id"]] = r
    st = {}
    for mid, m in muts.items():
        if mid in res and res[mid]["ran"]:
            r = res[mid]
            st[mid] = "KILLED" if r["killed_by"] else ("SURVIVED-CAPPED" if r["infecting"] > len(r["ran"]) else "SURVIVED")
        elif m["point"] not in reach:
            st[mid] = "NOT-REACHED"
        elif mid not in inf:
            st[mid] = "NOT-INFECTED"
        else:
            st[mid] = "NOT-RUN"
    with open(data("status.tsv"), "w") as f:
        f.write("id\tstatus\tfile\tline\tfn\top\tclass\n")
        for mid in sorted(st):
            m = muts[mid]
            f.write("%d\t%s\t%s\t%d\t%s\t%s\t%s\n" % (mid, st[mid], m["file"], m["line"], m["fn"], m["op"], m["class"]))
    names = ["KILLED", "SURVIVED", "SURVIVED-CAPPED", "NOT-INFECTED", "NOT-REACHED", "NOT-RUN"]
    for col in ("class", "op"):
        c = collections.defaultdict(collections.Counter)
        for mid, s in st.items():
            c[muts[mid][col]][s] += 1
        print("| %s | mutants | %s | score |" % (col, " | ".join(n.lower() for n in names)))
        print("|---|---:|%s---:|" % ("---:|" * len(names)))
        for k in sorted(c, key=lambda k: -sum(c[k].values())):
            run = c[k]["KILLED"] + c[k]["SURVIVED"] + c[k]["SURVIVED-CAPPED"]
            sc = "%d%%" % round(100 * c[k]["KILLED"] / run) if run else "-"
            print("| %s | %d | %s | %s |" % (k, sum(c[k].values()), " | ".join(str(c[k][n]) for n in names), sc))
        print()
    tot = collections.Counter(st.values())
    print("total: " + ", ".join("%s %d" % (n, tot[n]) for n in names) + " -> " + data("status.tsv"))


# ---- cone ----

def cmd_index():
    muts = mutants_map()
    by_point = collections.defaultdict(list)
    static, atoms = collections.defaultdict(set), collections.defaultdict(set)
    for m in muts.values():
        by_point[m["point"]].append(m["id"])
        for g in m["guards"]:
            static[g].add(m["id"])
        if m["atom"] is not None:
            atoms[(m["atom_decision"], m["atom"])].add(m["id"])
    dyn = collections.defaultdict(set)
    for p in sorted(os.listdir(data("logs"))):
        reach, _, stacks = parse_log([l.strip() for l in gzip.open(data("logs", p), "rt") if l.strip()])
        for pt, hs in reach.items():
            for h in hs:
                for g in stacks.get(h, []):
                    dyn[g].update(by_point.get(pt, ()))
    with open(data("cone.jsonl"), "w") as f:
        for k in sorted(set(static) | set(dyn)):
            f.write(json.dumps({"decision": k[0], "outcome": k[1], "static": sorted(static.get(k, ())),
                                "dynamic": sorted(dyn.get(k, ()))}) + "\n")
    with open(data("cone_atoms.jsonl"), "w") as f:
        for k in sorted(atoms):
            f.write(json.dumps({"decision": k[0], "atom": k[1], "mutants": sorted(atoms[k])}) + "\n")
    print("cone rows: %d, atom rows: %d" % (len(set(static) | set(dyn)), len(atoms)))


def load_cone():
    cone, atoms = {}, {}
    if os.path.exists(data("cone.jsonl")):
        for d in map(json.loads, open(data("cone.jsonl"))):
            cone[(d["decision"], d["outcome"])] = set(d["static"]) | set(d["dynamic"])
        for d in map(json.loads, open(data("cone_atoms.jsonl"))):
            atoms[(d["decision"], d["atom"])] = set(d["mutants"])
    else:  # static cone only
        for m in mutants_map().values():
            for g in m["guards"]:
                cone.setdefault(g, set()).add(m["id"])
            if m["atom"] is not None:
                atoms.setdefault((m["atom_decision"], m["atom"]), set()).add(m["id"])
    return cone, atoms


def sides(o):
    return [1, 0] if o == "*" else [int(o)]


def parse_targets(src):
    out = []
    for l in src.splitlines():
        m = re.match(r"^// (target|targets|gap):(.*)$", l)
        if not m:
            continue
        for part in re.split(r"\band\b|;", m.group(2)):
            ids = re.findall(r"id[= ](\d+)", part)
            am = re.search(r"atoms? ([\d, ]+)", part)
            alist = [int(x) for x in re.findall(r"\d+", am.group(1))] if am else [None]
            sm = re.search(r"=>\s*([TF])\)", part)
            side = "*" if not sm else ("1" if sm.group(1) == "T" else "0")
            out += [(int(d), a, side) for d in ids for a in alist]
    return out


def expand_atoms(targets):
    nat = {int(r["id"]): int(r["natoms"]) for r in tsv(os.path.join(map_dir(), "decisions.tsv"), 0)}
    out = []
    for d, a, s in targets:
        out += [(d, i, s) for i in range(nat.get(d, 1))] if a is None else [(d, a, s)]
    return sorted(set(out))


def check(t, targets, cap, quiet=False):
    muts = mutants_map()
    cone, atoms = load_cone()
    ic = {}
    for d, i, o in targets:
        for mid in atoms.get((d, i), ()):
            ic.setdefault(mid, (d, None))
        for s in sides(o):
            for mid in cone.get((d, s), ()):
                ic.setdefault(mid, (d, s))
    base, dt, lines = logged_run(t, int(O.timeout or 300))
    reach, inf, stacks = parse_log(lines)
    want = {(d, s) for d, i, o in targets for s in sides(o)}
    tdecs = {d for d, i, o in targets}
    on_path = lambda hs: any(set(stacks.get(h, [])) & want for h in hs)
    infected = []
    reached = 0
    for mid, (d, s) in sorted(ic.items()):
        m = muts[mid]
        hs = reach.get(m["point"], set())
        if s is None:
            ok_r, ok_i = bool(hs), bool(inf.get(mid))
        else:
            ok_r, ok_i = on_path(hs), on_path(inf.get(mid, ()))
            if not ok_r and hs and any(g[0] in tdecs for g in m["guards"]):
                ok_r, ok_i = True, bool(inf.get(mid))
        reached += ok_r
        if ok_r and ok_i:
            infected.append(mid)
    res = {"test": t["path"], "targets": targets, "base": base, "in_cone": len(ic), "reached": reached,
           "infected": len(infected), "ran": [], "killed": [], "survived": [], "capped": len(infected) > cap}
    for mid in infected[:cap]:
        sig, _, _ = run_verus(t, build("B"), {"MUTANT_BITSET": bitset(mid)}, max(60, 5 * dt))
        res["ran"].append(mid)
        (res["killed"] if killed(base, sig) else res["survived"]).append(mid)
    if not quiet:
        print("%s: in-cone %d, reached on the target path %d, infected %d, ran %d, killed %d, survived %d%s" % (
            os.path.basename(t["path"]), len(ic), reached, len(infected), len(res["ran"]), len(res["killed"]),
            len(res["survived"]), " (capped)" if res["capped"] else ""))
        for mid in res["survived"]:
            m = muts[mid]
            print("  SURVIVED #%d %s %s:%d %s\n      before: %s\n      after:  %s" % (
                mid, m["op"], m["file"], m["line"], m["fn"], m["orig"][:120], m["mutated"][:120]))
    return res


def verdict_ok(expected, sig):
    e = (expected or "").strip().lower()
    if e.startswith("verifies"):
        return verified(sig) and not sig["errs"]
    if e.startswith("rejected"):
        if verified(sig) or sig["panic"]:
            return False
        m = re.match(r"rejected:\s*([^(]{8,})", expected.strip(), re.I)
        return not m or any(m.group(1).strip()[:30].lower() in x.lower() for x in sig["errs"])
    if e.startswith("crash"):
        return bool(sig["panic"])
    return None


def cmd_vet(t, targets, cap):
    sig, dt, _ = run_verus(t, build("A"), {}, int(O.timeout or 300))
    g1 = verdict_ok(t["expected"], sig)
    print("check 1 (build A): exit %s, results %s, errors %s, panic %s; expected: %s -> %s" % (
        sig["exit"], sig["sum"], sig["errs"][:2], sig["panic"], t["expected"] or "(no header)",
        {True: "AGREES", False: "DISAGREES (a finding about Verus, or a wrong header)", None: "not checkable"}[g1]))
    if verified(sig) and t["runtime"]:
        run = run_verus(t, build("A"), {}, max(120, 10 * dt), compile_run=True)[0]["run"]
        ok = run is not None and run[0] == 0
        print("check 1 runtime: compiled binary %s -> %s" % (
            run, "AGREES" if ok else "DISAGREES: Verus verified the program but the binary fails"))
    print("check 2 (build B):")
    return check(t, targets, cap)


def cmd_suite(tree, test, name, ids):
    vt = int(O.timeout or 3600)

    def run(env):
        e = dict(os.environ)
        for k in ("MUTANT_ID", "MUTANT_BITSET", "MUTANT_LOG"):
            e.pop(k, None)
        e.update(env)
        cmd = ["vargo", "test", "--release", "-p", "rust_verify_test", "--test", test]
        cmd += ([name] if name else []) + ["--", "--test-threads=%d" % int(O.jobs or 1)]
        try:
            p = subprocess.run(cmd, cwd=tree, env=e, capture_output=True, text=True, errors="replace", timeout=vt)
            out = p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            out = ""
        return dict(re.findall(r"^test (\S+) \.\.\. (ok|FAILED|ignored)", out, re.M)), out

    base, out = run({})
    print("no mutant: %d tests, %d ok, %d failed" % (len(base), sum(v == "ok" for v in base.values()),
                                                   sum(v == "FAILED" for v in base.values())))
    for mid in ids:
        r, out = run({"MUTANT_BITSET": bitset(mid)})
        diff = sorted(n for n in set(base) | set(r) if base.get(n) != r.get(n))
        print("mutant %d: %s" % (mid, "killed by " + ", ".join("%s (%s -> %s)" % (n, base.get(n), r.get(n)) for n in diff)
                                 if diff else "survived (%d tests, same results)" % len(r)), flush=True)
        for l in [l for l in out.splitlines() if "panicked at" in l or l.startswith("assertion")][:2]:
            print("    " + l.strip()[:200])


# ---- rust_verify_test under mutants ----

def rvt_env(tree, extra):
    e = dict(os.environ)
    for k in ("MUTANT_ID", "MUTANT_BITSET", "MUTANT_LOG", "MCDC_DIR"):
        e.pop(k, None)
    e.update({"RUST_MIN_STACK": str(20 * 1024 * 1024), "RUSTC_BOOTSTRAP": "1", "VERUS_IN_VARGO": "1",
              "VARGO_TARGET_DIR": os.path.join(tree, "target-verus", "release"),
              "VERUS_Z3_PATH": e.get("VERUS_Z3_PATH") or os.path.join(tree, "z3")})
    e.update(extra)
    return e


def rvt_binaries(tree):
    """{test file stem: executable} from `cargo test --no-run` (built by vargo)."""
    p = subprocess.run(["vargo", "test", "--release", "-p", "rust_verify_test", "--no-run"], cwd=tree,
                       capture_output=True, text=True, errors="replace")
    out = {}
    for m in re.finditer(r"Executable tests/(\S+)\.rs \((\S+)\)", p.stdout + p.stderr):
        out[m.group(1)] = os.path.join(tree, m.group(2))
    if not out:
        sys.exit("no test executables found:\n" + (p.stdout + p.stderr)[-3000:])
    return out


def rvt_list(exe, ignored=False):
    p = subprocess.run([exe, "--list", "--format", "terse"] + (["--ignored"] if ignored else []),
                       capture_output=True, text=True, errors="replace",
                       cwd=os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(exe)))))
    return [l[:-len(": test")] for l in p.stdout.splitlines() if l.endswith(": test")]


def rvt_run(tree, exe, names, extra, timeout):
    """Runs the tests `names` of one executable in one process. Returns ({name: ok|FAILED}, rc, secs)."""
    cmd = shlex.split(O.wrap or "") + [exe, "--exact", "--test-threads=1"] + list(names)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=os.path.join(tree, "rust_verify_test"), env=rvt_env(tree, extra),
                           capture_output=True, text=True, errors="replace", timeout=timeout,
                           start_new_session=True)
        out, rc = p.stdout + p.stderr, p.returncode
    except subprocess.TimeoutExpired:
        out, rc = "", 124
    res = dict(re.findall(r"^test (\S+) \.\.\. (ok|FAILED|ignored)", out, re.M))
    return res, rc, time.time() - t0


def cmd_rvt_baseline(tree, only):
    outp = data("rvt-baseline.jsonl")
    done = set(json.loads(l)["name"] for l in open(outp)) if os.path.exists(outp) else set()
    todo = []
    for stem, exe in sorted(rvt_binaries(tree).items()):
        ign = set(rvt_list(exe, ignored=True))
        for n in rvt_list(exe):
            name = stem + "::" + n
            if n not in ign and name not in done and (not only or re.search(only, name)):
                todo.append((name, stem, exe, n))
    lock = threading.Lock()

    def one(item):
        name, stem, exe, n = item
        d = tempfile.mkdtemp(prefix="rvtlog")
        res, rc, dt = rvt_run(tree, exe, [n], {"MUTANT_LOG": d}, int(O.timeout or 1800))
        reach, inf, _ = parse_log(read_log(d))
        shutil.rmtree(d, ignore_errors=True)
        rec = {"name": name, "bin": stem, "exe": exe, "test": n, "result": res.get(n, "missing"), "rc": rc,
               "secs": round(dt, 2), "reach": sorted(reach), "inf": sorted(inf)}
        with lock:
            with open(outp, "a") as f:
                f.write(json.dumps(rec) + "\n")
        return rec

    for i, r in pool(one, todo):
        print("%d/%d %s %s %.1fs inf %d" % (i + 1, len(todo), r["name"], r["result"], r["secs"], len(r["inf"])),
              flush=True)


def rvt_baseline():
    return {r["name"]: r for r in map(json.loads, open(data("rvt-baseline.jsonl")))}


def cmd_rvt_mutants(tree, idfile, outp, tests_re, budget):
    bl = rvt_baseline()
    inf_by = collections.defaultdict(list)
    for n, b in bl.items():
        if b["result"] == "ok" and (not tests_re or re.search(tests_re, n)):
            for i in b["inf"]:
                inf_by[i].append(n)
    ids = [int(x) for x in open(idfile).read().split()]
    done = set(json.loads(l)["id"] for l in open(outp)) if os.path.exists(outp) else set()
    ids = [i for i in ids if i not in done]
    lock = threading.Lock()

    def one(mid):
        cands = sorted(inf_by.get(mid, []), key=lambda n: bl[n]["secs"])
        rec = {"id": mid, "infecting": len(cands), "ran": 0, "killed_by": None, "secs": 0.0}
        rest, size = list(cands), 1
        while rest and rec["killed_by"] is None and rec["secs"] <= budget:
            # one batch: up to `size` tests of the executable of the next candidate, in one process
            exe = bl[rest[0]]["exe"]
            batch = [n for n in rest if bl[n]["exe"] == exe][:size]
            rest = [n for n in rest if n not in set(batch)]
            to = max(60, 10 * sum(bl[n]["secs"] for n in batch))
            res, rc, dt = rvt_run(tree, exe, [bl[n]["test"] for n in batch], {"MUTANT_ID": str(mid)}, to)
            rec["secs"] += dt
            rec["ran"] += len(batch)
            for n in batch:
                r = res.get(bl[n]["test"])
                if r != "ok":
                    how = "FAILED" if r == "FAILED" else ("timeout" if rc in (124, 137, 143, -9, -15) else "crash")
                    rec.update(killed_by=n, how=how)
                    break
            size = min(32, size * 4)
        rec["secs"] = round(rec["secs"], 1)
        rec["capped"] = rec["killed_by"] is None and rec["ran"] < rec["infecting"]
        with lock:
            with open(outp, "a") as f:
                f.write(json.dumps(rec) + "\n")
        return rec

    for i, r in pool(one, ids):
        st = ("killed by %s (%s)" % (r["killed_by"], r["how"]) if r["killed_by"] else
              "survived-capped" if r["capped"] else "survived")
        print("%d/%d mutant %d: %s, %d of %d infecting tests, %.0fs" % (
            i + 1, len(ids), r["id"], st, r["ran"], r["infecting"], r["secs"]), flush=True)


def cmd_rvt_report(idfile, outs):
    muts, bl = mutants_map(), rvt_baseline()
    reach, inf = set(), set()
    for b in bl.values():
        if b["result"] == "ok":
            reach |= set(b["reach"])
            inf |= set(b["inf"])
    res = {}
    for p in outs:
        for l in open(p):
            r = json.loads(l)
            if r["id"] not in res or r["killed_by"]:
                res[r["id"]] = r
    ids = [int(x) for x in open(idfile).read().split()]
    st = {}
    for mid in ids:
        m = muts[mid]
        r = res.get(mid)
        if r and r["killed_by"]:
            st[mid] = "KILLED"
        elif m["point"] not in reach:
            st[mid] = "NOT-REACHED"
        elif mid not in inf:
            st[mid] = "NOT-INFECTED"
        elif r is None:
            st[mid] = "NOT-RUN"
        else:
            st[mid] = "SURVIVED-CAPPED" if r.get("capped") else "SURVIVED"
    names = ["KILLED", "SURVIVED", "SURVIVED-CAPPED", "NOT-INFECTED", "NOT-REACHED", "NOT-RUN"]
    for col in ("class", "op"):
        c = collections.defaultdict(collections.Counter)
        for mid, s in st.items():
            c[muts[mid][col]][s] += 1
        print("| %s | mutants | %s |" % (col, " | ".join(n.lower() for n in names)))
        print("|---|---:|%s" % ("---:|" * len(names)))
        for k in sorted(c, key=lambda k: -sum(c[k].values())):
            print("| %s | %d | %s |" % (k, sum(c[k].values()), " | ".join(str(c[k][n]) for n in names)))
        print()
    tot = collections.Counter(st.values())
    print("total %d: " % len(st) + ", ".join("%s %d" % (n, tot[n]) for n in names))


def main():
    global O
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for o in ("build-a", "build-b", "plain", "map", "mcdc", "data", "jobs", "timeout", "wrap"):
        ap.add_argument("--" + o)
    ap.add_argument("cmd")
    ap.add_argument("rest", nargs=argparse.REMAINDER)
    O = ap.parse_args()
    a = O.rest

    def flag(name, default=None, multi=False):
        vals = [a[i + 1] for i, x in enumerate(a) if x == name and i + 1 < len(a)]
        return vals if multi else (vals[0] if vals else default)

    if O.cmd == "tests":
        cmd_tests(a)
    elif O.cmd == "baseline":
        cmd_baseline(flag("--only"))
    elif O.cmd == "mutants":
        cmd_mutants(a[0], a[1], int(flag("--cap", 4)))
    elif O.cmd == "report":
        cmd_report([x for x in a if not x.startswith("--")], None)
    elif O.cmd == "index":
        cmd_index()
    elif O.cmd in ("check", "vet"):
        t = parse_test(a[0])
        targets = [(int(d), int(i), o) for d, i, o in (x.split(":") for x in flag("--target", multi=True))]
        if not targets:
            targets = expand_atoms(parse_targets(open(a[0], errors="replace").read()))
        if not targets:
            sys.exit("no target: pass --target D:I:O or a `// target:` header")
        cap = int(flag("--cap", 40))
        res = check(t, targets, cap) if O.cmd == "check" else cmd_vet(t, targets, cap)
        if flag("--json"):
            json.dump(res, open(flag("--json"), "w"))
    elif O.cmd == "suite":
        cmd_suite(os.path.abspath(a[0]), flag("--test"), flag("--name"),
                  [int(x) for x in flag("--ids", "").split(",") if x])
    elif O.cmd == "rvt-baseline":
        cmd_rvt_baseline(os.path.abspath(a[0]), flag("--only"))
    elif O.cmd == "rvt-mutants":
        cmd_rvt_mutants(os.path.abspath(a[0]), a[1], a[2], flag("--tests"), float(flag("--budget", 1e18)))
    elif O.cmd == "rvt-report":
        cmd_rvt_report(a[0], [x for x in a[1:] if not x.startswith("--")])
    else:
        sys.exit("unknown command %s; see --help" % O.cmd)


if __name__ == "__main__":
    main()
