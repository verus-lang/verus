#!/usr/bin/env python3
"""Reads a failed build log of a mutant build and appends to the disable list the mutation points
that cause the errors. Usage: fixbuild.py LOG MAP_DIR SOURCE_DIR DISABLE

MAP_DIR holds mutants.tsv and decisions.tsv (from `mcdc mutate`); SOURCE_DIR is the rewritten
source/ directory the log was built from. For each `error...` block with a `--> file:line:col`
location inside a mutated file, the candidate points are the `crate::__mut::f(ID` calls on that line
of the rewritten source (or the nearest line above, up to 15 lines). The error message narrows the
operator: a missing `Default` bound means drop-try / err-to-ok, a missing `Obo` bound means
const/index off-by-one, `?` on Option means drop-try, and so on. Entries are `file:line@op`
(`op` = guard disables the guard inserts of the decisions on that line) or `file:line`.
"""
import re, sys

LOG, MAP, SRC, DISABLE = sys.argv[1:5]
SRC = SRC.rstrip("/") + "/"

def tsv(path, skip):
    with open(path) as f:
        lines = f.read().splitlines()[skip:]
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, l.split("\t"))) for l in lines[1:] if l]

muts = {}
for r in tsv(MAP + "/mutants.tsv", 1):
    muts[int(r["id"])] = {"file": r["file"], "line": int(r["range"].split(":")[0]), "op": r["op"]}
decs = {}
for r in tsv(MAP + "/decisions.tsv", 0):
    decs[int(r["id"])] = {"file": r["file"], "line": int(r["line"])}

def ops_for(msg):
    if "Absent`" in msg:
        return {"container-insert-absent", "container-remove-absent"}
    if "MutUnwrapOr" in msg:
        return {"option-unwrap-or-default"}
    if "DoubleEndedIterator" in msg or "dyn Iterator" in msg or "Box<dyn" in msg or "dyn std::iter::Iterator" in msg:
        return {"container-iter-rev"}
    if "FnMut" in msg or "closure" in msg:
        return {"container-retain-negate"}
    if "Default` is not satisfied" in msg or "Default`" in msg:
        return {"drop-try", "err-to-ok"}
    if "Obo` is not satisfied" in msg or "Obo`" in msg:
        return {"const-plus1", "const-minus1", "index-plus1", "index-minus1"}
    if "`?` operator" in msg:
        return {"drop-try"}
    if "PartialOrd" in msg or "PartialEq" in msg or "can't compare" in msg:
        return {"rel-boundary", "eq-flip"}
    if "dropped while borrowed" in msg or "does not live long enough" in msg:
        return {"guard"}
    if "does not diverge" in msg:
        return {"delete-stmt", "skip-err-return", "FORWARD"}
    if "may be missing an `else`" in msg:
        return {"delete-stmt", "skip-err-return"}
    if "possibly-uninitialized" in msg or "used binding" in msg or "isn't initialized" in msg:
        return {"delete-stmt", "skip-err-return"}
    return None

log = open(LOG, errors="replace").read().splitlines()
blocks = []
cur = None
for line in log:
    if re.match(r"^error(\[E\d+\])?: ", line):
        cur = [line, None, []]
        blocks.append(cur)
    elif re.match(r"^(warning|error)", line):
        cur = None
    elif cur is not None:
        cur[2].append(line)
        if cur[1] is None:
            m = re.match(r"^\s*--> (\S+?):(\d+):(\d+)", line)
            if m:
                cur[1] = (m.group(1), int(m.group(2)))

files = {}
def src_lines(f):
    if f not in files:
        try:
            files[f] = open(SRC + f).read().splitlines()
        except OSError:
            files[f] = None
    return files[f]

add = set()
unresolved = []
for msg, loc, body in blocks:
    if loc is None:
        continue
    f, ln = loc
    lines = src_lines(f)
    if lines is None:
        unresolved.append((msg, loc))
        continue
    ops = ops_for(msg)
    found = None
    if re.search(r"E05(02|99|03|05|06)|borrowed", msg):
        # a boxed iterator (container-iter-rev) extends a borrow; look for it in the excerpt first
        txt = "\n".join(body)
        its = [int(x) for x in re.findall(r"crate::__mut::it\((\d+)", txt)]
        if its:
            for i in its:
                if i in muts:
                    add.add("%s:%d@%s" % (muts[i]["file"], muts[i]["line"], muts[i]["op"]))
            continue
    if re.search(r"E0(499|502|503|505|506|597|716)", msg):
        # a borrow error: a deleted or rewritten statement elsewhere changes a borrow; the lines named
        # in the excerpt (and the two lines after each, for a match arm and its body) are candidates
        bops = {"delete-stmt", "skip-err-return", "container-iter-rev", "option-get-none"}
        hit = False
        for L in sorted(set(int(x) for x in re.findall(r"^\s*(\d+) \|", "\n".join(body), re.M))):
            for k in range(L, L + 3):
                if 1 <= k <= len(lines):
                    for i in re.findall(r"crate::__mut::(?!guard)\w+\((\d+)", lines[k - 1]):
                        i = int(i)
                        if i in muts and muts[i]["op"] in bops:
                            add.add("%s:%d@%s" % (muts[i]["file"], muts[i]["line"], muts[i]["op"]))
                            hit = True
        # a skipped `return Err` between the borrow and its later use keeps the borrow alive
        nums = [int(x) for x in re.findall(r"^\s*(\d+) \|", "\n".join(body), re.M)]
        for k in range(min(nums or [ln]), max(nums or [ln]) + 1):
            if 1 <= k <= len(lines):
                for i in re.findall(r"crate::__mut::is\((\d+)\) \{ return", lines[k - 1]):
                    i = int(i)
                    if i in muts and muts[i]["op"] == "skip-err-return":
                        add.add("%s:%d@%s" % (muts[i]["file"], muts[i]["line"], muts[i]["op"]))
                        hit = True
        if hit:
            continue
    txt = "\n".join(body)
    if "E0308" in msg and "`()`" in txt:
        # a skipped `return Err` or a deleted statement made a block evaluate to `()`: every such point
        # in the lines the excerpt spans
        nums = [int(x) for x in re.findall(r"^\s*(\d+) \|", txt, re.M)] or [ln]
        hit = False
        for k in range(min(nums), max(nums) + 1):
            if 1 <= k <= len(lines):
                for i in re.findall(r"crate::__mut::(?!guard)\w+\((\d+)", lines[k - 1]):
                    i = int(i)
                    if i in muts and muts[i]["op"] in ("skip-err-return", "delete-stmt"):
                        add.add("%s:%d@%s" % (muts[i]["file"], muts[i]["line"], muts[i]["op"]))
                        hit = True
        if hit:
            continue
    rng = range(0, -16, -1) if ops and "FORWARD" in ops else range(0, 16)
    for back in rng:
        k = ln - back
        if k < 1 or k > len(lines):
            break
        ids = [int(x) for x in re.findall(r"crate::__mut::(?!guard)\w+\((\d+)", lines[k - 1])]
        cands = [muts[i] for i in ids if i in muts and (ops is None or muts[i]["op"] in ops)]
        if ops is None or "guard" in ops:
            gids = [int(x) for x in re.findall(r"crate::__mut::guard\((\d+)", lines[k - 1])]
            cands += [{"file": decs[i]["file"], "line": decs[i]["line"], "op": "guard"} for i in gids if i in decs]
        if cands:
            found = cands
            break
    if not found:
        # secondary: points shown anywhere in the error's source excerpt
        txt = "\n".join(body)
        ids = [int(x) for x in re.findall(r"crate::__mut::(?!guard)\w+\((\d+)", txt)]
        found = [muts[i] for i in ids if i in muts and (ops is None or muts[i]["op"] in ops)]
        gids = [int(x) for x in re.findall(r"crate::__mut::guard\((\d+)", txt)]
        found += [{"file": decs[i]["file"], "line": decs[i]["line"], "op": "guard"} for i in gids if i in decs]
        if not found:
            unresolved.append((msg, loc))
            add.add("%s:%d" % (f, ln))
            continue
    if ops is None and back == 0:
        # unknown error kind: disable every point on the line except the condition ones, unless only those
        for d in found:
            add.add("%s:%d@%s" % (d["file"], d["line"], d["op"]))
    else:
        # nearest candidate (last opened on that line is the innermost; take all matching)
        for d in found:
            add.add("%s:%d@%s" % (d["file"], d["line"], d["op"]))

old = set(l.strip() for l in open(DISABLE) if l.strip())
new = sorted(add - old)
with open(DISABLE, "a") as fo:
    for x in new:
        fo.write(x + "\n")
print("errors:", len(blocks), "new disable entries:", len(new), "unresolved:", len(unresolved))
for msg, loc in unresolved[:30]:
    print("  UNRESOLVED", loc, msg[:150])
