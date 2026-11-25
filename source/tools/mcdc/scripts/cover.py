#!/usr/bin/env python3
"""Smallest set of tests that keeps every kill: weighted set cover over a kill matrix.

Usage: cover.py MATRIX.jsonl [--weights TESTS.jsonl] [--free NAMES.txt] [--out SELECTION.json]

MATRIX.jsonl  one line per (test, mutant) run: {"test": NAME, "mid": ID, "killed": BOOL, "kind": K}
              (`mutrun.py mutants` writes it as DATA/matrix.jsonl). `kind` is optional: "on-target" for a
              mutant in the cone of the test's own target (gain 1.0); any other kind gains 0.85.
TESTS.jsonl   optional weights: {"name": NAME, "secs": S, "bytes": B} (for example mutrun's baseline.jsonl
              with "secs"); weight = 0.5 + secs + bytes / 2000 (defaults: secs 1, bytes 2000).
NAMES.txt     tests already in the suite (one name per line): weight 0, all taken first; a mutant they
              kill needs no new test.

Greedy picks the largest gain / weight until every killed mutant is covered, then a redundancy pass drops,
heaviest first, any chosen test whose kills the other chosen tests and the free tests cover. A lower bound
on the number of tests is printed: tests that are the only killer of some mutant, plus a set of mutants
with pairwise disjoint killer sets among the rest.
"""
import collections, json, sys


def main():
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)
    flag = lambda n: a[a.index(n) + 1] if n in a else None
    kills = collections.defaultdict(dict)
    for l in open(a[0]):
        p = json.loads(l)
        if p["killed"]:
            kills[p["test"]][p["mid"]] = p.get("kind", "")
    meta = {}
    if flag("--weights"):
        for l in open(flag("--weights")):
            r = json.loads(l)
            meta[r["name"]] = r
    free = set()
    if flag("--free"):
        free = set(l.strip() for l in open(flag("--free")) if l.strip())

    def weight(n):
        m = meta.get(n, {})
        return 0.5 + (m.get("secs") or 1.0) + (m.get("bytes") or 2000) / 2000.0

    def gain(n, unc):
        return sum(1.0 if k == "on-target" else 0.85 for m, k in kills[n].items() if m in unc)

    U = set(m for k in kills.values() for m in k)
    U_free = set(m for n in free if n in kills for m in kills[n])
    target = U - U_free
    cands = [n for n in kills if n not in free]
    unc, chosen = set(target), []
    while unc:
        best = max(cands, key=lambda n: (gain(n, unc) / weight(n), -weight(n), n))
        if gain(best, unc) == 0:
            break
        chosen.append(best)
        unc -= set(kills[best])
    keep = list(chosen)
    for n in sorted(chosen, key=lambda n: -weight(n)):
        others = set(U_free)
        for o in keep:
            if o != n:
                others |= set(kills[o])
        if set(kills[n]) & target <= others:
            keep.remove(n)
    killers = collections.defaultdict(set)
    for n in cands:
        for m in kills[n]:
            if m in target:
                killers[m].add(n)
    ess = {next(iter(v)) for v in killers.values() if len(v) == 1}
    cov_ess = set(m for n in ess for m in kills[n])
    used, pack = set(), []
    for m in sorted((m for m in target if m not in cov_ess), key=lambda m: len(killers[m])):
        if not (killers[m] & used) and not (killers[m] & ess):
            pack.append(m)
            used |= killers[m]
    final = set(U_free)
    for n in keep:
        final |= set(kills[n])
    assert final == U, (len(final), len(U))
    res = {"killed": len(U), "killed_by_free": len(U_free), "target": len(target), "greedy": len(chosen),
           "kept": sorted(keep), "lower_bound": len(ess) + len(pack), "essential": sorted(ess),
           "weight": round(sum(weight(n) for n in keep), 2)}
    if flag("--out"):
        json.dump(res, open(flag("--out"), "w"), indent=1)
    print("mutants killed %d; by the free tests %d; to cover %d; greedy %d tests, kept %d after the redundancy "
          "pass; lower bound %d (%d essential); weight %.2f" % (len(U), len(U_free), len(target), len(chosen),
                                                              len(keep), res["lower_bound"], len(ess), res["weight"]))


if __name__ == "__main__":
    main()
