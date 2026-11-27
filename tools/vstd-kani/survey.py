#!/usr/bin/env python3
"""Survey Q2: classify vstd assume_specification sites by translatability into
executable Kani assertions.

Classification (heuristic, on the ensures/returns clause text of each site):
  translatable        : first-order over scalars / Option / Result / Bound;
                        no ghost view (@, Seq/Set/Map), no unbounded quantifier,
                        no higher-order trait obligation (call_ensures/obeys/spec fn ptr).
  needs-view          : mentions a ghost view (`@`) or Seq/Set/Map/spec_index whose
                        exec counterpart (Vec/clone, index) exists but must be built.
  not-translatable    : unbounded quantifier (forall/exists w/o bound), higher-order
                        (call_ensures / obeys_* / trait spec fn), interior mutability /
                        pointers / atomics / tracked, or no machine-checkable postcond.

Usage: python3 survey.py <std_specs_dir>
"""
import os, re, sys, glob

STD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "..", "source", "vstd", "std_specs")

# Files whose whole domain is inherently non-scalar / effectful.
FILE_HINT_NOT = {
    "atomic.rs", "smart_ptrs.rs", "manually_drop.rs", "maybe_uninit.rs",
    "hash.rs", "alloc.rs",
}

def clause_of(text, start):
    """Return the text from an assume_specification site to its terminating ';'."""
    depth = 0
    i = start
    while i < len(text):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ";" and depth == 0:
            return text[start:i]
        i += 1
    return text[start:start+400]

VIEW = re.compile(r"@|Seq<|Set<|Map<|\bspec_index\b|\.view\(\)|DeepView|->\s*Seq|->\s*Set|->\s*Map")
HIGHER = re.compile(r"call_ensures|call_requires|obeys_|cmp_spec|partial_cmp_spec|_spec\(&|<Self::")
QUANT = re.compile(r"\bforall\b|\bexists\b")
BOUNDEDQ = re.compile(r"forall\s*\|[^|]*\|\s*[^:]*::MIN|\.\.")  # crude: quantifier over a range
EFFECT = re.compile(r"\btracked\b|opens_invariants(?!\s+none)|PointsTo|PPtr|raw_ptr|Atomic")
SCALARISH = re.compile(r"None|Some|Ok|Err|Bound::|== |!= |<=|>=|returns|::MAX|::MIN|wrapping|checked|is_some|is_none|is_ok|is_err")

def classify(clause, fname):
    if EFFECT.search(clause):
        return "not"
    if HIGHER.search(clause):
        return "not"
    if QUANT.search(clause):
        # unbounded quantifier unless clearly ranged
        return "needs-view" if BOUNDEDQ.search(clause) else "not"
    if VIEW.search(clause):
        return "needs-view"
    if fname in FILE_HINT_NOT and not SCALARISH.search(clause):
        return "not"
    # No view, no quantifier, no higher-order: scalar/Option/Result/Bound first-order.
    return "translatable"

rows = []
examples = {"translatable": [], "needs-view": [], "not": []}
tot = {"translatable": 0, "needs-view": 0, "not": 0}

for path in sorted(glob.glob(os.path.join(STD, "*.rs"))):
    fname = os.path.basename(path)
    text = open(path).read()
    counts = {"translatable": 0, "needs-view": 0, "not": 0}
    for m in re.finditer(r"assume_specification", text):
        clause = clause_of(text, m.start())
        # site signature: first line after assume_specification
        sig = clause.split("\n")[0][len("assume_specification"):].strip()
        cls = classify(clause, fname)
        counts[cls] += 1
        tot[cls] += 1
        line = text[:m.start()].count("\n") + 1
        if len(examples[cls]) < 40:
            examples[cls].append(f"{fname}:{line}  {sig[:80]}")
    n = sum(counts.values())
    if n:
        rows.append((fname, n, counts["translatable"], counts["needs-view"], counts["not"]))

print(f"{'file':16} {'total':>5} {'transl':>7} {'needs-view':>11} {'not':>5}")
print("-" * 52)
for fname, n, t, v, x in sorted(rows, key=lambda r: -r[1]):
    print(f"{fname:16} {n:>5} {t:>7} {v:>11} {x:>5}")
print("-" * 52)
grand = sum(tot.values())
print(f"{'TOTAL':16} {grand:>5} {tot['translatable']:>7} {tot['needs-view']:>11} {tot['not']:>5}")
print()
print(f"translatable     : {tot['translatable']:3}  ({100*tot['translatable']/grand:.0f}%)")
print(f"needs-view       : {tot['needs-view']:3}  ({100*tot['needs-view']/grand:.0f}%)")
print(f"not-translatable : {tot['not']:3}  ({100*tot['not']/grand:.0f}%)")
print()
for k, label in [("translatable", "TRANSLATABLE"), ("needs-view", "NEEDS-VIEW"), ("not", "NOT-TRANSLATABLE")]:
    print(f"--- 3 representative {label} ---")
    for e in examples[k][:3]:
        print("  ", e)
