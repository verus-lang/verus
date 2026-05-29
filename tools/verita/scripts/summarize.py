#!/usr/bin/env python3

import argparse
import json
import glob
import re
from pathlib import Path


def load_results(directory):
    """Load all JSON files from a directory and return dict keyed by filename stem."""
    results = {}
    for filename in sorted(glob.glob(f'{directory}/*.json')):
        stem = Path(filename).stem
        with open(filename) as f:
            data = json.load(f)
        runner = data.get("runner", {})
        run_config = runner.get("run_configuration", {})
        vr = data.get("verification-results", {})
        times = data.get("times-ms", {})

        functions = []
        smt = times.get("smt", {})
        for module in smt.get("smt-run-module-times", []):
            for fn in module.get("function-breakdown", []):
                functions.append({
                    "name": fn.get("function", ""),
                    "time_ms": fn.get("time"),
                    "time_us": fn.get("time-micros"),
                    "success": fn.get("success"),
                })

        # Determine which specific crate root this JSON represents.
        # When a project has multiple crate roots, main.rs names each output file
        # "<project-name>-<suffix>.json" where suffix is the parent directory
        # (slashes → dashes) or, for bare names like "pmemlog", the target name
        # itself.  We reverse that to recover the original crate root path.
        crate_roots = run_config.get("crate_roots", [])
        proj_name = run_config.get("name", stem)
        crate_root = None
        if len(crate_roots) > 1:
            if stem != proj_name and stem.startswith(proj_name + "-"):
                suffix = stem[len(proj_name) + 1:]  # e.g. "capybaraKV" or "pmemlog"
                for cr in crate_roots:
                    parent = str(Path(cr).parent).replace("/", "-")
                    if parent == suffix:
                        crate_root = cr
                        break
                if crate_root is None:
                    # Try matching against the target name/stem itself
                    # (for bare targets like "pmemlog" with no parent dir)
                    for cr in crate_roots:
                        if Path(cr).stem == suffix or cr == suffix:
                            crate_root = cr
                            break
                if crate_root is None:
                    crate_root = suffix  # fallback: show the raw suffix
            else:
                # Stem matched the project name exactly
                crate_root = crate_roots[0] if len(crate_roots) == 1 else stem

        results[stem] = {
            "name": proj_name,
            "crate_root": crate_root,
            "success": runner.get("success"),
            "stderr": runner.get("stderr", ""),
            "verified": vr.get("verified") if vr else None,
            "errors": vr.get("errors") if vr else None,
            "total_ms": times.get("total"),
            "functions": functions,
        }
    return results


def fmt_time(ms):
    if ms is None:
        return "N/A"
    return f"{ms / 1000:.2f} s"


def fmt_status(success):
    if success is None:
        return "ERROR"
    return "OK" if success else "FAILED"


def fmt_int_or_dash(val):
    if val is None:
        return "-"
    return str(val)


def sorted_entries(results):
    """Return (stem, result) pairs sorted by (name, stem)."""
    return sorted(results.items(), key=lambda kv: (kv[1]["name"], kv[0]))


# ── Single-run output ──────────────────────────────────────────────────────────

def print_single_summary(results):
    entries = sorted_entries(results)

    show_crate = any(r["crate_root"] is not None for _, r in entries)

    proj_col = max(len("Project"), max(len(r["name"]) for _, r in entries)) + 2
    if show_crate:
        cr_col = max(len("Crate Root"), max(len(r["crate_root"] or "") for _, r in entries)) + 2
        header = (
            f"{'Project':<{proj_col}} {'Crate Root':<{cr_col}}"
            f" {'Status':<8}  {'Verified':>10}   {'Errors':>6}   {'Total Time':>10}"
        )
    else:
        header = f"{'Project':<{proj_col}} {'Status':<8}  {'Verified':>10}   {'Errors':>6}   {'Total Time':>10}"
    sep = "-" * len(header)

    print("=== Project Summary ===")
    print()
    print(header)
    print(sep)

    for _, r in entries:
        status = fmt_status(r["success"])
        verified = fmt_int_or_dash(r["verified"])
        errors = fmt_int_or_dash(r["errors"])
        total = fmt_time(r["total_ms"])
        if show_crate:
            cr = r["crate_root"] or ""
            print(f"{r['name']:<{proj_col}} {cr:<{cr_col}} {status:<8}  {verified:>10}   {errors:>6}   {total:>10}")
        else:
            print(f"{r['name']:<{proj_col}} {status:<8}  {verified:>10}   {errors:>6}   {total:>10}")

    print()


def print_top5_single(results):
    entries = sorted_entries(results)

    print("=== Top 5 Slowest Functions ===")
    print()

    for _, r in entries:
        label = r['name']
        if r['crate_root']:
            label += f" ({r['crate_root']})"
        print(f"--- {label} ---")
        fns = r["functions"]
        if not fns:
            print("  (no timing data available)")
        else:
            top5 = sorted(fns, key=lambda f: f["time_ms"] or 0, reverse=True)[:5]
            for i, fn in enumerate(top5, 1):
                t = fn["time_ms"]
                tstr = f"{t:>6} ms" if t is not None else "    N/A"
                print(f"  {i}.  {tstr}   {fn['name']}")
        print()


# ── Single-run Markdown output ────────────────────────────────────────────────

def print_single_summary_md(results):
    entries = sorted_entries(results)
    show_crate = any(r["crate_root"] is not None for _, r in entries)

    if show_crate:
        print("| Project | Crate Root | Status | Verified | Errors | Total Time |")
        print("|---------|------------|--------|----------|--------|------------|")
    else:
        print("| Project | Status | Verified | Errors | Total Time |")
        print("|---------|--------|----------|--------|------------|")

    for _, r in entries:
        status = fmt_status(r["success"])
        verified = fmt_int_or_dash(r["verified"])
        errors = fmt_int_or_dash(r["errors"])
        total = fmt_time(r["total_ms"])
        if show_crate:
            cr = r["crate_root"] or ""
            print(f"| {r['name']} | {cr} | {status} | {verified} | {errors} | {total} |")
        else:
            print(f"| {r['name']} | {status} | {verified} | {errors} | {total} |")

    print()


def print_top5_single_md(results):
    entries = sorted_entries(results)

    print("### Top 5 Slowest Functions")
    print()

    for _, r in entries:
        label = r['name']
        if r['crate_root']:
            label += f" ({r['crate_root']})"
        print(f"**{label}**")
        print()
        fns = r["functions"]
        if not fns:
            print("_(no timing data available)_")
            print()
            continue
        print("| # | Time | Function |")
        print("|---|------|----------|")
        top5 = sorted(fns, key=lambda f: f["time_ms"] or 0, reverse=True)[:5]
        for i, fn in enumerate(top5, 1):
            t = fn["time_ms"]
            tstr = f"{t} ms" if t is not None else "N/A"
            print(f"| {i} | {tstr} | `{fn['name']}` |")
        print()


# ── Error summary (Markdown only) ─────────────────────────────────────────────

def _project_label(r):
    """Return a display label for a result entry (project name + crate root)."""
    label = r["name"]
    if r["crate_root"]:
        label += f" ({r['crate_root']})"
    return label


_ANSI_ESCAPE_RE = re.compile(r'\x1b\[[0-9;]*m')


def _strip_ansi(text):
    """Remove ANSI escape sequences from text."""
    return _ANSI_ESCAPE_RE.sub('', text)


def print_error_summary_md(results):
    """Print a foldable error summary for any failed projects (Markdown mode)."""
    entries = sorted_entries(results)
    failed = [(stem, r) for stem, r in entries if r["success"] is not True]
    if not failed:
        return

    print("### Error Summary")
    print()

    for _, r in failed:
        label = _project_label(r)
        stderr = _strip_ansi((r.get("stderr") or "")).strip()
        if not stderr:
            stderr = "_(no stderr captured)_"

        print(f"<details>")
        print(f"<summary>{label}</summary>")
        print()
        print("```")
        print(stderr)
        print("```")
        print()
        print("</details>")
        print()


# ── Two-run comparison output ──────────────────────────────────────────────────

def _signed(n):
    return f"+{n}" if n >= 0 else str(n)


def _signed_f(f, decimals=2):
    return f"+{f:.{decimals}f}" if f >= 0 else f"{f:.{decimals}f}"


def _cmp_int(old, new):
    """Return comparison string for an integer metric (verified/errors)."""
    ov = fmt_int_or_dash(old)
    nv = fmt_int_or_dash(new)
    if old is not None and new is not None:
        delta = new - old
        return f"{ov} → {nv} ({_signed(delta)})"
    return f"{ov} → {nv}"


def _cmp_time(old_ms, new_ms):
    """Return comparison string for a time metric."""
    if old_ms is not None and new_ms is not None:
        old_s = old_ms / 1000
        new_s = new_ms / 1000
        delta_s = new_s - old_s
        pct = (delta_s / old_s) * 100 if old_s != 0 else 0
        return f"{old_s:.2f} → {new_s:.2f} s ({_signed_f(delta_s)} s, {_signed_f(pct, 1)}%)"
    return f"{fmt_time(old_ms)} → {fmt_time(new_ms)}"


def print_comparison_summary(old_results, new_results):
    all_stems = sorted(
        set(old_results.keys()) | set(new_results.keys()),
        key=lambda s: ((old_results.get(s) or new_results.get(s))["name"], s),
    )

    def get_name(stem):
        return (old_results.get(stem) or new_results.get(stem))["name"]

    # Build rows first to compute column widths
    rows = []
    for stem in all_stems:
        old = old_results.get(stem)
        new = new_results.get(stem)
        name = get_name(stem)
        crate_root = (old or new)["crate_root"]

        if old is None:
            status_str = "(new)"
            ver_str = fmt_int_or_dash(new["verified"])
            err_str = fmt_int_or_dash(new["errors"])
            time_str = fmt_time(new["total_ms"])
        elif new is None:
            status_str = "(removed)"
            ver_str = fmt_int_or_dash(old["verified"])
            err_str = fmt_int_or_dash(old["errors"])
            time_str = fmt_time(old["total_ms"])
        else:
            old_st = fmt_status(old["success"])
            new_st = fmt_status(new["success"])
            status_str = old_st if old_st == new_st else f"{old_st} → {new_st}"
            ver_str = _cmp_int(old["verified"], new["verified"])
            err_str = _cmp_int(old["errors"], new["errors"])
            time_str = _cmp_time(old["total_ms"], new["total_ms"])

        rows.append((name, crate_root, status_str, ver_str, err_str, time_str))

    show_crate = any(r[1] is not None for r in rows)

    # Column widths
    proj_col  = max(len("Project"),  max(len(r[0]) for r in rows)) + 2
    if show_crate:
        cr_col = max(len("Crate Root"), max(len(r[1] or "") for r in rows)) + 2
    stat_col  = max(len("Status"),   max(len(r[2]) for r in rows)) + 2
    ver_col   = max(len("Verified"), max(len(r[3]) for r in rows))
    err_col   = max(len("Errors"),   max(len(r[4]) for r in rows))
    time_col  = max(len("Total Time"), max(len(r[5]) for r in rows))

    if show_crate:
        header = (
            f"{'Project':<{proj_col}} {'Crate Root':<{cr_col}} {'Status':<{stat_col}}"
            f" {'Verified':>{ver_col}}  {'Errors':>{err_col}}  {'Total Time':>{time_col}}"
        )
    else:
        header = (
            f"{'Project':<{proj_col}} {'Status':<{stat_col}}"
            f" {'Verified':>{ver_col}}  {'Errors':>{err_col}}  {'Total Time':>{time_col}}"
        )
    sep = "-" * len(header)

    print("=== Project Summary (old → new) ===")
    print()
    print(header)
    print(sep)

    for name, crate_root, status_str, ver_str, err_str, time_str in rows:
        if show_crate:
            cr = crate_root or ""
            print(
                f"{name:<{proj_col}} {cr:<{cr_col}} {status_str:<{stat_col}}"
                f" {ver_str:>{ver_col}}  {err_str:>{err_col}}  {time_str:>{time_col}}"
            )
        else:
            print(
                f"{name:<{proj_col}} {status_str:<{stat_col}}"
                f" {ver_str:>{ver_col}}  {err_str:>{err_col}}  {time_str:>{time_col}}"
            )

    print()


def print_top5_comparison(old_results, new_results):
    all_stems = sorted(
        set(old_results.keys()) | set(new_results.keys()),
        key=lambda s: ((old_results.get(s) or new_results.get(s))["name"], s),
    )

    print("=== Top 5 Slowest Functions ===")
    print()

    for stem in all_stems:
        old = old_results.get(stem)
        new = new_results.get(stem)
        r = old or new
        name = r["name"]
        label = name
        if r["crate_root"]:
            label += f" ({r['crate_root']})"
        print(f"--- {label} ---")

        # Collect all functions from each side
        old_fns_map = {fn["name"]: fn for fn in old["functions"]} if old else {}
        new_fns_map = {fn["name"]: fn for fn in new["functions"]} if new else {}

        old_top5 = sorted(old["functions"], key=lambda f: f["time_ms"] or 0, reverse=True)[:5] if old else []
        new_top5 = sorted(new["functions"], key=lambda f: f["time_ms"] or 0, reverse=True)[:5] if new else []

        # Union of top-5 names from each side, deduped, old-first ordering
        seen = set()
        union_names = []
        for fn in old_top5 + new_top5:
            if fn["name"] not in seen:
                seen.add(fn["name"])
                union_names.append(fn["name"])

        if not union_names:
            print("  (no timing data available)")
            print()
            continue

        fn_col  = max(len("Function"),  max(len(n) for n in union_names)) + 2
        old_col = max(len("Old"),  max(
            len(f"{old_fns_map[n]['time_ms']} ms") if n in old_fns_map and old_fns_map[n]["time_ms"] is not None else len("(gone)")
            for n in union_names
        ))
        new_col = max(len("New"),  max(
            len(f"{new_fns_map[n]['time_ms']} ms") if n in new_fns_map and new_fns_map[n]["time_ms"] is not None else len("(gone)")
            for n in union_names
        ))
        chg_col = len("Change")  # will be expanded by data below

        print(f"  {'Function':<{fn_col}} {'Old':>{old_col}} {'New':>{new_col}}   Change")
        print("  " + "-" * (fn_col + old_col + new_col + 20))

        for fn_name in union_names:
            old_fn = old_fns_map.get(fn_name)
            new_fn = new_fns_map.get(fn_name)

            old_t = old_fn["time_ms"] if old_fn else None
            new_t = new_fn["time_ms"] if new_fn else None

            old_str = f"{old_t} ms" if old_fn is not None and old_t is not None else ("(new)" if old_fn is None else "N/A")
            new_str = f"{new_t} ms" if new_fn is not None and new_t is not None else ("(gone)" if new_fn is None else "N/A")

            if old_t is not None and new_t is not None:
                delta = new_t - old_t
                pct = (delta / old_t) * 100 if old_t != 0 else 0
                change_str = f"{_signed(delta)} ms ({_signed_f(pct, 1)}%)"
            else:
                change_str = ""

            print(f"  {fn_name:<{fn_col}} {old_str:>{old_col}} {new_str:>{new_col}}   {change_str}")

        print()


# ── Two-run comparison Markdown output ────────────────────────────────────────

def print_comparison_summary_md(old_results, new_results):
    all_stems = sorted(
        set(old_results.keys()) | set(new_results.keys()),
        key=lambda s: ((old_results.get(s) or new_results.get(s))["name"], s),
    )

    show_crate = any(
        (old_results.get(s) or new_results.get(s))["crate_root"] is not None
        for s in all_stems
    )

    if show_crate:
        print("| Project | Crate Root | Status | Verified | Errors | Total Time |")
        print("|---------|------------|--------|----------|--------|------------|")
    else:
        print("| Project | Status | Verified | Errors | Total Time |")
        print("|---------|--------|----------|--------|------------|")

    for stem in all_stems:
        old = old_results.get(stem)
        new = new_results.get(stem)
        name = (old or new)["name"]
        crate_root = (old or new)["crate_root"]

        if old is None:
            status_str = "(new)"
            ver_str = fmt_int_or_dash(new["verified"])
            err_str = fmt_int_or_dash(new["errors"])
            time_str = fmt_time(new["total_ms"])
        elif new is None:
            status_str = "(removed)"
            ver_str = fmt_int_or_dash(old["verified"])
            err_str = fmt_int_or_dash(old["errors"])
            time_str = fmt_time(old["total_ms"])
        else:
            old_st = fmt_status(old["success"])
            new_st = fmt_status(new["success"])
            status_str = old_st if old_st == new_st else f"{old_st} → {new_st}"
            ver_str = _cmp_int(old["verified"], new["verified"])
            err_str = _cmp_int(old["errors"], new["errors"])
            time_str = _cmp_time(old["total_ms"], new["total_ms"])

        if show_crate:
            cr = crate_root or ""
            print(f"| {name} | {cr} | {status_str} | {ver_str} | {err_str} | {time_str} |")
        else:
            print(f"| {name} | {status_str} | {ver_str} | {err_str} | {time_str} |")

    print()


def print_top5_comparison_md(old_results, new_results):
    all_stems = sorted(
        set(old_results.keys()) | set(new_results.keys()),
        key=lambda s: ((old_results.get(s) or new_results.get(s))["name"], s),
    )

    print("### Top 5 Slowest Functions")
    print()

    for stem in all_stems:
        old = old_results.get(stem)
        new = new_results.get(stem)
        r = old or new
        name = r["name"]
        label = name
        if r["crate_root"]:
            label += f" ({r['crate_root']})"
        print(f"**{label}**")
        print()

        old_fns_map = {fn["name"]: fn for fn in old["functions"]} if old else {}
        new_fns_map = {fn["name"]: fn for fn in new["functions"]} if new else {}

        old_top5 = sorted(old["functions"], key=lambda f: f["time_ms"] or 0, reverse=True)[:5] if old else []
        new_top5 = sorted(new["functions"], key=lambda f: f["time_ms"] or 0, reverse=True)[:5] if new else []

        seen = set()
        union_names = []
        for fn in old_top5 + new_top5:
            if fn["name"] not in seen:
                seen.add(fn["name"])
                union_names.append(fn["name"])

        if not union_names:
            print("_(no timing data available)_")
            print()
            continue

        print("| Function | Old | New | Change |")
        print("|----------|-----|-----|--------|")

        for fn_name in union_names:
            old_fn = old_fns_map.get(fn_name)
            new_fn = new_fns_map.get(fn_name)

            old_t = old_fn["time_ms"] if old_fn else None
            new_t = new_fn["time_ms"] if new_fn else None

            old_str = f"{old_t} ms" if old_fn is not None and old_t is not None else ("(new)" if old_fn is None else "N/A")
            new_str = f"{new_t} ms" if new_fn is not None and new_t is not None else ("(gone)" if new_fn is None else "N/A")

            if old_t is not None and new_t is not None:
                delta = new_t - old_t
                pct = (delta / old_t) * 100 if old_t != 0 else 0
                change_str = f"{_signed(delta)} ms ({_signed_f(pct, 1)}%)"
            else:
                change_str = ""

            print(f"| `{fn_name}` | {old_str} | {new_str} | {change_str} |")

        print()


# ── Main ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description=(
            "Summarize Verita verification results.\n\n"
            "With one directory, prints a per-project summary and the top-5 slowest functions for each project.\n"
            "With two directories, compares old vs. new runs."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  %(prog)s output/2026-01-10-baseline/\n"
            "  %(prog)s output/2026-01-10-baseline/ output/2026-01-11-experiment/"
        ),
    )
    parser.add_argument(
        "--markdown", "-m",
        action="store_true",
        help="output in Markdown table format",
    )
    parser.add_argument(
        "dirs",
        nargs="+",
        metavar="DIR",
        help=(
            "output directory (or directories) to summarize; "
            "each directory should contain the JSON files produced by a single Verita run. "
            "Pass one DIR for a standalone summary, or two DIRs (old then new) for a comparison."
        ),
    )
    args = parser.parse_args()

    md = args.markdown

    if len(args.dirs) == 1:
        results = load_results(args.dirs[0])
        if not results:
            print(f"No JSON files found in {args.dirs[0]}")
            return
        if md:
            print_single_summary_md(results)
            print_top5_single_md(results)
            print_error_summary_md(results)
        else:
            print_single_summary(results)
            print_top5_single(results)
    elif len(args.dirs) == 2:
        old_results = load_results(args.dirs[0])
        new_results = load_results(args.dirs[1])
        if not old_results and not new_results:
            print("No JSON files found in either directory")
            return
        if md:
            print_comparison_summary_md(old_results, new_results)
            print_top5_comparison_md(old_results, new_results)
            print_error_summary_md(new_results)
        else:
            print_comparison_summary(old_results, new_results)
            print_top5_comparison(old_results, new_results)
    else:
        parser.error("Expected 1 or 2 directories")


if __name__ == "__main__":
    main()
