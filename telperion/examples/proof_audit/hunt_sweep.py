"""The hunt-attack sweep: the audit's one ADVERSARIAL stratum.

Every other audit row is confirmatory re-derivation; this one genuinely tries
to BREAK each certified family, exactly, with the three hunt modes
(coordinate descent, GA+memetic, quality-diversity).  A hunted value below
zero is a theorem — the claim is false, exact witness attached.  A
nonnegative sweep is evidence (recorded with the tightest point found), never
proof — the proofs are the certificates.

Attack shape by claim kind:
  * target      — minimize the target over the orthant (box-bounded where the
                  family declares constant bounds);
  * witnesses   — minimize the POINTWISE MAX over all candidates (the
                  existential claim fails only where every candidate fails);
  * equation    — exact evaluation at random rationals (any nonzero
                  difference is a disproof of the identity);
  * constants   — the value is its own verdict.

Ties are expected to hunt to EXACTLY zero — a zero minimum at a declared tie
is the geometry, not a break.  Skipped cells (non-constant box bounds) are
counted and reported, never silently dropped.

Usage: hunt_sweep.py [--check]   (--check re-runs and compares fingerprints)
"""
from __future__ import annotations

import argparse
import hashlib
import json
import multiprocessing as mp
import random
import sys
import time
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
TELPERION = HERE.parents[1]
sys.path.insert(0, str(TELPERION / "src"))

from telperion.hunt import hunt_diverse, hunt_evolve, hunt_minimum  # noqa: E402

# (example, families-to-skip, cells sampled per family, hunt effort scale)
PLAN = [
    ("r47_cells", (), 24, 1.0),
    ("g1_floors", (), 36, 1.0),
    ("shed_lemmas", (), 30, 1.0),
    ("legs_certs", (), 999, 1.0),        # constants: all, trivially
    ("interp_lemma", (), 60, 1.0),
    ("g34_twohub", (), 24, 0.6),         # big exprs; witness cells via Max
    ("r7_starofhubs", (), 6, 0.4),       # heaviest candidates
]
SEED = 47


def _load_families(example: str):
    import importlib.util

    p = TELPERION / "examples" / example / "family.py"
    spec = importlib.util.spec_from_file_location(f"_hunt_{example}", p)
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(p.parent))
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.path.pop(0)
    return [(a, getattr(mod, a)()) for a in dir(mod)
            if (a == "family" or a.endswith("_family"))
            and getattr(getattr(mod, a), "__module__", None) == mod.__name__]


TASKS: list[tuple] = []          # populated pre-fork; shared copy-on-write


def _build_tasks() -> dict:
    """Returns {example: bookkeeping}; appends hunt tasks to TASKS and
    resolves equation/constant kinds inline (they need no optimizer)."""
    rng = random.Random(SEED)
    inline: dict[str, dict] = {}
    for example, skip, k, effort in PLAN:
        book = inline.setdefault(example, {
            "cells_hunted": 0, "cells_inline": 0, "skipped": 0,
            "inline_min": None, "inline_where": None, "identity_points": 0,
            "disproofs": []})
        for fname, fam in _load_families(example):
            if fname in skip:
                continue
            pts = list(fam.grid.points())
            sample = pts if len(pts) <= k else rng.sample(pts, k)
            for i, pt in enumerate(sample):
                name = fam.lean_name(pt)
                if fam.equation is not None:
                    lhs, rhs = fam.equation(pt)
                    diff = sp.together(lhs - rhs)
                    for _ in range(40):
                        sub = {s: sp.Rational(rng.randint(0, 400),
                                              rng.randint(1, 16))
                               for s in fam.symbols}
                        v = sp.cancel(diff.subs(sub)) if fam.symbols else diff
                        if sp.simplify(v) != 0:
                            book["disproofs"].append(
                                {"cell": name, "kind": "identity",
                                 "at": {str(s): str(x) for s, x in sub.items()}})
                        book["identity_points"] += 1
                    book["cells_inline"] += 1
                    continue
                if fam.witnesses is not None:
                    exprs = [e for _, e in fam.witnesses(pt)]
                    expr, syms = sp.Max(*exprs), fam.symbols
                    lo, hi = {}, {}
                elif fam.target is not None:
                    expr, syms, lo, hi = fam.target(pt), fam.symbols, {}, {}
                else:                                   # bilinear box
                    # Reparametrize each box axis to u in [0,1]:
                    # s = lo + u*(hi - lo) — exact, and uniform whether the
                    # bounds are constants or expressions in the continuous
                    # symbols (no cell is ever skipped for symbolic bounds).
                    expr = fam.after(pt) - fam.before(pt)
                    lo, hi, syms = {}, {}, tuple(fam.symbols)
                    for ax in fam.box(pt):
                        u = sp.Symbol(f"u_{ax.symbol}", nonnegative=True)
                        expr = expr.subs(ax.symbol,
                                         ax.lo + u * (ax.hi - ax.lo))
                        hi[u] = sp.Integer(1)
                        syms += (u,)
                if not syms:                            # exact constant
                    v = sp.Rational(expr)
                    if v < 0:
                        book["disproofs"].append({"cell": name,
                                                  "kind": "constant"})
                    if book["inline_min"] is None or v < book["inline_min"]:
                        book["inline_min"], book["inline_where"] = v, name
                    book["cells_inline"] += 1
                    continue
                TASKS.append((example, name, expr, syms, lo, hi,
                              SEED + i, effort))
                book["cells_hunted"] += 1
    return inline


def _hunt_one(idx: int):
    example, name, expr, syms, lo, hi, seed, effort = TASKS[idx]
    it = max(1, int(120 * effort))
    best = hunt_minimum(expr, syms, iters=it, restarts=3, seed=seed,
                        lo=lo or None, hi=hi or None)
    ev = hunt_evolve(expr, syms, pop=12, gens=max(4, int(12 * effort)),
                     seed=seed, lo=lo or None, hi=hi or None)
    if ev.minimum < best.minimum:
        best = ev
    for d in hunt_diverse(expr, syms, iters=max(60, int(200 * effort)),
                          seed=seed, lo=lo or None, hi=hi or None, top=3):
        if d.minimum < best.minimum:
            best = d
    return (example, name,
            f"{sp.Rational(best.minimum)}",
            {k: str(v) for k, v in best.argmin.items()},
            best.evaluations + ev.evaluations)


def run(workers: int = 6) -> dict:
    t0 = time.time()
    books = _build_tasks()
    print(f"hunt: {len(TASKS)} optimizer cells + inline strata; "
          f"workers={workers}", flush=True)
    ctx = mp.get_context("fork")
    with ctx.Pool(workers) as pool:
        results = pool.map(_hunt_one, range(len(TASKS)), chunksize=1)
    report: dict[str, dict] = {}
    for example, book in books.items():
        fam_res = [r for r in results if r[0] == example]
        entry = dict(book)
        entry["evaluations"] = sum(r[4] for r in fam_res)
        hunted = [(sp.Rational(r[2]), r[1], r[3]) for r in fam_res]
        for v, cell, arg in hunted:
            if v < 0:
                entry["disproofs"].append({"cell": cell, "kind": "hunted",
                                           "minimum": str(v), "argmin": arg})
        if hunted:
            v, cell, arg = min(hunted, key=lambda t: t[0])
            entry["tightest"] = {"minimum": str(v), "cell": cell, "argmin": arg}
        entry["inline_min"] = (str(entry["inline_min"])
                               if entry["inline_min"] is not None else None)
        report[example] = entry
    total_dis = sum(len(e["disproofs"]) for e in report.values())
    fp = hashlib.sha256(json.dumps(report, sort_keys=True).encode()).hexdigest()
    out = {"seed": SEED, "families": report, "disproofs_total": total_dis,
           "verdict": "NO DISPROOF FOUND" if total_dis == 0
                      else f"DISPROOFS: {total_dis}",
           "fingerprint": fp, "runtime_seconds": round(time.time() - t0, 1)}
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--workers", type=int, default=6)
    args = ap.parse_args()
    out = run(args.workers)
    frozen = HERE / "frozen"
    if args.check:
        prev = json.loads((frozen / "hunt_report.json").read_text())
        ok = (prev["fingerprint"] == out["fingerprint"]
              and out["disproofs_total"] == 0)
        print("check:", "OK" if ok else "FAILED (fingerprint drift or disproof)")
        return 0 if ok else 1
    frozen.mkdir(exist_ok=True)
    (frozen / "hunt_report.json").write_text(json.dumps(out, indent=1))
    print(f"hunt sweep: {out['verdict']}; "
          f"{sum(e['cells_hunted'] for e in out['families'].values())} hunted "
          f"+ {sum(e['cells_inline'] for e in out['families'].values())} inline "
          f"cells, {sum(e.get('skipped', 0) for e in out['families'].values())} "
          f"skipped; fingerprint {out['fingerprint'][:16]}; "
          f"{out['runtime_seconds']}s")
    for ex, e in out["families"].items():
        t = e.get("tightest")
        print(f"  {ex}: tightest hunted "
              f"{t['minimum'] + ' at ' + t['cell'] if t else '(inline only)'}"
              f"{'; inline min ' + e['inline_min'] if e['inline_min'] else ''}",
              flush=True)
    return 0 if out["disproofs_total"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
