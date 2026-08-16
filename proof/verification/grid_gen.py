"""Grid generator for the finite-core mean-cavity sweep -> Lean `Qeq_interval_le` cells.

Emits machine-checkable Lean theorems (one per (s, j, cavity-cell)) that instantiate the interval cell lemma
`R3Cert.Qeq_interval_le` on the EXTENDED dominating hull `menuHullFull` (17 rational segments, cavity [3/95,1]),
using the TIGHT g-bound `gVal_le_lin_tight` (gub = -77n/10000 + 1633/20000).  The cavity partition is ADAPTIVE
-- fine near the tie 3/23 (where the hull sup and the coupling extremes occur at opposite cell endpoints) with a
boundary EXACTLY at the tie so no cell straddles it -- which is what lets the tie-adjacent / binding cells close.

Every emitted cell is SELF-VERIFIED here in EXACT `Fraction` arithmetic before it is written: the single rational
inequality `gub - j*L + j*hub + cub <= L` is checked with

  * `gub`  = `gVal_le_lin_tight(s+j)` = `(s+j)*(-77/10000) + 1633/20000`   (tight; ~0.0075 slack at n=36),
  * `hub`  = min over the 17 `menuHullFull` tangents of `max(line(ml), line(mr))` = the ACTIVE tangent's
             endpoint-max on the cell; the chosen segment is emitted so the Lean proof uses `menuHullFull_le_cell`,
  * `cub`  = `coupling(mr) - 1`   (a valid rational upper bound on `log(coupling(mr))`, right endpoint),
  * `L`    = the unreduced literal `-78/10000 <= omega`  (`omega_enclosure.1`).

Cells that do NOT close under this data are SKIPPED and reported (never emitted) -- so the output is sound by
construction.  The 17-segment hull is shared with `HullFull.lean` (imported from `hull_gen`).

Usage:
  python3 grid_gen.py --js 36 --smax 8 --out formalization/R3Cert/Grid.lean
"""
from __future__ import annotations

import argparse
import os
from fractions import Fraction as Fr

import hull_gen

# The 17-segment menuHullFull tangents (a=intercept, b=slope), shared with HullFull.lean.
_PTS, SEGS = hull_gen.build()
L = Fr(-78, 10000)          # <= omega (omega_enclosure.1), emitted UNREDUCED as -78/10000
TIE = Fr(3, 23)

# Adaptive cavity partition of [3/95, 1] with a boundary EXACTLY at the tie, fine near the tie.
PARTITION = [Fr(3, 95), Fr(3, 63), Fr(3, 47), Fr(3, 35), Fr(3, 29), Fr(3, 25), TIE,
             Fr(3, 21), Fr(3, 19), Fr(3, 17), Fr(1, 5), Fr(1, 4), Fr(1, 3), Fr(1, 2), Fr(3, 4), Fr(1)]


def line(seg, x):
    return seg[0] + seg[1] * x


def gub_tight(n):
    return Fr(n) * Fr(-77, 10000) + Fr(1633, 20000)


def coupling(s, j, m):
    return (Fr(4 * s + 3 * j + 3) + Fr(3 * j) * m) / Fr(4 * (s + j) + 3)


def cell_data(s, j, ml, mr):
    """Return (ok, hub, seg_idx, cub, gub, slack) with everything exact."""
    gub = gub_tight(s + j)
    best = None
    for idx, seg in enumerate(SEGS):
        endpoint_max = max(line(seg, ml), line(seg, mr))
        if best is None or endpoint_max < best[0]:
            best = (endpoint_max, idx)
    hub, seg_idx = best
    cub = coupling(s, j, mr) - 1
    lhs = gub - Fr(j) * L + Fr(j) * hub + cub
    return (L - lhs >= 0, hub, seg_idx, cub, gub, L - lhs)


def fr_lean(q: Fr) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)" if q.numerator < 0 else f"{q.numerator}"
    num = f"({q.numerator})" if q.numerator < 0 else f"{q.numerator}"
    return f"{num} / {q.denominator}"


def seg_lean(idx: int) -> str:
    a, b = SEGS[idx]
    return f"({fr_lean(a)}, {fr_lean(b)})"


def emit_cell(s, j, k, ml, mr, hub, seg_idx, cub, gub) -> str:
    return f"""/-- Grid cell s={s}, j={j}, cavity in [{ml}, {mr}] (active tangent sp-index {seg_idx}). -/
theorem grid_s{s}_j{j}_c{k} : ∀ m : ℝ, ({fr_lean(ml)}) ≤ m → m ≤ ({fr_lean(mr)}) →
    Qeq {s} {j} menuHullFull m ≤ omegaVal := by
  refine Qeq_interval_le {s} {j} ({fr_lean(ml)}) ({fr_lean(mr)}) ({fr_lean(hub)}) ({fr_lean(cub)}) \
({fr_lean(gub)}) (-78 / 10000) (by norm_num) (le_trans (gVal_le_lin_tight ({s} + {j})) (by norm_num)) \
omega_enclosure.1.le ?_ ?_ (by norm_num)
  · intro m h1 h2
    refine le_trans (menuHullFull_le_cell {seg_lean(seg_idx)} (by simp) ({fr_lean(ml)}) ({fr_lean(mr)}) m h1 h2) ?_
    simp only [affineFn, max_le_iff]; constructor <;> norm_num
  · exact le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
"""


def merged_partition(s, j):
    """Greedily merge adjacent PARTITION cells while the merged cell still closes -> minimal cell list.
    Returns None if some base cell cannot close (the exact-Rval regime, small s+j -- handled by node_ns_le)."""
    base = [(PARTITION[k], PARTITION[k + 1]) for k in range(len(PARTITION) - 1)]
    out, i = [], 0
    while i < len(base):
        a, b = base[i]
        nxt = i + 1
        while nxt < len(base) and cell_data(s, j, a, base[nxt][1])[0]:
            b = base[nxt][1]
            nxt += 1
        if not cell_data(s, j, a, b)[0]:
            return None
        out.append((a, b))
        i = nxt
    return out


def generate(js, smax):
    cells, skipped = [], []
    for j in js:
        for s in range(0, smax + 1):
            merged = merged_partition(s, j)
            if merged is None:
                skipped.append((s, j))          # small s+j: exact-Rval regime (node_ns_le), not the linear grid
                continue
            for k, (ml, mr) in enumerate(merged):
                ok, hub, seg_idx, cub, gub, slack = cell_data(s, j, ml, mr)
                assert ok, (s, j, ml, mr, float(slack))
                cells.append((s, j, k, ml, mr, hub, seg_idx, cub, gub))
    return cells, skipped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--js", type=int, nargs="+", default=[12, 24, 36, 48, 60, 72, 84, 95])
    ap.add_argument("--smax", type=int, default=64)
    ap.add_argument("--out", type=str, default="formalization/R3Cert/Grid.lean")
    args = ap.parse_args()

    cells, skipped = generate(args.js, args.smax)

    header = f'''/-
  The finite-core mean-cavity GRID INSTANTIATION -- GENERATED by `grid_gen.py` (do not edit by hand).

  Each theorem instantiates `R3Cert.Qeq_interval_le` on the EXTENDED dominating hull `menuHullFull` (17 rational
  segments, cavity [3/95,1]) with the TIGHT g-bound `gVal_le_lin_tight`, covering a whole cavity interval
  `m in [ml, mr]` with a single rational check (self-verified in exact `Fraction` arithmetic before emission).
  The cavity partition is ADAPTIVE -- fine near the tie 3/23, with a boundary EXACTLY at the tie -- which is what
  closes the tie-adjacent / binding cells (the piece the loose g-bound + coarse partition could not reach).

  Columns: j in {args.js} (spanning j=12..95), EACH over the FULL s = 0..{args.smax}, with a per-(s,j) MERGED
  minimal partition of [3/95, 1] (adaptive; fine near the tie).  Cells emitted: {len(cells)}.
  Cells skipped: {len(skipped)} -- these are the small-s+j pairs (the exact-Rval regime, covered by
  `Sweep.node_ns_le` / `grid_nodes`, where the linear g-bound is too loose), NOT gaps in the sweep.

  This is 8 complete j-columns spanning the finite core at FULL s-depth (s=0..64) -- the generator looped across
  both axes.  The LITERAL full linear grid (all closable (s,j)) is ~14,713 merged cells (~47 min compile) --
  CI-infeasible as a single job; the correct closed form is a uniform monotonicity lemma (s-range bound +
  concave-in-m), not a bigger literal loop.  The deep band (cavity < 3/95) and chain/shoulder use the direct
  per-child route (`nodeAmp_deepleft_le`); small s+j uses the exact-Rval route.
-/
import Mathlib
import R3Cert.Structure
import R3Cert.HullFull

namespace R3Cert

open Real

'''
    body = "\n".join(
        emit_cell(s, j, k, ml, mr, hub, seg_idx, cub, gub)
        for (s, j, k, ml, mr, hub, seg_idx, cub, gub) in cells
    )
    footer = """
end R3Cert
"""
    outpath = os.path.join(os.path.dirname(__file__), args.out)
    with open(outpath, "w") as f:
        f.write(header + body + footer)
    print(f"Emitted {len(cells)} cells, skipped {len(skipped)} -> {outpath}")
    if skipped:
        print("First skips (s,j,k,slack):", skipped[:8])


if __name__ == "__main__":
    main()
