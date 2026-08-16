"""Generate/check the R47 36-cell case study.

Usage:  python3 examples/r47_cells/generate.py [--check]

Certifies all 36 cells (the same self-checks as the origin's hand-tooled
generator: bilinear decomposition identity + 144 Polya corner certificates),
validates the before/after inequality at exact rational sample points on each
cell's box, and emits R47Cells.lean.  --check regenerates in memory and
byte-diffs against frozen/ (nonzero exit on drift).

The emitted Lean is NOT compiled in this repo's CI (it is a large batch); the
origin repository's lean-verify record for the equivalent hand-tooled files is
the compile evidence — see ../../..../proof/PROVENANCE.md.
"""
from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from family import after, before, box, r47_family, r47_profile, u, v  # noqa: E402

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)

HERE = Path(__file__).resolve().parent


def _exact_spot_checks() -> ValidationReport:
    """Exact-rational spot checks of after >= before on each cell's box —
    the numeric-first gate, independent of the symbolic certification."""
    rng = random.Random(19841215)  # Brualdi-Goldwasser vintage
    fam = r47_family()

    def spot():
        for pt in fam.grid.points():
            qa, ra = fam.box(pt)
            for _ in range(6):
                sub0 = {
                    u: sp.Rational(rng.randint(0, 60), rng.randint(1, 6)),
                    v: sp.Rational(rng.randint(0, 60), rng.randint(1, 6)),
                }
                for tq, tr in ((0, 0), (8, 8), (3, 5)):
                    qq = (qa.lo + (qa.hi - qa.lo) * sp.Rational(tq, 8)).subs(sub0)
                    rr = (ra.lo + (ra.hi - ra.lo) * sp.Rational(tr, 8)).subs(sub0)
                    sub = dict(sub0)
                    sub[qa.symbol] = qq
                    sub[ra.symbol] = rr
                    diff = (after(pt) - before(pt)).subs(sub)
                    assert diff >= 0, (pt, sub0, tq, tr, diff)

    return ValidationReport.from_asserts([("r47_exact_spot_checks", spot)])


def build():
    validation = _exact_spot_checks()
    return emit(
        certify(r47_family()),
        r47_profile(),
        [BilinearBoxEmitter()],
        validation,
        file_name="R47Cells.lean",
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        if not rep.ok:
            print("DRIFT:", *rep.details, sep="\n  ")
        print("check:", "OK" if rep.ok else "FAILED")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(
        f"wrote R47Cells.lean ({res.n_theorems} theorems, "
        f"{res.n_checks} self-checks); hash {res.input_hash[:16]}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
