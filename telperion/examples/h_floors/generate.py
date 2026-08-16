"""H-floors: certify -> validate -> emit -> freeze.  --check = drift diff.

Emits HFloors.lean (56 bracket-quantified piece claims in origin's
H/slackForm spelling) and HFloorAnchors.lean (the deduped log1p Taylor
anchors).  The L-bracket instantiation facts live in G1Anchors (same
constant) — not duplicated here.
"""
from __future__ import annotations

import argparse
import math
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import family as F  # noqa: E402

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    ExactFactEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    certify,
    diff_frozen,
    emit,
    freeze,
)

HERE = Path(__file__).resolve().parent


def _taylor_sum_expr(q, K: int) -> sp.Expr:
    terms = [sp.Integer(1)]
    for k in range(1, K + 1):
        terms.append(sp.Mul(sp.Pow(sp.Rational(q), k, evaluate=False),
                            sp.Rational(1, math.factorial(k)),
                            evaluate=False))
    return sp.Add(*terms, evaluate=False)


def _anchor_family_and_spelling():
    facts = F.anchor_facts()
    rows, spellings = [], {}
    for name, u0, q, K in facts:
        lhs = sp.Rational(1 + u0)
        rhs = _taylor_sum_expr(q, K)
        rows.append(name)
        spellings[name] = (lhs, "≤", rhs)

    def target(pt):
        lhs, _, rhs = spellings[rows[pt["i"]]]
        return sp.expand(rhs.doit() - lhs)

    fam = InequalityFamily(
        name="HFloorAnchors",
        symbols=(),
        grid=GridSpec([("i", list(range(len(rows))))]),
        lean_name=lambda pt: rows[pt["i"]],
        target=target,
    )
    return fam, lambda pt: spellings[rows[pt["i"]]]


def build():
    floors = emit(
        certify(F.family(), workers=4),
        F.profile(),
        [BilinearBoxEmitter()],
        F.validation(),
        file_name="HFloors.lean",
    )
    anchor_fam, spelling = _anchor_family_and_spelling()
    anchors = emit(
        certify(anchor_fam),
        LeanProfile(namespace=("G1", "HFloorAnchors")),
        [ExactFactEmitter(spelling=spelling, tactic="norm_num",
                          type_ascription="ℚ")],
        F.validation(),
        file_name="HFloorAnchors.lean",
    )
    return floors, anchors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    floors, anchors = build()
    if args.check:
        ok = True
        for res, sub in ((floors, "floors"), (anchors, "anchors")):
            rep = diff_frozen(res, HERE / "frozen" / sub)
            if not rep.ok:
                ok = False
                print(f"DRIFT in {sub}:", *rep.details, sep="\n  ")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    for res, sub in ((floors, "floors"), (anchors, "anchors")):
        freeze(res, HERE / "frozen" / sub)
    print(f"HFloors: {floors.n_theorems} theorems ({floors.n_checks} checks), "
          f"hash {floors.input_hash[:16]}; HFloorAnchors: {anchors.n_theorems} "
          f"anchors, hash {anchors.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
