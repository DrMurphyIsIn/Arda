"""Generate the toy example's Lean files: certify -> validate -> emit -> write.

Usage:  python3 examples/toy_box/generate.py [--check]

Without --check: writes lean/Toy/Direct.lean and lean/Toy/Box.lean (and the
frozen/ manifests).  With --check: regenerates in memory and diffs against the
frozen copies — nonzero exit on any drift.
"""
from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from family import (  # noqa: E402
    box_family,
    box_profile,
    direct_family,
    direct_profile,
    lift_family,
    split_family,
    u,
    v,
)

from telperion import (  # noqa: E402
    BilinearBoxEmitter,
    CaseDispatchAssemblyEmitter,
    DirectPolyaEmitter,
    Reparam,
    ReparamAdapterEmitter,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.expr import expr_lean_factored  # noqa: E402
from telperion import BilinearBoxEmitter as _BBE  # noqa: E402
from telperion import SubdivisionGlueEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent


def _exact_spot_checks() -> ValidationReport:
    """The numeric-first discipline in miniature: before formalizing, evaluate the
    claimed inequalities at exact rational sample points (fractions.Fraction —
    no floats) and assert them."""
    rng = random.Random(20260815)
    fam = box_family()
    checks = []

    def spot():
        for pt in fam.grid.points():
            qa, ra = fam.box(pt)
            for _ in range(25):
                uu = Fraction(rng.randint(0, 400), rng.randint(1, 40))
                vv = Fraction(rng.randint(0, 400), rng.randint(1, 40))
                sub0 = {u: sp.Rational(uu), v: sp.Rational(vv)}
                qq = qa.hi.subs(sub0) * sp.Rational(rng.randint(0, 8), 8)
                rr = ra.hi.subs(sub0) * sp.Rational(rng.randint(0, 8), 8)
                sub = dict(sub0)
                sub[qa.symbol] = qq
                sub[ra.symbol] = rr
                diff = (fam.after(pt) - fam.before(pt)).subs(sub)
                assert diff >= 0, (pt, uu, vv, qq, rr, diff)

    def spot_direct():
        dfam = direct_family()
        for pt in dfam.grid.points():
            for _ in range(50):
                uu = sp.Rational(rng.randint(0, 800), rng.randint(1, 40))
                val = dfam.target(pt).subs({u: uu})
                assert val >= 0, (pt, uu, val)

    return ValidationReport.from_asserts(
        [("box_exact_spot_checks", spot), ("direct_exact_spot_checks", spot_direct)]
    )


def _toy_reparam(inst) -> Reparam:
    """Kind-2 instance: re-state each direct certificate over n : ℕ with
    u := (n : ℝ) - 1 under 1 ≤ n, exercising the Nat.cast_sub shape."""
    import re

    body = expr_lean_factored(inst.corners[0].expr, (u,))
    return Reparam(
        nat_binders="(n : ℕ) (h1 : 1 ≤ n)",
        nat_body=re.sub(r"\bu\b", "((n : ℝ) - 1)", body),
        cast_eq=("((n : ℝ) - 1)", "((n - 1 : ℕ) : ℝ)"),
        cast_lemmas=("Nat.cast_sub h1",),
        image="((n - 1 : ℕ) : ℝ)",
    )


def build():
    validation = _exact_spot_checks()
    res_direct = emit(
        certify(direct_family()),
        direct_profile(),
        [
            DirectPolyaEmitter(),
            ReparamAdapterEmitter(reparam=_toy_reparam),
            CaseDispatchAssemblyEmitter(
                name="toy_direct_all",
                axis="a",
                binders="(a : ℕ) (h1 : 1 ≤ a) (h3 : a ≤ 3) (u : ℝ) (hu : 0 ≤ u)",
                body_template="(«axisR» + u) / (u + 1) - «axisR» / (u + 2)",
            ),
        ],
        validation,
        file_name="Direct.lean",
    )
    res_box = emit(
        certify(box_family()),
        box_profile(),
        [BilinearBoxEmitter()],
        validation,
        file_name="Box.lean",
    )
    res_lift = emit(
        certify(lift_family()),
        direct_profile(),
        [DirectPolyaEmitter()],
        validation,
        file_name="Lift.lean",
    )
    from telperion import LeanProfile
    split_profile = LeanProfile(
        namespace=("Toy",),
        imports=("Mathlib", "Toy.Box"),   # reuses Box's bilinear_corner_nonneg
    )
    res_split = emit(
        certify(split_family(), force_subdivide=1),
        split_profile,
        [BilinearBoxEmitter(), SubdivisionGlueEmitter()],
        validation,
        file_name="Split.lean",
    )
    return res_direct, res_box, res_lift, res_split


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res_direct, res_box, res_lift, res_split = build()
    if args.check:
        ok = True
        for res, sub in ((res_direct, "direct"), (res_box, "box"),
                         (res_lift, "lift"), (res_split, "split")):
            rep = diff_frozen(res, HERE / "frozen" / sub)
            if not rep.ok:
                ok = False
                print(f"DRIFT in {sub}:", *rep.details, sep="\n  ")
        # the live lean copies must match the frozen text too
        for res, fname in ((res_direct, "Direct.lean"), (res_box, "Box.lean"),
                           (res_lift, "Lift.lean"), (res_split, "Split.lean")):
            live = HERE / "lean" / "Toy" / fname
            if not live.exists() or live.read_text() != res.files[fname]:
                ok = False
                print(f"DRIFT: lean/Toy/{fname} differs from regenerated text")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    for res, sub in ((res_direct, "direct"), (res_box, "box"),
                     (res_lift, "lift"), (res_split, "split")):
        freeze(res, HERE / "frozen" / sub)
        for fname, text in res.files.items():
            (HERE / "lean" / "Toy" / fname).write_text(text)
    print(
        f"wrote Direct({res_direct.n_theorems}) Box({res_box.n_theorems}) "
        f"Lift({res_lift.n_theorems}) Split({res_split.n_theorems}) theorems"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
