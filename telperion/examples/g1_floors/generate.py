"""G1 floors: certify -> validate -> emit -> freeze.  --check = drift diff.

Emits G1Floors.lean (the bracket-quantified floor cells) and G1Anchors.lean
(the Taylor-bracket kernel facts the floors stand on).
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
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


def _taylor_sum_expr(q: Fr, K: int) -> sp.Expr:
    """The UNEVALUATED Taylor partial sum 1 + q + q^2/2! + ... + q^K/K!."""
    import math as _m

    terms = [sp.Integer(1)]
    for k in range(1, K + 1):
        terms.append(
            sp.Mul(
                sp.Pow(sp.Rational(q), k, evaluate=False),
                sp.Rational(1, _m.factorial(k)),
                evaluate=False,
            )
        )
    return sp.Add(*terms, evaluate=False)


def _anchor_family_and_spellings():
    facts = F.anchor_facts()
    spellings = {}
    rows = []
    for name, u0, q, K in facts:
        lhs = sp.Rational(1 + u0)             # 1 + u0 <= Taylor_K(q)
        rhs = _taylor_sum_expr(q, K)
        rows.append((name, lhs, rhs))
        spellings[name] = (lhs, "≤", rhs)
    # exp brackets for L and G (both directions: the real constant is IN the
    # bracket).  exp_upper's geometric tail is rational, so these are facts.
    def _exp_lower_expr(x, K):
        return _taylor_sum_expr(x, K)

    def _exp_upper_expr(x, K=30):
        import math as _m

        s_ = _taylor_sum_expr(x, K)
        term = sp.Mul(sp.Pow(sp.Rational(x), K + 1, evaluate=False),
                      sp.Rational(1, _m.factorial(K + 1)), evaluate=False)
        tail = sp.Mul(term, sp.Rational(Fr(1) / (1 - Fr(x) / (K + 2))),
                      evaluate=False)
        return sp.Add(s_, tail, evaluate=False)

    v5q = sp.Rational(621, 64)
    threehalf = sp.Rational(3, 2)
    for nm, lo, hi, tgt in (("L", F.L_LO, F.L_HI, v5q),
                            ("G", F.G_LO, F.G_HI, threehalf)):
        mult = 11 if nm == "L" else 1
        up = _exp_upper_expr(mult * lo)
        Kmin = next(k for k in range(1, 31)
                    if F.exp_lower(Fr(mult) * hi, k) >= (Fr(621, 64) if nm == "L" else Fr(3, 2)))
        low = _exp_lower_expr(mult * hi, Kmin)
        rows.append((f"{nm}_bracket_lo", up, tgt))
        spellings[f"{nm}_bracket_lo"] = (up, "≤", tgt)
        rows.append((f"{nm}_bracket_hi", tgt, low))
        spellings[f"{nm}_bracket_hi"] = (tgt, "≤", low)

    # the T0 bracket pair: (1+T_LO)^11 <= 621/64 <= (1+T_HI)^11
    tlo1 = sp.Pow(sp.Rational(1 + F.T_LO), 11, evaluate=False)
    thi1 = sp.Pow(sp.Rational(1 + F.T_HI), 11, evaluate=False)
    v5 = sp.Rational(621, 64)
    rows.append(("t0_bracket_lo", tlo1, v5))
    spellings["t0_bracket_lo"] = (tlo1, "≤", v5)
    rows.append(("t0_bracket_hi", v5, thi1))
    spellings["t0_bracket_hi"] = (v5, "≤", thi1)

    names = [r[0] for r in rows]

    def target(pt):
        name = names[pt["i"]]
        lhs, rel, rhs = spellings[name]
        return sp.expand(rhs.doit() - lhs.doit() if hasattr(rhs, "doit") else rhs - lhs)

    fam = InequalityFamily(
        name="G1Anchors",
        symbols=(),
        grid=GridSpec([("i", list(range(len(names))))]),
        lean_name=lambda pt: names[pt["i"]],
        target=target,
    )
    return fam, lambda pt: spellings[names[pt["i"]]]


def build():
    floors = emit(
        certify(F.family(), workers=4),
        F.profile(),
        [BilinearBoxEmitter()],
        F.validation(),
        file_name="G1Floors.lean",
    )
    anchor_fam, spelling = _anchor_family_and_spellings()
    anchors = emit(
        certify(anchor_fam),
        LeanProfile(namespace=("G1", "Anchors")),
        [ExactFactEmitter(spelling=spelling, tactic="norm_num",
                          type_ascription="ℚ")],
        F.validation(),
        file_name="G1Anchors.lean",
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
        for res, fname, live in ((floors, "G1Floors.lean", "Floors.lean"),
                                 (anchors, "G1Anchors.lean", "Anchors.lean")):
            p = HERE / "lean" / "G1" / live
            if not p.exists() or p.read_text() != res.files[fname]:
                ok = False
                print(f"DRIFT: lean/G1/{live} differs from regenerated text")
        print("check:", "OK" if ok else "FAILED")
        return 0 if ok else 1
    for res, sub in ((floors, "floors"), (anchors, "anchors")):
        freeze(res, HERE / "frozen" / sub)
    lean_dir = HERE / "lean" / "G1"
    lean_dir.mkdir(parents=True, exist_ok=True)
    (lean_dir / "Floors.lean").write_text(floors.files["G1Floors.lean"])
    (lean_dir / "Anchors.lean").write_text(anchors.files["G1Anchors.lean"])
    print(
        f"G1Floors: {floors.n_theorems} theorems ({floors.n_checks} checks), "
        f"hash {floors.input_hash[:16]}; G1Anchors: {anchors.n_theorems} facts, "
        f"hash {anchors.input_hash[:16]}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
