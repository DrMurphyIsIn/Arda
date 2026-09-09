"""PairCollapse6 cell-certificate generator (A3(2) campaign).

Emits `proof/formalization/R3Cert/R47PC6Cells.lean`: the polynomial layer of the PairCollapse6
certificate -- for every cell (d, candidate, cA) of the FROZEN selection table, three cleared
polynomial inequalities (W1, W2' at weight 1/6, ROOT) over the region

    a5,a4,b5,b4 >= 0,  a5+a4 >= 5,  b5+b4 >= 5,  [selection hypothesis]

Each cell is (1) numerically self-checked on a dense exact-Fraction grid BEFORE emission (a wrong
cell refuses to emit), and (2) discharged in Lean by `nlinarith` with a uniform product-hint
battery (validated: the hardest probed cell closes in ~3 s).

Selection table (verified EXACT on 171,693 points, 2026-09-09):
    d=0 : (0,-1,5)  when 1 <= a4+b4       else (-6,7,2)   [a4+b4 = 0]
    d=1 : (1,-2,5)  when 2 <= a4+b4       else (-6,7,3)   [a4+b4 <= 1]
    d=2 : (-2,3,0)  when 2 <= a5+b5       else (2,-3,5)   [a5+b5 <= 1]
    d=3 : (-1,2,0)  when 1 <= a5+b5       else (3,-4,5)   [a5+b5 = 0]
    d>=4: (0,1,d-4) always
Candidate (x,y,c') means target hub (a5+b5+x, a4+b4+y, c'); prefactor V5^x*V4^y/Vc^d.

Usage:  python3 proof/verification/gen_pc6_cells.py [--check]
conjecture1_proved = False.
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

import sympy as sp

V5, V4, Vc = sp.Rational(621, 64), sp.Rational(513, 80), sp.Rational(3, 2)
Q5, Q4, QC = sp.Rational(3, 23), sp.Rational(3, 19), sp.Rational(1, 3)
a5, a4, b5, b4 = sp.symbols("a5 a4 b5 b4", real=True)

OUT = Path(__file__).resolve().parent.parent / "formalization" / "R3Cert" / "R47PC6Cells.lean"

# (d, tag, (x,y,cp), extra-hyp (lean string, sympy nonneg form or None))
SELECTION = []
SELECTION.append((0, "p", (0, -1, 5), ("hsel : 1 ≤ a4 + b4", a4 + b4 - 1)))
SELECTION.append((0, "f", (-6, 7, 2), ("hsel : a4 + b4 ≤ 0", -(a4 + b4))))
SELECTION.append((1, "p", (1, -2, 5), ("hsel : 2 ≤ a4 + b4", a4 + b4 - 2)))
SELECTION.append((1, "f", (-6, 7, 3), ("hsel : a4 + b4 ≤ 1", 1 - (a4 + b4))))
SELECTION.append((2, "p", (-2, 3, 0), ("hsel : 2 ≤ a5 + b5", a5 + b5 - 2)))
SELECTION.append((2, "f", (2, -3, 5), ("hsel : a5 + b5 ≤ 1", 1 - (a5 + b5))))
SELECTION.append((3, "p", (-1, 2, 0), ("hsel : 1 ≤ a5 + b5", a5 + b5 - 1)))
SELECTION.append((3, "f", (3, -4, 5), ("hsel : a5 + b5 ≤ 0", -(a5 + b5))))
for d in range(4, 11):
    SELECTION.append((d, "p", (0, 1, d - 4), None))


def clause_polys(d: int, cand, cA: int):
    """The three cleared numerators (integer-coefficient sympy polys) for one cell."""
    x, y, cp = cand
    cb = d - cA
    QBn = 171 * b5 + 207 * b4 + 437 * cb          # 1311*Q_B
    LB = b5 + b4 + cb
    DB = 1311 * (LB + 1) + QBn                     # 1311*(L_B+1+Q_B)
    Q2n = 171 * a5 + 207 * a4 + 437 * cA
    L2 = a5 + a4 + cA + 1
    envB = 1 + sp.Rational(1, 1311) * QBn / (LB + 1)
    env2 = 1 + (sp.Rational(1, 1311) * Q2n + 1311 / DB) / (L2 + 1)
    A2env = 1 + (sp.Rational(1, 1311) * Q2n + 1311 / DB) / L2
    at, bt = a5 + b5 + x, a4 + b4 + y              # target counts
    Q1n = 171 * at + 207 * bt + 437 * cp
    L1 = at + bt + cp
    env1 = 1 + sp.Rational(1, 1311) * Q1n / (L1 + 1)
    A1env = 1 + sp.Rational(1, 1311) * Q1n / L1
    pref = V5**x * V4**y * Vc**(cp - d)
    out = []
    for expr in (
        pref * env1 - env2 * envB,                                                    # W1
        pref * (env1 + sp.Rational(1, 6) / (L1 + 1))
            - (env2 + sp.Rational(1, 6) / (L2 + 1)) * envB,                           # W2' (1/6)
        pref * A1env - A2env * envB,                                                  # ROOT
    ):
        num, den = sp.fraction(sp.together(expr))
        num = sp.expand(num)
        # normalize: make the denominator positive on the region (all dens are products of
        # positive linear forms up to a rational constant; fix the sign via a sample point)
        sample = {a5: 7, a4: 7, b5: 7, b4: 7}
        if den.subs(sample) < 0:
            num = sp.expand(-num)
        # clear rational content to integer coefficients
        pol = sp.Poly(num, a5, a4, b5, b4)
        lcm = sp.ilcm(*[sp.fraction(sp.Rational(c))[1] for c in pol.coeffs()])
        pol = sp.Poly(sp.expand(num * lcm), a5, a4, b5, b4)
        g = sp.igcd(*[int(c) for c in pol.coeffs()])
        if g > 1:
            pol = sp.Poly(sp.expand(pol.as_expr() / g), a5, a4, b5, b4)
        out.append(pol)
    return out


def numeric_selfcheck(d, cand, cA, pols, sel_form) -> None:
    """Refuse to emit a wrong cell: dense exact check of the three polys on the region."""
    cb = d - cA
    pts = []
    for p5, p4, q5v, q4v in product(range(0, 8), repeat=4):
        if p5 + p4 < 5 or q5v + q4v < 5:
            continue
        pts.append((p5, p4, q5v, q4v))
    import random
    rng = random.Random(1000 * d + 10 * cA + hash(cand) % 97)
    for _ in range(250):
        p5, p4, q5v, q4v = (rng.randint(0, 40) for _ in range(4))
        if p5 + p4 < 5 or q5v + q4v < 5:
            continue
        pts.append((p5, p4, q5v, q4v))
    # region-targeted points for thin (<=-type) selection cells: constrained axes small,
    # free axes swept wide
    for w in list(range(5, 45, 2)):
        for v in range(0, 3):
            pts.append((w, v, w + 3, 2 - v))      # a4+b4 small
            pts.append((v, w, 2 - v, w + 3))      # a5+b5 small
            pts.append((w, 0, w + 7, 0))
            pts.append((0, w, 0, w + 7))
    lam = [sp.lambdify((a5, a4, b5, b4), pol.as_expr(), "math") for pol in pols]
    selfn = sp.lambdify((a5, a4, b5, b4), sel_form, "math") if sel_form is not None else None
    checked = 0
    for (p5, p4, q5v, q4v) in pts:
        if selfn is not None and selfn(p5, p4, q5v, q4v) < 0:
            continue
        checked += 1
        for i, pol in enumerate(pols):
            v = pol.as_expr().subs({a5: p5, a4: p4, b5: q5v, b4: q4v})
            if v < 0:
                raise SystemExit(
                    f"SELF-CHECK FAIL: cell d={d} cand={cand} cA={cA} clause {i} "
                    f"at {(p5, p4, q5v, q4v)}: {v}")
    if checked < 8:
        raise SystemExit(f"SELF-CHECK too sparse for d={d} cand={cand} cA={cA}: {checked}")


def poly_lean(pol) -> str:
    """Render an integer-coefficient sympy Poly in Lean syntax."""
    terms = []
    for exps, coef in sorted(pol.terms(), reverse=True):
        c = int(coef)
        mono = []
        for s, e in zip(("a5", "a4", "b5", "b4"), exps):
            if e == 1:
                mono.append(s)
            elif e > 1:
                mono.append(f"{s}^{e}")
        body = "*".join(mono)
        if body:
            terms.append(f"({c})*{body}" if c < 0 else f"{c}*{body}")
        else:
            terms.append(f"({c})" if c < 0 else f"{c}")
    return " + ".join(terms)


BATTERY = """mul_nonneg h4 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ b5 + b4 - 5) (by linarith : (0:ℝ) ≤ b5 + b4 - 5),
      mul_nonneg (by linarith : (0:ℝ) ≤ a5 + a4 - 5) (by linarith : (0:ℝ) ≤ a5 + a4 - 5),
      sq_nonneg (b5 + b4), sq_nonneg (a5 + a4)"""

SEL_HINTS = {
    "1 ≤ a4 + b4": ", mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1),\n      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 1)",
    "2 ≤ a4 + b4": ", mul_nonneg h5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2),\n      mul_nonneg g5 (by linarith : (0:ℝ) ≤ a4 + b4 - 2)",
    "a4 + b4 ≤ 0": ", mul_nonneg h5 (by linarith : (0:ℝ) ≤ -(a4 + b4)),\n      mul_nonneg g5 (by linarith : (0:ℝ) ≤ -(a4 + b4))",
    "a4 + b4 ≤ 1": ", mul_nonneg h5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4)),\n      mul_nonneg g5 (by linarith : (0:ℝ) ≤ 1 - (a4 + b4))",
    "2 ≤ a5 + b5": ", mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2),\n      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 2)",
    "a5 + b5 ≤ 1": ", mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5)),\n      mul_nonneg g4 (by linarith : (0:ℝ) ≤ 1 - (a5 + b5))",
    "1 ≤ a5 + b5": ", mul_nonneg h4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1),\n      mul_nonneg g4 (by linarith : (0:ℝ) ≤ a5 + b5 - 1)",
    "a5 + b5 ≤ 0": ", mul_nonneg h4 (by linarith : (0:ℝ) ≤ -(a5 + b5)),\n      mul_nonneg g4 (by linarith : (0:ℝ) ≤ -(a5 + b5))",
}


def build() -> str:
    lines = []
    lines.append("""/-
  A3(2): the PairCollapse6 POLYNOMIAL layer -- auto-generated, do not edit by hand.

  For every cell (d = cA + cb, candidate (x,y,c'), cA) of the frozen selection table, the three
  cleared clause numerators (W1, W2' at weight 1/6, ROOT) as integer-coefficient polynomial
  inequalities over the Capped region.  Every cell was numerically self-checked on a dense
  exact grid before emission (proof/verification/gen_pc6_cells.py); nlinarith discharges with a
  uniform product-hint battery.  The bridge layer (rational cavity forms -> these polynomials)
  and the assembly into `PairCollapse6` are separate, upcoming files.

  Genuine proofs (no `sorry`).  conjecture1_proved = False.
-/
import Mathlib

namespace R3Cert
namespace Step3
namespace PC6

set_option maxHeartbeats 1000000
""")
    nthm = 0
    for (d, tag, cand, sel) in SELECTION:
        cA_range = range(max(0, d - 5), min(5, d) + 1)
        for cA in cA_range:
            pols = clause_polys(d, cand, cA)
            numeric_selfcheck(d, cand, cA, pols, sel[1] if sel else None)
            for ci, cname in enumerate(("W1", "W2", "RT")):
                name = f"pc6_d{d}{tag}_c{cA}_{cname}"
                hyp = f"\n    ({sel[0]})" if sel else ""
                allnn = all(c >= 0 for c in pols[ci].coeffs())
                if allnn:
                    tac = "positivity"
                    hopt = ""
                else:
                    extra = ""
                    if sel:
                        key = sel[0].split(" : ", 1)[1]
                        extra = SEL_HINTS.get(key, "")
                    tac = f"nlinarith [{BATTERY}{extra}]"
                    hopt = "set_option maxHeartbeats 4000000 in\n"
                lines.append(f"""{hopt}theorem {name} (a5 a4 b5 b4 : ℝ)
    (h5 : 0 ≤ a5) (h4 : 0 ≤ a4) (g5 : 0 ≤ b5) (g4 : 0 ≤ b4)
    (hA : 5 ≤ a5 + a4) (hB : 5 ≤ b5 + b4){hyp} :
    (0:ℝ) ≤ {poly_lean(pols[ci])} := by
  {tac}
""")
                nthm += 1
    lines.append(f"-- {nthm} cell theorems emitted\nend PC6\nend Step3\nend R3Cert\n")
    return "\n".join(lines)


def main(check: bool = False) -> int:
    text = build()
    if check:
        if not OUT.exists() or OUT.read_text() != text:
            print("DRIFT: R47PC6Cells.lean does not match regeneration")
            return 1
        print("check: OK")
        return 0
    OUT.write_text(text)
    print(f"wrote {OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    sys.exit(main(check=ap.parse_args().check))
