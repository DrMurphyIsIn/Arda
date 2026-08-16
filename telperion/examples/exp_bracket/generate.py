"""The far-case threshold constant, certified: a rigorous rational enclosure of
exp(-theta) for the origin R47Encode far predicate (theta = 0.37167).

The origin's `far_discharge` bounds the objective by 4/3 * exp(-C) * rho^n with
C = theta, and theta was tuned so 4/3 * exp(-theta) equals the template
amplitude C1 = 26/23/rho exactly.  Because that is an EQUALITY, no strict
rational comparison closes it; the useful, honest deliverable is a rigorous
enclosure of the transcendental constant itself:

    exp(-theta) <= 68959/100000      (the amplitude bound far_discharge uses),
    1 - theta   <= exp(-theta)       (a convexity companion lower bound),

both Mathlib-only (Real.sum_le_exp_of_nonneg for the tight upper via a Taylor
lower bound on exp(theta), Real.add_one_le_exp for the lower).  The rational
heart (Taylor_9(theta) >= 145015/100000, hence 1/Taylor <= 68959/100000) is the
Polya-certified target; the Real.exp wrapping is the emitted assembly; the
Fraction engine dual-checks every constant; the compile gate is the arbiter.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CustomAssemblyEmitter,
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)

HERE = Path(__file__).resolve().parent

THETA = Fr(37167, 100000)     # far-case threshold C = theta
NTERMS = 9                    # Real.sum_le_exp_of_nonneg range n (i = 0..8)
TFLOOR = Fr(145015, 100000)   # clean rational <= Taylor_{NTERMS}(theta) <= exp(theta)
HI = Fr(68959, 100000)        # exp(-theta) <= HI
LO = 1 - THETA                # convexity: 1 - theta <= exp(-theta)


def taylor(x: Fr, nterms: int) -> Fr:
    s, term = Fr(0), Fr(1)
    for k in range(nterms):
        s += term
        term = term * x / (k + 1)
    return s


def _family() -> InequalityFamily:
    # Polya-certified rational heart: HI * Taylor_n(theta) - 1 >= 0
    # (=> 1/Taylor <= HI => exp(-theta) = 1/exp(theta) <= 1/Taylor <= HI).
    margin = sp.Rational(HI * taylor(THETA, NTERMS) - 1)
    return InequalityFamily(
        name="ExpBracket",
        symbols=(),
        grid=GridSpec([("i", [0])]),
        lean_name=lambda pt: "exp_neg_theta_bracket_core",
        target=lambda pt: margin,
    )


STATEMENT = """theorem exp_neg_theta_le :
    Real.exp (-(«theta_num» / «theta_den» : ℝ)) ≤ «hi_num» / «hi_den» := by
  rw [Real.exp_neg, ← one_div]
  have hlow : («tf_num» / «tf_den» : ℝ) ≤ Real.exp («theta_num» / «theta_den») := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) «nterms»)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < «tf_num» / «tf_den» := by norm_num
  calc 1 / Real.exp («theta_num» / «theta_den»)
      ≤ 1 / («tf_num» / «tf_den» : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ «hi_num» / «hi_den» := by norm_num

theorem exp_neg_theta_ge :
    (1 - «theta_num» / «theta_den» : ℝ) ≤ Real.exp (-(«theta_num» / «theta_den»)) := by
  have h := Real.add_one_le_exp (-(«theta_num» / «theta_den» : ℝ))
  linarith
«branches»"""


def build():
    fills = {
        "theta_num": str(THETA.numerator), "theta_den": str(THETA.denominator),
        "hi_num": str(HI.numerator), "hi_den": str(HI.denominator),
        "tf_num": str(TFLOOR.numerator), "tf_den": str(TFLOOR.denominator),
        "nterms": str(NTERMS),
    }
    emitter = CustomAssemblyEmitter(
        statement_template=STATEMENT,
        branch_template="",
        fills=lambda fam: fills,
        branch_fills=lambda inst: {},
        theorems=2,
    )
    return emit(
        certify(_family()),
        LeanProfile(namespace=("G1", "ExpBracket")),
        [emitter],
        _validation(),
        file_name="ExpBracket.lean",
    )


def _validation() -> ValidationReport:
    def constants_bracket():
        T = taylor(THETA, NTERMS)
        assert TFLOOR <= T, (TFLOOR, T)              # Taylor lower is valid
        assert 1 / TFLOOR <= HI, (1 / TFLOOR, HI)    # so exp(-theta) <= HI
        # independent (math.exp) enclosure sanity — the true value is inside
        v = math.exp(-float(THETA))
        assert float(LO) <= v <= float(HI), (LO, v, HI)
        # and the amplitude identity the origin reported: 4/3 * exp(-theta) ~ C1
        assert abs(float(Fr(4, 3)) * v - 0.9194424) < 1e-6

    return ValidationReport.from_asserts([("exp_bracket_constants", constants_bracket)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"ExpBracket: {res.n_theorems} theorems, hash {res.input_hash[:16]} "
          f"(exp(-{float(THETA):.5f}) in [{float(LO):.5f}, {float(HI):.5f}])")
    return 0


if __name__ == "__main__":
    sys.exit(main())
