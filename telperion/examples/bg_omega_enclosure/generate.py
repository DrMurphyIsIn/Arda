"""Taylor-log + d9 wired into BG: the omega enclosure of R3Cert/Sweep.lean.

BG's `omega_enclosure` (`R3Cert/Sweep.lean`) is the sweep's comparison target:
`omega = (3/11) log 3 - (5/11) log 2 - (2/11) log(1 - 1/24)`, enclosed as
`-78/10000 < omega < -77/10000`.  It combines the {log 2, log 3} basis (Mathlib d9
constants) with a degree-4 Taylor enclosure of `log(1 - 1/24)`.

This regenerates the transcendental content of that enclosure via Telperion:
`TaylorLogNear1Certificate` supplies the `log(1-1/24)` bracket, the d9 constants supply
`log 2`, `log 3`, and `nlinarith` closes the window (computed here from the interval box,
outward-rounded to BG's /10000 grid).  Stated over the explicit combination
`3/11 log 3 - 5/11 log 2 - 2/11 log(1-1/24)` (= omegaVal) so it is self-contained and
kernel-checkable in the rh_lean gate.  RH-toolchain reuse on a real BG constant; NOT RH
or BG progress.  conjecture1_proved = False.

    python3 examples/bg_omega_enclosure/generate.py [--check]
"""
from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.taylor_log import TaylorLogNear1Certificate  # noqa: E402
from telperion.tight_log import LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGOmegaEnclosure.lean"

# omega = c3 log3 + c2 log2 + ct log(1-1/24)
C3, C2, CT = Fr(3, 11), Fr(-5, 11), Fr(-2, 11)
K, DEGREE, PRECISION = 24, 4, 10000
EXPR = "3 / 11 * Real.log 3 - 5 / 11 * Real.log 2 - 2 / 11 * Real.log (1 - 1 / 24)"


def _window(tay: TaylorLogNear1Certificate) -> tuple[Fr, Fr]:
    tlo, thi = tay.bracket()  # bracket on log(1-1/24)
    lo = (C3 * (LOG3_LO if C3 > 0 else LOG3_HI) + C2 * (LOG2_LO if C2 > 0 else LOG2_HI)
          + CT * (tlo if CT > 0 else thi))
    hi = (C3 * (LOG3_HI if C3 > 0 else LOG3_LO) + C2 * (LOG2_HI if C2 > 0 else LOG2_LO)
          + CT * (thi if CT > 0 else tlo))
    P = PRECISION
    return Fr(math.floor(lo * P), P), Fr(math.ceil(hi * P), P)


def build() -> str:
    tay = TaylorLogNear1Certificate(name="_", k=K, degree=DEGREE)
    if not tay.check():
        raise ValueError("taylor bracket invalid")
    lo, hi = _window(tay)
    lo_n, hi_n = lo * PRECISION, hi * PRECISION  # integer numerators over /PRECISION
    assert lo_n.denominator == 1 and hi_n.denominator == 1
    thm = (
        f"theorem bg_omega_enclosure :\n"
        f"    ({int(lo_n)} : ℝ) / {PRECISION} < {EXPR}\n"
        f"      ∧ {EXPR} < ({int(hi_n)} : ℝ) / {PRECISION} := by\n"
        f"  have h2lo := Real.log_two_gt_d9\n"
        f"  have h2hi := Real.log_two_lt_d9\n"
        f"  have h3lo := Real.log_three_gt_d9\n"
        f"  have h3hi := Real.log_three_lt_d9\n"
        f"{tay.htay_block('htay')}"
        f"  refine ⟨by nlinarith [h2lo, h2hi, h3lo, h3hi, htay.1, htay.2],\n"
        f"    by nlinarith [h2lo, h2hi, h3lo, h3hi, htay.1, htay.2]⟩\n"
    )
    header = (
        "/- Taylor-log + d9 wired into BG: the omega enclosure of R3Cert/Sweep.lean.\n"
        "   omega = 3/11 log 3 - 5/11 log 2 - 2/11 log(1 - 1/24), enclosed in BG's /10000\n"
        "   window via Mathlib's Real.log_{two,three}_d9 + a degree-4 Taylor bracket of\n"
        "   log(1-1/24) (Real.abs_log_sub_add_sum_range_le).  Regenerated + kernel-checkable. -/\n"
        "import Mathlib\n\nnamespace BGOmegaEnclosure\n\n"
    )
    return header + thm + "\nend BGOmegaEnclosure\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        if not OUT.exists():
            print(f"MISSING: {OUT}")
            return 1
        if OUT.read_text() != src:
            print(f"DRIFT: {OUT} differs from freshly generated output")
            return 1
        print(f"OK: {OUT} matches")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(src)
    print(f"WROTE: {OUT} (BG omega enclosure via d9 + degree-{DEGREE} Taylor)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
