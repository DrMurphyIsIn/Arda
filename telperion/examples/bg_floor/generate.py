"""Generate the Brualdi-Goldwasser R7 ledger-floor certificate (chain class).

    python examples/bg_floor/generate.py           # write lean/BGFloor.lean
    python examples/bg_floor/generate.py --check    # drift check (no write)

R7 (the open frontier of the BG program) hardens the slack-ledger CONTEXT-FREE
FLOORS: for each structural class, the per-node slack

    slack(y) = p*L - a*log(3/2) - log(1+u) - (11/50)*D

(hinge potential defect; equal-children/Jensen relaxation, child cavity y in
(0,1/2]) is >= a positive class floor.  The parallel BG kernel
(proof/verification/g1_floor_certificates.py) certifies these in exact rational
arithmetic via adaptive bisection; this example emits the CHAIN class
(a=0, nl=0, m=1; floor 27/5000) as a CLEAN, single kernel-checked Bernstein
certificate — the Telperion beachhead for the G1 floor lemma.

CHAIN class: p=1, k=1, S=y, u=y/2, cav=1/(2+y).  Bracket the transcendentals by
verified rationals (the kernel's constants):
  * L = log(621/64)/11 >= L_LO = 206586/10^6           (g1_floor_certificates._verified_constants)
  * log(1+u) <= u - u^2/2 + u^3/3 - u^4/4 + u^5/5       (alternating-series upper bound, u>=0)
  * T0 = rhoB - 1 in [T_LO, T_HI], T_LO = 2294736/10^7
Split the hinge at T0 into two rational cells (a COMPLETE cover of [0,1/2]):
  * I1 = [0, T_LO]      : y <= T0 so (y-T0)_+ = 0, D = cav - T0 <= 1/(2+y) - T_LO
  * I2 = [T_LO, 1/2]    : T0 CANCELS between the two hinge terms, D = cav - y = 1/(2+y) - y (EXACT)
On each cell, clearing the positive denominator (2+y) turns slack_lb(y) - floor >= 0
into a degree-6 polynomial positivity, certified by Telperion's Bernstein emitter.

The theorem certifies `0 <= numerator(slack_lb - floor)` per cell; since (2+y) > 0
that is exactly `slack_lb(y) >= floor`, and slack_lb(y) <= slack(y) by the rational
brackets above (the kernel's exp/log bracket lemmas), so slack(y) >= 27/5000 on the
whole chain-cavity range.  conjecture1_proved = False; this is one G1 brick.
"""
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import BernsteinEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_bernstein import bernstein_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "BGFloor.lean"

# --- verified rational constants (proof/verification/g1_floor_certificates.py) ---
_L_LO = sp.Rational(206586, 10**6)      # L = log(621/64)/11 >= L_LO
_T_LO = sp.Rational(2294736, 10**7)     # T0 = rhoB - 1 >= T_LO
_C = sp.Rational(11, 50)                # hinge constant 0.22
_FLOOR = sp.Rational(27, 5000)          # chain-class ledger floor (~0.0054)
_HALF = sp.Rational(1, 2)

_Y = sp.Symbol("y")


def _cells():
    """(lean_name, numerator poly, lo, hi) for the two hinge cells of the chain class."""
    u = _Y / 2
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5   # log(1+u) <= this
    slb1 = _L_LO - log_ub - _C * (1 / (2 + _Y) - _T_LO)      # I1: (y-T0)_+ = 0
    slb2 = _L_LO - log_ub - _C * (1 / (2 + _Y) - _Y)         # I2: T0 cancels, D = cav - y
    out = []
    for name, expr, lo, hi in [
        ("bg_floor_chain_below_knee", slb1, sp.Integer(0), _T_LO),
        ("bg_floor_chain_above_knee", slb2, _T_LO, _HALF),
    ]:
        num = sp.expand(sp.fraction(sp.together(expr - _FLOOR))[0])   # denom (2+y) > 0
        out.append((name, num, lo, hi))
    return out


def build() -> str:
    cells = _cells()
    names = {i: c[0] for i, c in enumerate(cells)}
    specs = {i: (c[1], c[2], c[3]) for i, c in enumerate(cells)}
    fam = bernstein_family(
        "BGFloor",
        (_Y,),
        GridSpec([("cell", list(range(len(cells))))]),
        lambda pt: names[pt["cell"]],
        spec=lambda pt: specs[pt["cell"]],
        n_max=16,
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BGFloor",)),
        [BernsteinEmitter()],
        ValidationReport(checks=(("bernstein", True),)),
    )
    text = next(iter(report.files.values()))
    # degree-6 rings with large rational coefficients can exceed Lean's default
    # 200k-heartbeat cap; raise it locally (the shared emitter stays untouched).
    for nm in names.values():
        text = text.replace(
            f"theorem {nm}",
            f"set_option maxHeartbeats 2000000 in\ntheorem {nm}",
        )
    return text


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BGFloor.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
