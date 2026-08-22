"""Generate the BG R7 ledger-floor certificates for the bare-leaf and nl=2 families.

    python examples/bg_floor_families/generate.py           # write lean/BGFloorFamilies.lean
    python examples/bg_floor_families/generate.py --check    # drift check (no write)

Extends the chain-class beachhead (examples/bg_floor/) to the two main context-free
ledger classes with a child cavity `y in (0,1/2]`:

  * bare-leaf   (nl=1, floor 26/500 = 0.052),  a in 0..9,  m in {1,2,3}
  * nl=2        (nl=2, floor 54/500 = 0.108),  a in 0..6,  m in {1,2,3}

For class (a, nl, m) the per-node slack (equal children at cavity y) is

    slack(y) = p*L - a*log(3/2) - log(1+u) - (11/50)*D,
    p = 1+2a+nl,  k = a+nl+m,  S = a/3+nl+m*y,  u = S/(k+1),
    cav = 1/(k+1+S),  D = (cav-T0)_+ - m*(y-T0)_+ .

Bracket the transcendentals by verified rationals (BG kernel g1_floor_certificates):
  * L >= L_LO = 206586/10^6 ;  log(3/2) <= G_HI = 405466/10^6
  * log(1+u) <= u - u^2/2 + u^3/3 - u^4/4 + u^5/5   (alternating-series upper bound)
Upper-bound D on two cells tiling [0,1/2] (so slack_lb <= slack):
  * cav decreases in y, so (cav-T0)_+ <= (cav(0) - T_LO)_+ =: Dc  (a per-class constant)
  * below-cell [0, T_HI] : drop the help term ((y-T0)_+ >= 0),          D <= Dc
  * above-cell [T_LO, 1/2]: keep it via (y-T0)_+ >= y - T_HI,           D <= Dc - m*(y - T_HI)
On each cell slack_lb(y) is a degree-5 polynomial; slack_lb(y) - floor >= 0 is
certified by Telperion's Bernstein emitter (nonneg coefficients) -> ring + linarith.

The wider margins here (>= 0.0089 bare-leaf, >= 0.065 nl=2) make these strictly
lower-risk than the tight chain class.  Two class facets are handled elsewhere and
documented, not re-emitted: m=0 (childless -> a point norm_num value, y-independent)
and the m>=4 collapse tail (reduces to y=T0 via the collapse monotonicity
`R3Cert.R7CollapseMono.g_mono`, the BG kernel session's brick).  conjecture1_proved = False.
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

_OUT = Path(__file__).resolve().parent / "lean" / "BGFloorFamilies.lean"

# --- verified rational constants (proof/verification/g1_floor_certificates.py) ---
_L_LO = sp.Rational(206586, 10**6)
_G_HI = sp.Rational(405466, 10**6)
_T_LO = sp.Rational(2294736, 10**7)
_T_HI = sp.Rational(2294737, 10**7)
_C = sp.Rational(11, 50)
_HALF = sp.Rational(1, 2)
_Y = sp.Symbol("y")

# (class label, nl, floor, a-range, m-values)
_CLASSES = [
    ("bareleaf", 1, sp.Rational(26, 500), range(0, 10), (1, 2, 3)),
    ("nl2", 2, sp.Rational(54, 500), range(0, 7), (1, 2, 3)),
]


def _cells():
    """(lean_name, numerator poly, lo, hi) for every (class, a, m, cell)."""
    out = []
    for label, nl, floor, arange, mvals in _CLASSES:
        for a in arange:
            for m in mvals:
                k = a + nl + m
                p = 1 + 2 * a + nl
                S = sp.Rational(a, 3) + nl + m * _Y
                u = S / (k + 1)
                log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
                cav0 = sp.Integer(1) / (k + 1 + sp.Rational(a, 3) + nl)
                Dc = sp.Max(sp.Integer(0), cav0 - _T_LO)
                below = p * _L_LO - a * _G_HI - log_ub - _C * Dc
                above = p * _L_LO - a * _G_HI - log_ub - _C * (Dc - m * (_Y - _T_HI))
                for cell, expr, lo, hi in [
                    ("below", below, sp.Integer(0), _T_HI),
                    ("above", above, _T_LO, _HALF),
                ]:
                    name = f"bg_floor_{label}_a{a}_m{m}_{cell}"
                    num = sp.expand(sp.fraction(sp.together(expr - floor))[0])
                    out.append((name, num, lo, hi))
    return out


def build() -> str:
    cells = _cells()
    names = {i: c[0] for i, c in enumerate(cells)}
    specs = {i: (c[1], c[2], c[3]) for i, c in enumerate(cells)}
    fam = bernstein_family(
        "BGFloorFamilies",
        (_Y,),
        GridSpec([("cell", list(range(len(cells))))]),
        lambda pt: names[pt["cell"]],
        spec=lambda pt: specs[pt["cell"]],
        n_max=13,
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BGFloorFamilies",)),
        [BernsteinEmitter()],
        ValidationReport(checks=(("bernstein", True),)),
    )
    text = next(iter(report.files.values()))
    # degree-5 rings; raise the heartbeat cap locally (shared emitter untouched).
    for nm in names.values():
        text = text.replace(
            f"theorem {nm}",
            f"set_option maxHeartbeats 1000000 in\ntheorem {nm}",
        )
    return text


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BGFloorFamilies.lean does not match regeneration")
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
