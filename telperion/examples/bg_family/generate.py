"""Generate the Brualdi-Goldwasser (a, b, nu) family base-cell certificate.

    python examples/bg_family/generate.py           # write lean/BGFamily.lean
    python examples/bg_family/generate.py --check    # drift check (no write)

The heterogeneous Brualdi-Goldwasser master inequality reduces (via the vertex /
majorization lemma) to the 2-integer + 1-real canonical family

    GS(a, b, nu) = base(a+b+1, a*mu_c + b/2 + nu)^11 * glemma(1/2)^b * glemma(nu),

where a below-knee children sit at the rational knee mu_c = 37/120 (Bcap = 1),
b children sit at 1/2 (Bcap = glemma(1/2)), and one interior child sits at
nu in (mu_c, 1/2].  A finite exact scan (proof/verification/hetero_family_scan.py)
establishes the complete certificate as three bricks:

  * base cell    : GS(0, 0, nu) <= T  on [mu_c, 1/2]     (this file)
  * monotone-a   : GS(a+1, b, nu) <= GS(a, b, nu)        (worst ratio 0.99955)
  * monotone-b   : GS(a, b+1, nu) <= GS(a, b, nu)        (worst ratio 0.87370)

so GS(a, b, nu) <= GS(0, 0, nu) <= T for every a, b >= 0.  This example emits the
BASE CELL: clearing the positive denominator (1 + nu/3)^11 turns GS(0,0,nu) <= T
into the degree-11 polynomial positivity

    0 <= T*(1 + nu/3)^11 - GAMMA*((7 + 3*nu)/6)^11   on [37/120, 1/2],

certified by Telperion's Bernstein emitter (nonnegative Bernstein coefficients at
elevation 11) and discharged by the Lean kernel via `ring` + `linarith`.

Constants match the kernel `HomogMasterAssembled.lean` (W, GAMMA, T, glemma, base).
The monotone-a / monotone-b bricks are 2-integer + 1-real ratio families; their
certification (and the Mathlib convex-analysis vertex lemma that yields the whole
reduction) is documented in docs/BG_FAMILY_CERTIFICATION.md as the next layer.
"""
import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import BernsteinEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_bernstein import bernstein_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "BGFamily.lean"

# --- kernel-matched exact constants (fractions.Fraction <-> sympy.Rational) ---
_W = sp.Rational(64, 621)
_GAMMA = _W ** 2 * sp.Rational(5, 3) ** 11
_T = _W * sp.Rational(5, 3) ** 11
_KNEE = sp.Rational(37, 120)          # rational knee mu_c used by the kernel split
_HALF = sp.Rational(1, 2)

_NU = sp.Symbol("nu")


def _base_cell_poly():
    """0 <= T*(1+nu/3)^11 - GAMMA*base(1,nu)^11, with base(1,nu) = (7+3nu)/6."""
    base1 = (7 + 3 * _NU) / sp.Integer(6)
    return sp.expand(_T * (1 + _NU / 3) ** 11 - _GAMMA * base1 ** 11)


def build() -> str:
    fam = bernstein_family(
        "BGFamily",
        (_NU,),
        GridSpec([("_", [0])]),
        lambda pt: "bg_family_base_cell",
        spec=lambda pt: (_base_cell_poly(), _KNEE, _HALF),
        n_max=11,
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BGFamily",)),
        [BernsteinEmitter()],
        ValidationReport(checks=(("bernstein", True),)),
    )
    text = next(iter(report.files.values()))
    # The degree-11 `ring` identity carries ~40-digit rational coefficients and
    # can exceed Lean's default 200k-heartbeat deterministic cap.  Give it headroom
    # (a local generation step; the shared Bernstein emitter stays untouched).
    return text.replace(
        "theorem bg_family_base_cell",
        "set_option maxHeartbeats 4000000 in\ntheorem bg_family_base_cell",
    )


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BGFamily.lean does not match regeneration")
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
