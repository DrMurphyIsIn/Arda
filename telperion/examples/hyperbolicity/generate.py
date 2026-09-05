"""Generate the Hyperbolicity example (#3, d=2): certify -> emit -> write.

    python examples/hyperbolicity/generate.py           # write lean/Hyperbolicity.lean
    python examples/hyperbolicity/generate.py --check    # drift check (no write)

Forall-box REAL-ROOTEDNESS of a quadratic: for every quadratic whose coefficients
lie in a rational box, `roots.card = 2` (roots counted with multiplicity, the
double-root case carried by the multiset).  Certified by a rigorous rational lower
bound of the discriminant `a1^2 - 4*a2*a0` over the box (`box_min_lower_bound`, #2)
plus the leading-coefficient sign, chained into the prelude bridge lemma
`hyperbolic_deg2_of_discrim_nonneg` (this project owns it, in HyperbolicityBridge.lean).

TWO distinct real-rooted quadratics (to prove genericity), both via rational boxes:
  * x^2 - 1        (a0=-1, a1=0, a2=1;  disc = 0 - 4*(-1)*1 = 4 > 0)
  * x^2 - 3x + 2   (a0=2,  a1=-3, a2=1; disc = 9 - 8 = 1 > 0)

Each emits `∀ a0 a1 a2, (box) → (C a2*X^2 + C a1*X + C a0).roots.card = 2`, proved by
`ha : a2 ≠ 0` (box sign) + `hdisc : 0 ≤ a1^2 - 4*a2*a0` (box-robust nlinarith) +
`hyperbolic_deg2_of_discrim_nonneg`.  The emitted file imports HyperbolicityBridge.
conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_hyperbolicity import (  # noqa: E402
    HyperbolicityEmitter,
    hyperbolicity_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "hyperbolicity" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_OUT = Path(__file__).resolve().parent / "lean" / "Hyperbolicity.lean"

# case -> (coeff_box [a0, a1, a2] as (lo, hi) rational pairs, degree)
_SPECS = {
    0: ([(-1, -1), (0, 0), (1, 1)], 2),   # x^2 - 1
    1: ([(2, 2), (-3, -3), (1, 1)], 2),   # x^2 - 3x + 2
}
_NAMES = {0: "x_sq_minus_one_real_rooted", 1: "x_sq_minus_3x_plus_2_real_rooted"}


def _spec(pt):
    box, degree = _SPECS[pt["case"]]
    from fractions import Fraction as F

    return [(F(lo), F(hi)) for lo, hi in box], degree


def build() -> str:
    fam = hyperbolicity_family(
        "Hyperbolicity",
        (),
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=_spec,
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("Hyperbolicity",),
            imports=("Mathlib", "HyperbolicityBridge"),
        ),
        [HyperbolicityEmitter()],
        ValidationReport(checks=(("hyperbolicity", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: Hyperbolicity.lean does not match regeneration")
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
