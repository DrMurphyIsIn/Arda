"""Generate the BoxRobust example (#1 -> #2 composition): certify -> emit -> write.

    python examples/box_robust/generate.py           # write lean/BoxRobust.lean
    python examples/box_robust/generate.py --check    # drift check (no write)

Forall-box separable-quadratic nonnegativity, certified by a rigorous rational
MONOMIAL-WISE lower bound over a rational box (`box_min_lower_bound`) and emitted
as one `nlinarith` theorem per instance.

Case 0 demonstrates the #1 -> #2 composition: the box is SOURCED from the Task-1
certified transcendental enclosure `enclose_constant("zeta(1/2)", 300)` -- a
331-bit rational interval [lo, hi] rigorously containing zeta(1/2) ~ -1.4603545
(Arb ball arithmetic; box membership is that provider's documented non-kernel
input).  Over that box we prove the separable-quadratic

    forall z, lo <= z -> z <= hi -> 0 <= z^2 - 2

i.e. zeta(1/2)^2 >= 2 on the certified enclosure (margin ~ 0.1326 > 0, since the
box lies wholly below 0 so min z^2 = hi^2 ~ 2.1326).

Case 1 exercises the bilinear corner-product path on a small clean box:

    forall u v, 1 <= u -> u <= 2 -> 1 <= v -> v <= 2 -> 0 <= u*v - 1

(margin 0, tight at the corner (1,1)).

The emitted proofs are self-contained: `nlinarith` seeded with the box's
`sq_nonneg` and corner `mul_nonneg` facts, over `Mathlib`.  conjecture1_proved=False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.arb_enclosure import enclose_constant  # noqa: E402  (Task 1: #1)
from telperion.emit_box_robust import (  # noqa: E402
    BoxRobustEmitter,
    box_robust_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "box_robust" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_OUT = Path(__file__).resolve().parent / "lean" / "BoxRobust.lean"

_z, _u, _v = sp.symbols("z u v")


def _spec(pt):
    if pt["case"] == 0:
        # #1 -> #2: box sourced from the certified zeta(1/2) enclosure.
        lo, hi = enclose_constant("zeta(1/2)", 300)
        box = [(sp.Rational(lo), sp.Rational(hi))]
        # zeta(1/2) ~ -1.46, box below 0 => z^2 >= hi^2 ~ 2.1326 > 2.
        return box, _z**2 - sp.Integer(2), (_z,)
    # Bilinear corner-product demonstration on a clean box.
    box = [(sp.Integer(1), sp.Integer(2)), (sp.Integer(1), sp.Integer(2))]
    return box, _u * _v - sp.Integer(1), (_u, _v)


_NAMES = {0: "zeta_half_sq_ge_two", 1: "box_uv_ge_one"}


def build() -> str:
    fam = box_robust_family(
        "BoxRobust",
        (),
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=_spec,
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BoxRobust",)),
        [BoxRobustEmitter()],
        ValidationReport(checks=(("box_robust", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BoxRobust.lean does not match regeneration")
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
