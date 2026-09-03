"""Generate the separable-convex example: certify -> emit -> write.

    python examples/separable_convex/generate.py           # write lean/SeparableConvex.lean
    python examples/separable_convex/generate.py --check    # drift check (no write)

Both FACES of the separable-convex extremum on the fixed-sum box (see
proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md, the vertex lemma, and the
proven proof/formalization/R3Cert/VertexLemma.lean / VertexLemmaFull.lean):

  * MIN (homogeneous / Jensen face): for a CONVEX polynomial φ over the fixed-sum
    box {Σxᵢ = S, lᵢ ≤ xᵢ ≤ uᵢ}, the minimum of Σφ(xᵢ) is n·φ(S/n), certified via
    the tangent-line surplus at S/n (per-term rational SOS + linarith).

  * MAX (vertex face): for a CONVEX polynomial φ (even degree ≤ 6) over the
    UNIFORM box {Σxᵢ = S, l ≤ xᵢ ≤ u}, the maximum of Σφ(xᵢ) is the vertex value
    (n−1)·φ(u) + φ(S−(n−1)·u) — push n−1 coords to the bound u, the last carries
    the residual.  Certified via the chained push-to-bound exchanges
    φ(a)+φ(b) ≤ φ(a+b−u)+φ(u) (each an nlinarith fact from the box slacks), the
    parameterization of the proven VertexLemmaFull.glemma_push_to_bound /
    vertex_bound chain (glemma / cap-1/2 replaced by φ / bound u).

Five instances:
  - sepconv_jensen_sq3   (MIN): φ=x², n=3, S=3 on box [0,3]³      =>  3 ≤ Σx²
  - sepconv_quartic_box  (MIN): φ=x⁴, n=2, S=2 on box [1/2,3/2]²  =>  2 ≤ Σx⁴
  - sepconv_max_sq3      (MAX): φ=x², n=3, S=6 on box [0,3]³      =>  Σx² ≤ 18
  - sepconv_max_quartic  (MAX): φ=x⁴, n=3, S=5 on box [0,2]³      =>  Σx⁴ ≤ 33
  - sepconv_max_deg6     (MAX): φ=x⁶+x², n=2, S=3 on box [1,2]²   =>  Σφ ≤ 70

NOTE: the `separable_convex` kind is registered in certify._SPECIAL_KINDS /
_SPECIAL_DISPATCH (both min and max dispatch through the same
certify_separable_convex_point).  This script exercises the real certify()->emit()
path for both faces.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402


from telperion import ValidationReport, certify, emit  # noqa: E402

# NB: the package re-exports certify() as a FUNCTION over the submodule name, so
# `telperion.certify` resolves to the function.  Grab the certify SUBMODULE (which
# owns _SPECIAL_KINDS / _SPECIAL_DISPATCH) explicitly via importlib.
from telperion.emit_separable_convex import (  # noqa: E402
    SeparableConvexExtremumEmitter,
    separable_convex_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


_x = sp.Symbol("x")

# spec: pt -> ((φ, x), n, S, box[, mode])   box = [(lᵢ, uᵢ), ...], mode "min"/"max"
_SPECS = {
    # MIN / homogeneous face
    0: ((_x**2, _x), 3, sp.Integer(3), [(0, 3), (0, 3), (0, 3)]),
    1: ((_x**4, _x), 2, sp.Integer(2),
        [(sp.Rational(1, 2), sp.Rational(3, 2)),
         (sp.Rational(1, 2), sp.Rational(3, 2))]),
    # MAX / vertex face
    2: ((_x**2, _x), 3, sp.Integer(6), [(0, 3), (0, 3), (0, 3)], "max"),
    3: ((_x**4, _x), 3, sp.Integer(5), [(0, 2), (0, 2), (0, 2)], "max"),
    4: ((_x**6 + _x**2, _x), 2, sp.Integer(3), [(1, 2), (1, 2)], "max"),
}
_NAMES = {
    0: "sepconv_jensen_sq3", 1: "sepconv_quartic_box",
    2: "sepconv_max_sq3", 3: "sepconv_max_quartic", 4: "sepconv_max_deg6",
}
_OUT = Path(__file__).resolve().parent / "lean" / "SeparableConvex.lean"


def build() -> str:
    fam = separable_convex_family(
        "SeparableConvex",
        GridSpec([("case", [0, 1, 2, 3, 4])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SeparableConvex",)),
        [SeparableConvexExtremumEmitter()],
        ValidationReport(checks=(("separable_convex", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SeparableConvex.lean does not match regeneration")
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
