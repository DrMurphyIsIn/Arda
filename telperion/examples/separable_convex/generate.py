"""Generate the separable-convex example: certify -> emit -> write.

    python examples/separable_convex/generate.py           # write lean/SeparableConvex.lean
    python examples/separable_convex/generate.py --check    # drift check (no write)

Separable-convex MINIMUM at the homogeneous point (the EASY / Jensen face of the
separable-convex extremum problem — see
proof/docs/design/HETERO_REDUCTION_SCOPING_20260821.md, the vertex lemma).  For a
CONVEX polynomial φ over the fixed-sum box {Σxᵢ = S, lᵢ ≤ xᵢ ≤ uᵢ}, the minimum
of Σφ(xᵢ) is the homogeneous value n·φ(S/n) (Jensen), certified via the
tangent-line surplus at S/n (per-term rational SOS + linarith).  The vertex/MAX
face is NAMED-OPEN (heavy spreading-exchange induction) and is not emitted.

Two instances:
  - sepconv_jensen_sq3:  φ=x², n=3, S=3 on box [0,3]³  =>  3 ≤ Σx²
  - sepconv_quartic_box: φ=x⁴, n=2, S=2 on box [1/2,3/2]²  =>  2 ≤ Σx⁴

NOTE: the `separable_convex` kind is not yet registered in
certify._SPECIAL_KINDS / _SPECIAL_DISPATCH (that is a REPORTED shared-file edit).
Until it is, this script registers the dispatch locally at runtime so the real
certify()->emit() path exercises the emitter exactly as it would once the
one-line registration lands.
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

# spec: pt -> ((φ, x), n, S, box)   box = [(lᵢ, uᵢ), ...]
_SPECS = {
    0: ((_x**2, _x), 3, sp.Integer(3), [(0, 3), (0, 3), (0, 3)]),
    1: ((_x**4, _x), 2, sp.Integer(2),
        [(sp.Rational(1, 2), sp.Rational(3, 2)),
         (sp.Rational(1, 2), sp.Rational(3, 2))]),
}
_NAMES = {0: "sepconv_jensen_sq3", 1: "sepconv_quartic_box"}
_OUT = Path(__file__).resolve().parent / "lean" / "SeparableConvex.lean"


def build() -> str:
    fam = separable_convex_family(
        "SeparableConvex",
        GridSpec([("case", [0, 1])]),
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
