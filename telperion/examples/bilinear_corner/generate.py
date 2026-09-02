"""Generate the bilinear-corner example: certify -> emit -> write.

    python examples/bilinear_corner/generate.py           # write lean/BilinearCorner.lean
    python examples/bilinear_corner/generate.py --check    # drift check (no write)

Three worst-corner box-positivity instances for 0 ≤ A + B·s + C·t + E·(s·t) on
[s0,s1]×[t0,t1] (all four corner values ≥ 0):
  - product_unit:  f = 1 + s + t + s·t   = (1+s)(1+t)  on [0,1]²
  - mixed_slopes:  f = 3 − s − 2t + s·t                on [0,1]²   (E flips t-slope)
  - shifted_box:   f = (1/2) + s − t + 2·s·t           on [1/2,1]×[0,1]

NOTE: the `bilinear_corner` kind is not yet registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it is, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

import importlib  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (not the re-exported certify() function) — its dispatch
# tables get the local registration below.
_certify_mod = importlib.import_module("telperion.certify")
from telperion.emit_bilinear_corner import (  # noqa: E402
    BilinearCornerBoxEmitter,
    bilinear_corner_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# --- local registration (mirrors the reported one-line certify.py edits) ------
if "bilinear_corner" not in _certify_mod._SPECIAL_KINDS:
    _certify_mod._SPECIAL_KINDS = _certify_mod._SPECIAL_KINDS + ("bilinear_corner",)
_certify_mod._SPECIAL_DISPATCH.setdefault(
    "bilinear_corner", ("emit_bilinear_corner", "certify_bilinear_corner_point")
)

# spec: pt -> (A, B, C, E, s0, s1, t0, t1)
_SPECS = {
    0: (sp.Integer(1), sp.Integer(1), sp.Integer(1), sp.Integer(1),
        sp.Integer(0), sp.Integer(1), sp.Integer(0), sp.Integer(1)),
    1: (sp.Integer(3), sp.Integer(-1), sp.Integer(-2), sp.Integer(1),
        sp.Integer(0), sp.Integer(1), sp.Integer(0), sp.Integer(1)),
    2: (sp.Rational(1, 2), sp.Integer(1), sp.Integer(-1), sp.Integer(2),
        sp.Rational(1, 2), sp.Integer(1), sp.Integer(0), sp.Integer(1)),
}
_NAMES = {0: "bc_product_unit", 1: "bc_mixed_slopes", 2: "bc_shifted_box"}
_OUT = Path(__file__).resolve().parent / "lean" / "BilinearCorner.lean"


def build() -> str:
    fam = bilinear_corner_family(
        "BilinearCorner",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BilinearCorner",)),
        [BilinearCornerBoxEmitter()],
        ValidationReport(checks=(("bilinear_corner", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BilinearCorner.lean does not match regeneration")
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
