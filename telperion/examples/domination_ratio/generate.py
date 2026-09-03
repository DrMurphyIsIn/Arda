"""Generate the domination-ratio example: certify -> emit -> write.

    python examples/domination_ratio/generate.py           # write lean/DominationRatio.lean
    python examples/domination_ratio/generate.py --check    # drift check (no write)

Rational domination ratio r = P/Q ≥ 1 on a parameter box — the multivariate-
envelope generalization of the shipped finite-argmax margin.  A template T_tmpl
dominates a competitor T (Φ(T) ≤ Φ(T_tmpl)) via an all-nonneg-coefficient
rational ratio r = P/Q ≥ 1; cross-multiplied (Q > 0) it is the polynomial
box-positivity fact P − Q ≥ 0, certified for a MULTI-AFFINE D = P − Q by the
k-variable corner principle (the generalization of examples/bilinear_corner).

Two instances:
  - dr_two_param:  Q = 1 + x + y + x*y,  P = 2(1 + x + y + x*y) on [0,1]^2;
                   D = P − Q = Q ≥ 0 (ratio exactly 2 ≥ 1), corners 1,2,2,4.
  - dr_mixed_slope: Q = 2 + x + 2y,  P = 5 + x*y on [0,1]^2; D = 3 − x − 2y + x*y,
                   a genuine mixed-slope multi-affine bracket, corners 3,1,2,1.

NOTE: the `domination_ratio` kind is not registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it is, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402


from telperion import ValidationReport, certify, emit  # noqa: E402

from telperion.emit_domination_ratio import (  # noqa: E402
    RecursiveDominationRatioEmitter,
    domination_ratio_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402


x, y = sp.symbols("x y")

# spec: pt -> (P, Q, box)  with box a sequence of (l_i, u_i) per symbol.
_SPECS = {
    0: (2 + 2 * x + 2 * y + 2 * x * y, 1 + x + y + x * y, ((0, 1), (0, 1))),
    1: (5 + x * y, 2 + x + 2 * y, ((0, 1), (0, 1))),
}
_NAMES = {0: "dr_two_param", 1: "dr_mixed_slope"}
_OUT = Path(__file__).resolve().parent / "lean" / "DominationRatio.lean"


def build() -> str:
    fam = domination_ratio_family(
        "DominationRatio",
        (x, y),
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("DominationRatio",)),
        [RecursiveDominationRatioEmitter()],
        ValidationReport(checks=(("domination_ratio", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: DominationRatio.lean does not match regeneration")
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
