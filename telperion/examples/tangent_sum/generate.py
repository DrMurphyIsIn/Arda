"""Generate the tangent-line-trick example: certify -> emit -> write.

    python examples/tangent_sum/generate.py           # write lean/TangentSum.lean
    python examples/tangent_sum/generate.py --check    # drift check (no write)

Two convex-quadratic symmetric-sum inequalities via the tangent line at S/n:
  - Jensen for squares:  x1+x2+x3 = 3  =>  3 <= x1^2 + x2^2 + x3^2
  - a shifted quadratic: x1+x2 = 4     => 14 <= f(x1)+f(x2), f = 2x^2-3x+5
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import TangentSumEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_tangent import tangent_sum_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_x = sp.Symbol("x")
_SPECS = {
    0: ((_x**2, _x), 3, sp.Integer(3)),                 # Jensen for squares
    1: ((2 * _x**2 - 3 * _x + 5, _x), 2, sp.Integer(4)),  # a shifted quadratic
    2: ((_x**4, _x), 2, sp.Integer(2)),                 # convex quartic (deg 4)
}
_NAMES = {0: "jensen_sq", 1: "quad_shift", 2: "quartic_two"}
_OUT = Path(__file__).resolve().parent / "lean" / "TangentSum.lean"


def build() -> str:
    fam = tangent_sum_family(
        "TangentSum",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    certified = certify(fam)
    report = emit(
        certified,
        LeanProfile(namespace=("TangentSum",)),
        [TangentSumEmitter()],
        ValidationReport(checks=(("tangent", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: TangentSum.lean does not match regeneration")
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
