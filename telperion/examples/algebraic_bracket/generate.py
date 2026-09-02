"""Generate the AlgebraicBracket example: certify -> emit -> write.

    python examples/algebraic_bracket/generate.py           # write lean/AlgebraicBracket.lean
    python examples/algebraic_bracket/generate.py --check    # drift check (no write)

Rigorous rational two-sided enclosures of a square root  lo <= √a <= hi,
certified by the exact rational facts  0 <= lo,  lo^2 <= a,  a <= hi^2:
  - √2:  1     <= √2  <= 17/12   (1 <= 2 <= 289/144)   -- the BG e2_two_rhoB crux
  - √3:  12/7  <= √3  <= 7/4     (144/49 <= 3 <= 49/16)
  - √23: 14/3  <= √23 <= 24/5    (196/9 <= 23 <= 576/25) -- BG-relevant (621/64 = 27*23)

The emitted Lean uses only Real.le_sqrt_of_sq_le + Real.sqrt_le_iff (Mathlib
v4.32.0), with the three rational side-goals closed by norm_num.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_algebraic_bracket import (  # noqa: E402
    AlgebraicBracketEmitter,
    algebraic_bracket_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "algebraic_bracket" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_SPECS = {
    0: (sp.Integer(2), sp.Integer(1), sp.Rational(17, 12)),
    1: (sp.Integer(3), sp.Rational(12, 7), sp.Rational(7, 4)),
    2: (sp.Integer(23), sp.Rational(14, 3), sp.Rational(24, 5)),
}
_NAMES = {0: "sqrt_two", 1: "sqrt_three", 2: "sqrt_twentythree"}
_OUT = Path(__file__).resolve().parent / "lean" / "AlgebraicBracket.lean"


def build() -> str:
    fam = algebraic_bracket_family(
        "AlgebraicBracket",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("AlgebraicBracket",)),
        [AlgebraicBracketEmitter()],
        ValidationReport(checks=(("algebraic_bracket", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: AlgebraicBracket.lean does not match regeneration")
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
