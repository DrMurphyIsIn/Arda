"""Generate the cauchy-deriv example: certify -> emit -> write.

    python examples/cauchy_deriv/generate.py           # write lean/CauchyDeriv.lean
    python examples/cauchy_deriv/generate.py --check    # drift check (no write)

Three Cauchy derivative-estimate instances:
  - cd_half:     main wrapper, R=1/2, M=12  (the `zeta_deriv_bound` shape:
                 ‖ζ'‖ ≤ 12γ/(1/2) = 24γ on the radius-1/2 disk)
  - cd_two_one:  constant companion, R=2, r=1  ((2(r+ρ')/(R−(r+ρ')))·(1/ρ')
                 = 4(R+r)/(R−r)² at ρ'=(R−r)/2)
  - cd_both:     main wrapper + constant companion, R=1, M=3, r=1/2

NOTE: the `cauchy_deriv` kind is not yet registered in certify._SPECIAL_KINDS
(that is a REPORTED shared-file edit).  Until it lands, this script registers the
dispatch locally at runtime so the real certify()->emit() path exercises the
emitter exactly as it would once the one-line registration is in place.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))


import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402

# the certify SUBMODULE (not the re-exported certify() function) — its dispatch
from telperion.emit_cauchy_deriv import (  # noqa: E402
    CauchyDerivBoundEmitter,
    cauchy_deriv_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> dict selecting main wrapper / constant companion
_SPECS = {
    0: {"R": sp.Rational(1, 2), "M": sp.Integer(12)},
    1: {"R": sp.Integer(2), "r": sp.Integer(1), "main": False, "const": True},
    2: {"R": sp.Integer(1), "M": sp.Integer(3), "r": sp.Rational(1, 2),
        "main": True, "const": True},
}
_NAMES = {0: "cd_half", 1: "cd_two_one", 2: "cd_both"}
_OUT = Path(__file__).resolve().parent / "lean" / "CauchyDeriv.lean"


def build() -> str:
    fam = cauchy_deriv_family(
        "CauchyDeriv",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("CauchyDeriv",)),
        [CauchyDerivBoundEmitter()],
        ValidationReport(checks=(("cauchy_deriv", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: CauchyDeriv.lean does not match regeneration")
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
