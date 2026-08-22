"""Generate the Cauchy–Schwarz example: certify -> emit -> write.

    python examples/cauchy_schwarz/generate.py           # write lean/CauchySchwarz.lean
    python examples/cauchy_schwarz/generate.py --check    # drift check (no write)

Two pairwise-difference-SOS symmetric inequalities:
  - unweighted (QM-AM):  (x1+x2+x3)^2 <= 3*(x1^2+x2^2+x3^2)
  - weighted:            (x1+2x2+3x3)^2 <= 6*(x1^2+2x2^2+3x3^2)
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import CauchySchwarzEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_cs import cauchy_schwarz_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: [sp.Integer(1), sp.Integer(1), sp.Integer(1)],
    1: [sp.Integer(1), sp.Integer(2), sp.Integer(3)],
}
_NAMES = {0: "qm_am_three", 1: "weighted_three"}
_OUT = Path(__file__).resolve().parent / "lean" / "CauchySchwarz.lean"


def build() -> str:
    fam = cauchy_schwarz_family(
        "CauchySchwarz",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("CauchySchwarz",)),
        [CauchySchwarzEmitter()],
        ValidationReport(checks=(("cauchy_schwarz", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: CauchySchwarz.lean does not match regeneration")
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
