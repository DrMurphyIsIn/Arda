"""Generate the magnitude-split example: certify -> emit -> write.

    python examples/magnitude_split/generate.py           # write lean/MagnitudeSplit.lean
    python examples/magnitude_split/generate.py --check    # drift check (no write)

Three triangle-inequality magnitude-split instances for `‖A + B − C‖ ≤ α+β+γ`
(the final assembly of `zeta_log_bound`):
  - abc_universal:  the clean universally-quantified `‖A+B−C‖ ≤ α+β+γ`
  - abc_concrete:   concrete rational bounds α=1+log-style placeholders 1/1/4
                    (`(α : ℝ)` ascription avoids the ℤ-default pitfall)
  - nterm_alt:      general signed sum `‖t1 − t2 + t3 − t4‖ ≤ b1+b2+b3+b4`

NOTE: the `magnitude_split` kind is registered in certify._SPECIAL_KINDS /
_SPECIAL_DISPATCH as a REPORTED shared-file edit.  This script registers the
dispatch locally at runtime as a fallback so the real certify()->emit() path
exercises the emitter exactly as it would once the one-line registration lands.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402

from telperion.emit_magnitude_split import (  # noqa: E402
    MagnitudeSplitBoundEmitter,
    magnitude_split_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> bounds  (or dict with shape/signs/concrete)
_SPECS = {
    0: [1, 1, 1],
    1: {"bounds": [sp.Integer(1), sp.Integer(1), sp.Integer(4)],
        "shape": "abc", "concrete": True},
    2: {"bounds": [sp.Integer(1), sp.Integer(2), sp.Integer(3), sp.Integer(4)],
        "shape": "nterm", "signs": [1, -1, 1, -1]},
}
_NAMES = {0: "magsplit_abc_universal", 1: "magsplit_abc_concrete", 2: "magsplit_nterm_alt"}
_OUT = Path(__file__).resolve().parent / "lean" / "MagnitudeSplit.lean"


def build() -> str:
    fam = magnitude_split_family(
        "MagnitudeSplit",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("MagnitudeSplit",)),
        [MagnitudeSplitBoundEmitter()],
        ValidationReport(checks=(("magnitude_split", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: MagnitudeSplit.lean does not match regeneration")
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
