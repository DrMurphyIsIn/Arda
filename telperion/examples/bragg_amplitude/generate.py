"""Generate the Bragg-amplitude example: certify -> emit -> write INTO the zeta island.

    python examples/bragg_amplitude/generate.py           # write the island lib
    python examples/bragg_amplitude/generate.py --check    # drift check (no write)

The emitted Lean uses `CosEnclosure` (order-4 base bracket + Lipschitz `cos_encl_bracket` + interval
`add_encl`), which lives in the zeta_zero_localization island.  Rather than a fragile cross-package
`require`, we follow the recipe's honest fallback: the emitted instances are written as a NEW lib
inside that island (`BraggAmplitudeInstances.lean`, registered in its lakefile), and the
`bragg-amplitude-compiles` CI job builds that lib in the island (which already carries the CosEnclosure
olean cache).  This is the SAME shape BraggH100 uses — a base-case (3-ordinate, |c|≤1) instance of the
29-zero `bragg_amplitude_h100` fold.

Two instances:
  - a 3-ordinate sum at u = 3/2 in [0, 3]
  - a 2-ordinate sum at u = 1   in [0, 2]
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    BraggAmplitudeEmitter, ValidationReport, certify, emit,
)
from telperion.emit_bragg_amplitude import bragg_amplitude_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: {"brackets": [("1/2", "51/100"), ("3/5", "61/100"), ("2/5", "41/100")],
        "u": "3/2", "A": "0", "B": "3"},
    1: {"brackets": [("1/2", "51/100"), ("3/5", "61/100")],
        "u": "1", "A": "0", "B": "2"},
}
_NAMES = {0: "bragg_three_u32", 1: "bragg_two_u1"}
# Emitted INTO the zeta island (which carries the CosEnclosure olean cache).
_ISLAND = Path(__file__).resolve().parents[1] / "zeta_zero_localization" / "lean"
_OUT = _ISLAND / "BraggAmplitudeInstances.lean"


def build() -> str:
    fam = bragg_amplitude_family(
        "BraggAmplitudeInstances",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("BraggAmplitudeInstances",), imports=("Mathlib", "CosEnclosure")),
        [BraggAmplitudeEmitter()],
        ValidationReport(checks=(("bragg_amplitude", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BraggAmplitudeInstances.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
