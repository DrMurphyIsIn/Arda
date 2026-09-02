"""Generate the half-plane -> disk example: certify -> emit -> write.

    python examples/halfplane_disk/generate.py           # write lean/HalfPlaneDisk.lean
    python examples/halfplane_disk/generate.py --check    # drift check (no write)

The Moebius half-plane -> disk positivity core (Borel-Caratheodory / Moebius-Schwarz):
for a strictly positive rational B, `Re w ≤ B  ⟹  ‖w / (2B − w)‖ ≤ 1`.  Instances:
  - B = 1     (core only)
  - B = 2     (core only)
  - B = 1/2   (core + inversion + reverse-triangle companions)

NOTE: the `halfplane_disk` kind is a NEW first-class emitter.  Until the two
registration lines are added to `src/telperion/certify.py` (`_SPECIAL_KINDS` and
`_SPECIAL_DISPATCH`), this generator registers them at runtime below so the
example is self-contained.  The exact lines to add permanently are reported in
the emitter delivery notes.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

# kind "halfplane_disk" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_halfplane_disk import (  # noqa: E402
    HalfPlaneDiskEmitter,
    halfplane_disk_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec(pt) -> B, or {"B":.., "inv":bool, "reverse":bool} to add companion lemmas.
_SPECS = {
    0: sp.Integer(1),
    1: sp.Integer(2),
    2: {"B": sp.Rational(1, 2), "inv": True, "reverse": True},
}
_NAMES = {0: "halfplane_disk_one", 1: "halfplane_disk_two", 2: "halfplane_disk_half"}
_OUT = Path(__file__).resolve().parent / "lean" / "HalfPlaneDisk.lean"


def build() -> str:
    fam = halfplane_disk_family(
        "HalfPlaneDisk",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("HalfPlaneDisk",)),
        [HalfPlaneDiskEmitter()],
        ValidationReport(checks=(("halfplane_disk", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: HalfPlaneDisk.lean does not match regeneration")
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
