"""Generate the disk-coordinate-bounds example: certify -> emit -> write.

    python examples/disk_coord/generate.py           # write lean/DiskCoord.lean
    python examples/disk_coord/generate.py --check    # drift check (no write)

Three Farkas-style disk -> coordinate-bounds instances: from
`z ∈ Metric.closedBall (wr + wi·I) ρ` derive `wr∓ρ ≤ z.re` and `wi∓ρ ≤ z.im`.
  - c_2_3i:     center 2 + 3i,      radius 1/2
  - c_neg_half: center -1/2 + i,    radius 1
  - c_origin:   center (5/4)i,      radius 3/2

NOTE: the `disk_coord` kind is not yet registered in certify._SPECIAL_KINDS
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

# the certify SUBMODULE (not the re-exported certify() function) — its dispatch
from telperion.emit_disk_coord import (  # noqa: E402
    DiskCoordBoundsEmitter,
    disk_coord_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> (wr, wi, rho)
_SPECS = {
    0: (sp.Integer(2), sp.Integer(3), sp.Rational(1, 2)),
    1: (sp.Rational(-1, 2), sp.Integer(1), sp.Integer(1)),
    2: (sp.Integer(0), sp.Rational(5, 4), sp.Rational(3, 2)),
}
_NAMES = {0: "disk_coord_2_3i", 1: "disk_coord_neg_half", 2: "disk_coord_origin"}
_OUT = Path(__file__).resolve().parent / "lean" / "DiskCoord.lean"


def build() -> str:
    fam = disk_coord_family(
        "DiskCoord",
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("DiskCoord",)),
        [DiskCoordBoundsEmitter()],
        ValidationReport(checks=(("disk_coord", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: DiskCoord.lean does not match regeneration")
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
