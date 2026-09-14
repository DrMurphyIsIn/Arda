"""Generate the defect-witness example: certify -> emit -> write.

    python examples/defect_witness/generate.py           # write lean/DefectWitness.lean
    python examples/defect_witness/generate.py --check    # drift check (no write)

Two two-configuration inertia gaps (the MIRRORMERE BraggDefect shape, self-contained on the given
rational excess brackets — no Arb `exp` hypothesis):
  - the BraggDefect δ=1/10 pair:  excess ∈ [1/10, 11/100]  ->  q ∈ [-121/10000, -1/100] < 0 = q(0)
  - a wider δ pair:               excess ∈ [1/5, 21/100]   ->  q ∈ [-441/10000, -1/25] < 0 = q(0)
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    DefectWitnessEmitter, ValidationReport, certify, emit,
)
from telperion.emit_defect_witness import defect_witness_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: {"d_lo": "1/10", "d_hi": "11/100"},
    1: {"d_lo": "1/5", "d_hi": "21/100"},
}
_NAMES = {0: "defect_delta_tenth", 1: "defect_delta_fifth"}
_OUT = Path(__file__).resolve().parent / "lean" / "DefectWitness.lean"


def build() -> str:
    fam = defect_witness_family(
        "DefectWitness",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("DefectWitness",)),
        [DefectWitnessEmitter()],
        ValidationReport(checks=(("defect_witness", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: DefectWitness.lean does not match regeneration")
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
