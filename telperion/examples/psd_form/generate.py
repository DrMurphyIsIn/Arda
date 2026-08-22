"""Generate the positive-definite quadratic-form example: certify -> emit -> write.

    python examples/psd_form/generate.py           # write lean/PSDForm.lean
    python examples/psd_form/generate.py --check    # drift check (no write)

Exact-LDLT PSD certificates for two explicit rational symmetric matrices:
  - a 2x2:  0 <= 2 x1^2 + 2 x1 x2 + 2 x2^2
  - a 3x3:  0 <= x^T [[4,2,0],[2,3,1],[0,1,5]] x
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import PSDFormEmitter, ValidationReport, certify, emit  # noqa: E402
from telperion.emit_psd_form import psd_form_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: [[2, 1], [1, 2]],
    1: [[4, 2, 0], [2, 3, 1], [0, 1, 5]],
}
_NAMES = {0: "psd_two", 1: "psd_three"}
_OUT = Path(__file__).resolve().parent / "lean" / "PSDForm.lean"


def build() -> str:
    fam = psd_form_family(
        "PSDForm",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("PSDForm",)),
        [PSDFormEmitter()],
        ValidationReport(checks=(("psd_form", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: PSDForm.lean does not match regeneration")
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
