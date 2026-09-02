"""Generate the logderiv-region example: certify -> emit -> write.

    python examples/logderiv_region/generate.py           # write lean/LogDerivRegion.lean
    python examples/logderiv_region/generate.py --check    # drift check (no write)

Two de la Vallee Poussin log-derivative region-core instances (ported from the
kernel-checked `dlvp_core_estimate` / `dlvp_region_gap` in ZeroFreeRegion.lean,
with the `-Re ζ'/ζ` values abstracted to reals so the emitted lemmas are
Mathlib-only):
  - dlvp_region_unit:   A=1, L=1, k=1   (the standard normalized dVP constants)
  - dlvp_region_A2L3k2: A=2, L=3, k=2   (an order-2 zero, larger constants)

NOTE: the `logderiv_region` kind is not yet registered in certify._SPECIAL_KINDS
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
from telperion.emit_logderiv_region import (  # noqa: E402
    LogDerivRegionCoreEmitter,
    logderiv_region_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# spec: pt -> (A, L, k)
_SPECS = {
    0: (sp.Integer(1), sp.Integer(1), sp.Integer(1)),
    1: (sp.Integer(2), sp.Integer(3), sp.Integer(2)),
}
_NAMES = {0: "dlvp_region_unit", 1: "dlvp_region_A2L3k2"}
_OUT = Path(__file__).resolve().parent / "lean" / "LogDerivRegion.lean"


def build() -> str:
    fam = logderiv_region_family(
        "LogDerivRegion",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("LogDerivRegion",)),
        [LogDerivRegionCoreEmitter()],
        ValidationReport(checks=(("logderiv_region", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LogDerivRegion.lean does not match regeneration")
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
