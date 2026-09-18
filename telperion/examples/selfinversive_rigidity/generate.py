"""Generate the self-inversive-rigidity example: certify -> emit -> write INTO the quasicrystal island.

    python examples/selfinversive_rigidity/generate.py           # write the island lib
    python examples/selfinversive_rigidity/generate.py --check    # drift check (no write)

The emitted Lean applies `Quasicrystal.twoFreq_realRooted_iff` (the R3(n=2) rigidity theorem), which
lives in the quasicrystal island's `TwoFreqRigidity` lib.  Per the recipe's honest fallback for a
cross-package dependency, the emitted instances are written as a NEW lib inside that island
(`SelfInversiveRigidityInstances.lean`, registered in its lakefile) and the
`selfinversive-rigidity-compiles` CI job builds that lib in the island.

Two equal-modulus instances (|c₁|² = |c₂|² exactly ⟹ real-rooted):
  - c₁ = 3/5 + 4/5 i, c₂ = 1        (|c|² = 1),  λ = 1, 2
  - c₁ = 1 + i,       c₂ = 1 − i    (|c|² = 2),  λ = 0, 3
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    SelfInversiveRigidityEmitter, ValidationReport, certify, emit,
)
from telperion.emit_selfinversive_rigidity import selfinversive_rigidity_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    0: {"c1": ("3/5", "4/5"), "c2": ("1", "0"), "lam1": "1", "lam2": "2"},
    1: {"c1": ("1", "1"), "c2": ("1", "-1"), "lam1": "0", "lam2": "3"},
}
_NAMES = {0: "rigidity_unit_modulus", 1: "rigidity_conjugate_pair"}
# Emitted INTO the quasicrystal island (which carries the TwoFreqRigidity olean cache).
_ISLAND = Path(__file__).resolve().parents[1] / "quasicrystal" / "lean"
_OUT = _ISLAND / "SelfInversiveRigidityInstances.lean"


def build() -> str:
    fam = selfinversive_rigidity_family(
        "SelfInversiveRigidityInstances",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("SelfInversiveRigidityInstances",),
                    imports=("Mathlib", "TwoFreqRigidity")),
        [SelfInversiveRigidityEmitter()],
        ValidationReport(checks=(("selfinversive_rigidity", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: SelfInversiveRigidityInstances.lean does not match regeneration")
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
