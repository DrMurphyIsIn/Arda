"""Generate the disjoint-discs example: certify -> emit -> write INTO the quasicrystal island.

    python examples/disjoint_discs/generate.py           # write the island lib
    python examples/disjoint_discs/generate.py --check    # drift check (no write)

The general MIRRORMERE E4b isolation lemma (registry node ``MM_offline_disjoint_discs``) is proved
in the island's ``OfflineDiscs.lean``: SOME positive radius always works.  What the Rouche/E5 leg
consumes is the INSTANCE -- explicit strip points plus an EXPLICIT rational radius -- and that is
this example, emitted through the ``disjoint_discs`` kind (``DisjointDiscsEmitter``).

Because the emitted strip-containment proofs call the in-island lemma
``Quasicrystal.abs_re_sub_le_dist``, the instances are written as a NEW lib inside the quasicrystal
island (``OfflineDiscsInstances.lean``, registered in its lakefile), exactly as the sibling
``selfinversive_rigidity`` example does, and the ``disjoint-discs-compiles`` CI job builds it there.

Two instances:
  - ``offline_discs_online_pair``   -- two centre-line points (re = 1/2) at heights 7067/500 and
    10511/500, radius 1/50.
  - ``offline_discs_offline_bank``  -- the E5-shaped case: the same two centre-line points PLUS a
    symmetric OFF-LINE pair (re = 2/5 and re = 3/5) at height 12505/500, radius 1/50; the off-line
    pair is 1/5 apart, so a radius-1/50 disc bank isolates all four.

THE POINTS ARE INPUT, not output: nothing here asserts that zeta vanishes at any of them.  The
heights merely make the instance look like the object E5 wants to count.  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    DisjointDiscsEmitter, ValidationReport, certify, emit,
)
from telperion.emit_disjoint_discs import disjoint_discs_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_ON_LINE = [("1/2", "7067/500"), ("1/2", "10511/500")]
_OFF_LINE_BANK = _ON_LINE + [("2/5", "12505/500"), ("3/5", "12505/500")]

_SPECS = {
    0: {"points": _ON_LINE, "r": "1/50"},
    1: {"points": _OFF_LINE_BANK, "r": "1/50"},
}
_NAMES = {0: "offline_discs_online_pair", 1: "offline_discs_offline_bank"}
# Emitted INTO the quasicrystal island (which carries the OfflineDiscs olean cache).
_ISLAND = Path(__file__).resolve().parents[1] / "quasicrystal" / "lean"
_OUT = _ISLAND / "OfflineDiscsInstances.lean"


def build() -> str:
    fam = disjoint_discs_family(
        "OfflineDiscsInstances",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("OfflineDiscsInstances",),
                    imports=("Mathlib", "OfflineDiscs")),
        [DisjointDiscsEmitter()],
        ValidationReport(checks=(("disjoint_discs", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: OfflineDiscsInstances.lean does not match regeneration")
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
