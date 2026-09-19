"""Generate the twofreq-offline example: certify -> emit -> write INTO the quasicrystal island.

    python examples/twofreq_offline/generate.py           # write the island lib
    python examples/twofreq_offline/generate.py --check   # drift check (no write)

The emitted Lean applies `Quasicrystal.twoFreq_realRooted_iff` (the R3(n=2) rigidity
theorem) in its NOT-real-rooted direction, so -- exactly as for the sibling
`selfinversive_rigidity` example -- the instances are written as a NEW lib inside the
quasicrystal island (`EulerFactorSectionOffline.lean`, registered in its lakefile) and the
`twofreq-offline-compiles` CI job builds that lib there.

Instances: the Euler factor `1 - p^(-s)` read on `s = 1/2 + i x` at p = 2, 3, 5, in both
modes -- the p = 2 and p = 3 rungs in 'displacement' mode (which additionally certifies
that EVERY zero sits at `Im x = 1/2`), and p = 5 in plain 'offline' mode.

The p = 2 theorem is named `euler_factor_section_offline` and its statement is
byte-identical (modulo the missions normalizer) to the MIRRORMERE registry node
`MM_euler_factor_section_offline`; `tests/test_emit_twofreq_offline.py` pins that.

conjecture1_proved = False -- a finite fact about single Euler factors, at fixed primes.
Nothing here is about zeta, the Euler product, or RH; on the contrary, it certifies that
per-rung line-membership FAILS, so critical-line membership can only be an infinite-N
continuation phenomenon.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    TwoFreqOfflineEmitter, ValidationReport, certify, emit,
)
from telperion.emit_twofreq_offline import (  # noqa: E402
    euler_factor_spec, twofreq_offline_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_SPECS = {
    2: euler_factor_spec(2, mode="displacement"),
    3: euler_factor_spec(3, mode="displacement"),
    5: euler_factor_spec(5, mode="offline"),
}
# p = 2 carries the MIRRORMERE node's exact theorem name.
_NAMES = {2: "euler_factor_section_offline",
          3: "euler_factor_section_offline_p3",
          5: "euler_factor_section_offline_p5"}
_ISLAND = Path(__file__).resolve().parents[1] / "quasicrystal" / "lean"
_OUT = _ISLAND / "EulerFactorSectionOffline.lean"


def build() -> str:
    fam = twofreq_offline_family(
        "EulerFactorSectionOffline",
        GridSpec([("p", [2, 3, 5])]),
        lambda pt: _NAMES[pt["p"]],
        spec=lambda pt: _SPECS[pt["p"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(namespace=("EulerFactorSectionOffline",),
                    imports=("Mathlib", "TwoFreqRigidity"),
                    prelude="open Quasicrystal\n"),
        [TwoFreqOfflineEmitter()],
        ValidationReport(checks=(("twofreq_offline", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: EulerFactorSectionOffline.lean does not match regeneration")
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
