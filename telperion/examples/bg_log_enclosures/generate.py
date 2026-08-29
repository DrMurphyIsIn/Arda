"""TightLogCertificate wired into BG: the sweep-constant log enclosures of R3Cert/Sweep.lean.

BG's `s`-tail sweep (`R3Cert/Sweep.lean`) proves tight rational enclosures of `log(3/2)`
and `log(4/3)` -- `405/1000 < log(3/2) < 406/1000` and `287/1000 < log(4/3) < 288/1000`
-- by range-reducing onto Mathlib's decimal constants `Real.log_{two,three}_{gt,lt}_d9`
and `nlinarith`.  That is exactly a `TightLogCertificate` (basis {log 2, log 3}).  This
generator regenerates/maintains both enclosures via Telperion, in BG's exact `/1000` form
so they drop straight back into the sweep.

The COARSE `LogBoundCertificate` (`1 - d/n <= log <= n/d - 1`) cannot reproduce these --
its log(3/2) bracket is [1/3, 1/2], far wider than BG's [0.405, 0.406].  The tight emitter
computes the enclosure from the d9 interval box, rounded outward to /1000, reproducing BG's
windows exactly.  RH-toolchain reuse on real BG constants; NOT RH or BG progress.
conjecture1_proved = False.

    python3 examples/bg_log_enclosures/generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.tight_log import TightLogCertificate  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGLogEnclosures.lean"

# BG's sweep constants (R3Cert/Sweep.lean): name -> (n, d)
CONSTANTS = [
    ("log_three_half_enclosure", 3, 2),
    ("log_four_third_enclosure", 4, 3),
]


def build() -> str:
    certs = [TightLogCertificate(name=nm, n=n, d=d) for nm, n, d in CONSTANTS]
    body = "\n\n".join(c.lean().rstrip() for c in certs)
    header = (
        "/- TightLogCertificate wired into BG: the sweep-constant log enclosures of\n"
        "   R3Cert/Sweep.lean (log_three_half_enclosure, log_four_third_enclosure).\n"
        "   Tight rational enclosures of log(3/2), log(4/3) over the {log 2, log 3} basis,\n"
        "   from Mathlib's Real.log_{two,three}_{gt,lt}_d9 decimal constants + nlinarith --\n"
        "   BG's exact /1000 windows, regenerated + kernel-checkable. -/\n"
        "import Mathlib\n\nnamespace BGLogEnclosures\n\n"
    )
    return header + body + "\n\nend BGLogEnclosures\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    src = build()
    if args.check:
        if not OUT.exists():
            print(f"MISSING: {OUT}")
            return 1
        if OUT.read_text() != src:
            print(f"DRIFT: {OUT} differs from freshly generated output")
            return 1
        print(f"OK: {OUT} matches")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(src)
    print(f"WROTE: {OUT} ({len(CONSTANTS)} BG sweep log enclosures)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
