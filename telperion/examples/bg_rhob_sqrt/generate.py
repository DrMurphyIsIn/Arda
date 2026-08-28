"""sqrt_bracket wired into Brualdi-Goldwasser: the sqrt(2) bracket of `e2_two_rhoB_gt`.

BG's `ExactCruxes.e2_two_rhoB_gt` (`1 + sqrt 2 < 2 * rhoB`, the E2 shoulder crux) is the
one place BG needs a genuine transcendental bracket -- it hand-writes `Real.sqrt 2 < 17/12`
via `Real.sqrt_lt_sqrt`/`Real.sqrt_sq`.  That is exactly a `SqrtBracketCertificate`.  This
generator regenerates/maintains that bracket via Telperion, in the coarse `17/12` form BG
uses (so it drops straight into `e2_two_rhoB_gt`), plus the tight auto-bracket as a witness.

The rest of `e2_two_rhoB_gt` is BG-specific (`rhoB > 29/24  <=>  (29/24)^11 < 621/64`, the
11th-root clearing) and is NOT a transcendental bracket -- only the `sqrt 2` half is wired
here.  RH-toolchain reuse on a real BG constant; not RH or BG progress.  conjecture1_proved
= False.

    python3 examples/bg_rhob_sqrt/generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.sqrt_bracket import SqrtBracketCertificate  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "frozen" / "BGRhoBSqrt.lean"


def _cert_coarse():
    # the exact bound BG uses: 1 <= sqrt 2 <= 17/12  (1^2 <= 2 <= (17/12)^2 = 289/144)
    return SqrtBracketCertificate(name="bg_rhob_e2_sqrt2", qn=2, qd=1, lo=Fr(1), hi=Fr(17, 12))


def _cert_tight():
    return SqrtBracketCertificate.build(name="bg_rhob_e2_sqrt2_tight", qn=2, qd=1)


def build() -> str:
    coarse, tight = _cert_coarse(), _cert_tight()
    header = (
        "/- sqrt_bracket wired into BG: the sqrt 2 bracket of ExactCruxes.e2_two_rhoB_gt.\n"
        "   `bg_rhob_e2_sqrt2` gives `sqrt 2 <= 17/12` (BG's coarse bound) -- combined with\n"
        "   `1 + 17/12 < 2 * rhoB` (from rhoB > 29/24 via the 11th-root clearing) it yields\n"
        "   `1 + sqrt 2 <= 1 + 17/12 < 2 * rhoB`, i.e. e2_two_rhoB_gt with `<=` in place of the\n"
        "   hand-written strict `<`.  Generated + kernel-checkable (Real.sqrt_sq / sqrt_le_sqrt). -/\n"
        "import Mathlib\n\nnamespace BGRhoBSqrt\n\n"
    )
    return header + coarse.lean() + "\n" + tight.lean() + "\nend BGRhoBSqrt\n"


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
    print(f"WROTE: {OUT} (sqrt 2 <= 17/12 for e2_two_rhoB_gt, + tight witness)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
