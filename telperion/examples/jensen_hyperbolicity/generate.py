"""Generate the d=2 Jensen box-hyperbolicity Lean certificate(s).

conjecture1_proved = False. Emits JensenHyperbolicity.lean: for each offset n,
a theorem that every degree-2 Jensen polynomial in the certified rational
coefficient box is hyperbolic (real-root multiset cardinality = 2). The proof
chains a box-positivity discriminant bound into the Task-4 bridge lemma
`hyperbolic_deg2_of_discrim_nonneg`. NOT a proof of RH.

The emitter REFUSES (ValueError) any box whose discriminant lower bound is
non-positive (not certifiably hyperbolic) or whose leading coefficient straddles
zero (cannot prove c2 != 0).

Usage: generate.py            # (re)write JensenHyperbolicity.lean
       generate.py --check    # verify the on-disk file matches a fresh render
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.emit_jensen_polynomial_hyperbolicity import (  # noqa: E402
    JensenPolynomialHyperbolicityEmitter,
)
from telperion.rh_jensen.jensen import jensen_coeff_box  # noqa: E402

HERE = Path(__file__).resolve().parent
TARGET = HERE / "lean" / "JensenHyperbolicity.lean"

# Offsets to certify. n=0 is warm-verified to build GREEN.
OFFSETS = [0]
PREC_BITS = 300

HEADER = """/-
Jensen-Polya hyperbolicity: d=2 box-hyperbolicity certificates (Task 5).

conjecture1_proved = False. Emitted by JensenPolynomialHyperbolicityEmitter.
Each theorem asserts that every degree-2 Jensen polynomial in a certified
rational coefficient box is hyperbolic (real-root multiset cardinality = degree).
The proof chains a box-positivity discriminant bound into the d=2 bridge lemma
hyperbolic_deg2_of_discrim_nonneg (JensenBridge.lean). NOT a proof of RH.
-/
import Mathlib
import JensenBridge

open Polynomial

"""


def render() -> str:
    em = JensenPolynomialHyperbolicityEmitter(degree=2)
    bodies: list[str] = []
    axiom_checks: list[str] = []
    for n in OFFSETS:
        box = jensen_coeff_box(n=n, d=2, prec_bits=PREC_BITS)
        text, count = em.render_box(n=n, box=box)
        assert count == 1
        bodies.append(text)
        axiom_checks.append(f"#print axioms jensen_box_hyperbolic_deg2_{n}")
    return HEADER + "\n".join(bodies) + "\n\n" + "\n".join(axiom_checks) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    fresh = render()
    if args.check:
        on_disk = TARGET.read_text() if TARGET.exists() else ""
        ok = on_disk == fresh
        print("check:", "OK" if ok else "FAILED (regenerate with generate.py)")
        return 0 if ok else 1
    TARGET.write_text(fresh)
    print(f"JensenHyperbolicity: wrote {len(OFFSETS)} cert(s) to {TARGET}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
