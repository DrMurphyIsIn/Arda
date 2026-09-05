"""Generate the d=2 Jensen box-hyperbolicity Lean certificate(s).

conjecture1_proved = False. Emits JensenHyperbolicity.lean: for each offset n,
a theorem that every degree-2 Jensen polynomial in the certified rational
coefficient box is hyperbolic (real-root multiset cardinality = 2). The proof
chains a box-positivity discriminant bound into the Task-4 bridge lemma
`hyperbolic_deg2_of_discrim_nonneg`. NOT a proof of RH.

The emitter REFUSES (ValueError) any box whose discriminant lower bound is
non-positive (not certifiably hyperbolic) or whose leading coefficient straddles
zero (cannot prove c2 != 0).

Usage:
    generate.py                          # (re)write JensenHyperbolicity.lean (d=2, n=0)
    generate.py --degree 2 --n 0        # explicit; same as default
    generate.py --prec 300              # set Arb precision bits (default 300)
    generate.py --check                 # verify on-disk file matches a fresh render
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.emit_jensen_polynomial_hyperbolicity import (  # noqa: E402
    JensenPolynomialHyperbolicityEmitter,
)
from telperion.rh_jensen.jensen import disc2_margin, jensen_coeff_box  # noqa: E402

HERE = Path(__file__).resolve().parent
TARGET = HERE / "lean" / "JensenHyperbolicity.lean"

HEADER = """/-
Jensen-Polya hyperbolicity: d=2 box-hyperbolicity certificates (Task 6).

conjecture1_proved = False. Emitted by JensenPolynomialHyperbolicityEmitter.
Each theorem asserts that every degree-2 Jensen polynomial in a certified
rational coefficient box is hyperbolic (real-root multiset cardinality = degree).
The proof chains a box-positivity discriminant bound into the d=2 bridge lemma
hyperbolic_deg2_of_discrim_nonneg (JensenBridge.lean). NOT a proof of RH.

Each theorem is followed by an AXLE statement-match example that the Lean kernel
verifies: the example ascribes the exact box-hyperbolicity type to the theorem,
so the build fails if the emitted Prop does not match the intended statement.
-/
import Mathlib
import JensenBridge

open Polynomial

"""


def render(degree: int, offsets: list[int], prec_bits: int) -> str:
    if degree != 2:
        raise ValueError(f"Only degree=2 is supported, got degree={degree}")
    em = JensenPolynomialHyperbolicityEmitter(degree=degree)
    bodies: list[str] = []
    axiom_checks: list[str] = []
    for n in offsets:
        box = jensen_coeff_box(n=n, d=degree, prec_bits=prec_bits)
        text, count = em.render_box(n=n, box=box)
        assert count == 1
        bodies.append(text)
        axiom_checks.append(f"#print axioms jensen_box_hyperbolic_deg2_{n}")
    return HEADER + "\n".join(bodies) + "\n\n" + "\n".join(axiom_checks) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Emit JensenHyperbolicity.lean: d=2 box-hyperbolicity certificate."
    )
    ap.add_argument(
        "--degree",
        type=int,
        default=2,
        help="Jensen polynomial degree (only 2 supported, default 2)",
    )
    ap.add_argument(
        "--n",
        type=int,
        default=0,
        help="Offset into the alpha sequence (default 0)",
    )
    ap.add_argument(
        "--prec",
        type=int,
        default=300,
        help="Arb precision bits for coefficient enclosure (default 300)",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="Verify that the on-disk file matches a fresh render (exit 1 if different)",
    )
    args = ap.parse_args()

    degree: int = args.degree
    n: int = args.n
    prec_bits: int = args.prec
    offsets = [n]

    if not args.check:
        # Print the certified box and discriminant margin for the requested (d, n).
        box = jensen_coeff_box(n=n, d=degree, prec_bits=prec_bits)
        margin = disc2_margin(box)
        print(f"Certified box for J^{{{degree},{n}}} (prec={prec_bits} bits):")
        labels = ["c0 (constant)", "c1 (linear)", "c2 (leading)"]
        for k, (lab, (lo, hi)) in enumerate(zip(labels, box)):
            print(f"  {lab}: [{float(lo):.8g}, {float(hi):.8g}]")
            print(f"    lo = {lo}")
            print(f"    hi = {hi}")
        print(f"Discriminant lower bound (margin): {float(margin):.6g}")
        print(f"  margin = {margin}")
        print()

    fresh = render(degree=degree, offsets=offsets, prec_bits=prec_bits)

    if args.check:
        on_disk = TARGET.read_text() if TARGET.exists() else ""
        ok = on_disk == fresh
        print("check:", "OK" if ok else "FAILED (regenerate with generate.py)")
        return 0 if ok else 1

    TARGET.write_text(fresh)
    print(f"JensenHyperbolicity: wrote {len(offsets)} cert(s) to {TARGET}")
    print("AXLE statement-match gate: included in emitted .lean (kernel-enforced).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
