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
    generate.py --grid                  # emit d=2 grid for n=0,1,2 (three certs)
    generate.py --n-list 0 1 2          # explicit list of n offsets
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

# Default grid offsets for --grid mode (d=2, n=0..2, three certs).
# n=3 needs alpha(5), which requires a rigorous Cauchy truncation-tail bound
# (deferred to Phase 2); it is NOT in the grid to preserve soundness.
GRID_D2_OFFSETS: list[int] = [0, 1, 2]
# Default precision for grid mode: 400 bits ensures positive margins for all n=0..2.
GRID_PREC_BITS: int = 400

HEADER = """/-
Jensen-Polya hyperbolicity: d=2 box-hyperbolicity certificates (Task 9).

conjecture1_proved = False. Emitted by JensenPolynomialHyperbolicityEmitter.
Each theorem asserts that every degree-2 Jensen polynomial in a certified
rational coefficient box is hyperbolic (real-root multiset cardinality = degree).
The proof chains a box-positivity discriminant bound into the d=2 bridge lemma
hyperbolic_deg2_of_discrim_nonneg (JensenBridge.lean). NOT a proof of RH.

Grid: J^{2,n} for n = 0, 1, 2 (three certs). Higher n (needing alpha(m>=5))
and degrees d >= 3 are deferred to Phase 2 (general Hermite-Bezoutian engine).

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
        margin = disc2_margin(box)
        text, count = em.render_box(n=n, box=box)
        assert count == 1
        bodies.append(text)
        axiom_checks.append(f"#print axioms jensen_box_hyperbolic_deg2_{n}")
        _ = margin  # margin already validated inside render_box (raises on <= 0)
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
        help="Offset into the alpha sequence (default 0); ignored when --grid is set",
    )
    ap.add_argument(
        "--prec",
        type=int,
        default=300,
        help="Arb precision bits for coefficient enclosure (default 300; grid default 400)",
    )
    ap.add_argument(
        "--check",
        action="store_true",
        help="Verify that the on-disk file matches a fresh render (exit 1 if different)",
    )
    ap.add_argument(
        "--grid",
        action="store_true",
        help=(
            "Grid mode: emit d=2 certs for n=0,1,2 (three theorems). "
            "Uses prec=400 by default unless --prec is explicit. "
            "n>=3 (needs alpha(m>=5)) and d>=3 deferred to Phase 2."
        ),
    )
    ap.add_argument(
        "--n-list",
        type=int,
        nargs="+",
        metavar="N",
        help="Explicit list of n offsets (overrides --n and --grid offset defaults)",
    )
    args = ap.parse_args()

    degree: int = args.degree

    # Determine offsets and precision.
    if args.n_list is not None:
        offsets = args.n_list
        prec_bits = args.prec  # user must specify --prec if defaults are wrong
    elif args.grid:
        offsets = GRID_D2_OFFSETS
        # Use 400 bits for grid mode unless the caller explicitly overrode it.
        prec_bits = args.prec if args.prec != 300 else GRID_PREC_BITS
    else:
        offsets = [args.n]
        prec_bits = args.prec

    if not args.check:
        # Print certified box and discriminant margin for each requested (d, n).
        for n in offsets:
            box = jensen_coeff_box(n=n, d=degree, prec_bits=prec_bits)
            margin = disc2_margin(box)
            print(f"Certified box for J^{{{degree},{n}}} (prec={prec_bits} bits):")
            labels = ["c0 (constant)", "c1 (linear)", "c2 (leading)"]
            for k, (lab, (lo, hi)) in enumerate(zip(labels, box)):
                print(f"  {lab}: [{float(lo):.8g}, {float(hi):.8g}]")
            print(f"  Discriminant lower bound (margin): {float(margin):.6g}")
            print()

    fresh = render(degree=degree, offsets=offsets, prec_bits=prec_bits)

    if args.check:
        on_disk = TARGET.read_text() if TARGET.exists() else ""
        ok = on_disk == fresh
        print("check:", "OK" if ok else "FAILED (regenerate with generate.py)")
        return 0 if ok else 1

    TARGET.write_text(fresh)
    print(f"JensenHyperbolicity: wrote {len(offsets)} cert(s) to {TARGET}")
    if args.grid:
        print(f"Grid mode: d=2, offsets={offsets}, prec={prec_bits} bits.")
        print("n>=3 (alpha(m>=5)) and d>=3 deferred to Phase 2 "
              "(general Hermite-Bezoutian engine + Cauchy tail bound).")
    print("AXLE statement-match gate: included in emitted .lean (kernel-enforced).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
