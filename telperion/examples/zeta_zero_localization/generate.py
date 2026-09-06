"""Generate the XiLineZeros example (Stage 1 core): certify -> emit -> write.

    python examples/zeta_zero_localization/generate.py            # write lean/XiLineZeros.lean
    python examples/zeta_zero_localization/generate.py --check    # drift check (no write)
    python examples/zeta_zero_localization/generate.py --a 10 --b 35 --n-samples 51 --prec 300
        # print certified N for an ad-hoc interval; does NOT write the Lean file

On-line zero localization of the completed Riemann zeta function `Lambda` via
alternating-sign real enclosures + the intermediate value theorem.

DEFAULT CASES (written to lean/XiLineZeros.lean):

  Case 0 -- lambda_zero_first_14_15:
    Brackets the FIRST nontrivial zero (t ~ 14.1347) between t = 14 (Re < 0) and
    t = 15 (Re > 0).  One sign change => one certified on-line zero.

  Case 1 -- lambda_two_zeros_14_22:
    Brackets the first (t ~ 14.1347) in [14, 15] and the second (t ~ 21.022) in
    [15, 22] with three sample points alternating neg/pos/neg.  Two sign changes.

  Case 2 -- lambda_five_zeros_10_35:
    Half-integer sweep t in {10.0, 10.5, ..., 35.0} (51 points) at 300-bit Arb
    precision over [10, 35].  Resolves all 5 known nontrivial zeros in that range
    (t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351); certifies N >= 5 on-line
    zeros of Lambda on the critical line.  This is the MILESTONE theorem.

All three theorems share the prelude (gLine, gLine_continuous, lambda_eq_gLine).
The Lean file imports LambdaLineReal (Task 2).  conjecture1_proved = False.

INTERVAL DRIVER (ad-hoc; does not write):
  --a A  --b B    sweep interval (integers or halves)
  --n-samples N   number of evenly-spaced sample points in [a, b]
  --prec P        Arb working precision in bits (default 300)
Prints the certified N and exits; does not modify XiLineZeros.lean.

CERTIFICATION STATUS:
  Box membership (enclose_lambda -> sign-definite real box) is a documented
  Arb-certified NON-KERNEL input: Arb ball arithmetic (via python-flint) gives
  outward-rounded rational endpoints, but Lean does not independently verify the
  value.  The sign-change counting and IVT zero-existence argument are
  kernel-clean.  conjecture1_proved = False.
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.arb_enclosure import enclose_lambda  # noqa: E402  (Task 1)
from telperion.emit_xi_line_zeros import (  # noqa: E402
    XI_LINE_ZEROS_PRELUDE,
    XiLineZerosEmitter,
    sign_change_count,
    xi_line_zeros_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "xi_line_zeros" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_OUT = Path(__file__).resolve().parent / "lean" / "XiLineZeros.lean"

_PREC_DEMO = 200    # Arb bits for demo cases 0-1 (enclosures wide enough at t ~ 14-22)
_PREC_SWEEP = 300   # Arb bits for case 2 sweep over [10, 35]


def _real_box(t, prec):
    """Real box (lo, hi) of Lambda(1/2 + i*t) from the Task-1 Arb enclosure."""
    (lo_re, hi_re), _im = enclose_lambda("1/2", str(t), prec)
    return (lo_re, hi_re)


def _sweep_samples(a, b, n_samples, prec):
    """Build a list of (t, (lo, hi)) for n_samples evenly-spaced t in [a, b].

    t values are exact Fraction so they can be passed directly to enclose_lambda
    (converted to string internally) and to the certifier (which requires Fraction).
    The spacing is (b-a)/(n_samples-1); with a, b integer and n_samples = 51 this
    gives half-integer steps over [10, 35].
    """
    fa, fb = Fraction(a), Fraction(b)
    if n_samples < 2:
        raise ValueError("n_samples must be >= 2")
    step = (fb - fa) / (n_samples - 1)
    samples = []
    for k in range(n_samples):
        t = fa + k * step
        samples.append((t, _real_box(t, prec)))
    return samples


_NAMES = {
    0: "lambda_zero_first_14_15",
    1: "lambda_two_zeros_14_22",
    2: "lambda_five_zeros_10_35",
}


def _spec(pt):
    case = pt["case"]
    if case == 0:
        # Bracket the FIRST nontrivial zero (t ~ 14.1347) between t = 14 (Re < 0)
        # and t = 15 (Re > 0): one sign change -> one certified on-line zero.
        # Exercises the neg->pos IVT path (intermediate_value_Icc).
        a, b = sp.Integer(14), sp.Integer(15)
        samples = [
            (sp.Integer(14), _real_box(14, _PREC_DEMO)),
            (sp.Integer(15), _real_box(15, _PREC_DEMO)),
        ]
        return a, b, samples
    if case == 1:
        # TWO zeros with ALTERNATING signs, exercising BOTH IVT directions:
        #   t = 14 (Re < 0), t = 15 (Re > 0), t = 22 (Re < 0)
        # gives sign changes 14->15 (neg->pos, intermediate_value_Icc) and
        # 15->22 (pos->neg, intermediate_value_Icc') -- bracketing the first zero
        # (t ~ 14.1347) in [14, 15] and the third zero (t ~ 21.022) in [15, 22].
        a, b = sp.Integer(14), sp.Integer(22)
        samples = [
            (sp.Integer(14), _real_box(14, _PREC_DEMO)),
            (sp.Integer(15), _real_box(15, _PREC_DEMO)),
            (sp.Integer(22), _real_box(22, _PREC_DEMO)),
        ]
        return a, b, samples
    # case 2: MILESTONE -- 5 zeros in [10, 35].
    # Half-integer sweep at 300-bit precision: t in {10.0, 10.5, ..., 35.0} (51 points).
    # All 5 known nontrivial zeros in [10, 35] (t ~ 14.1347, 21.0220, 25.0109,
    # 30.4249, 32.9351) produce sign-change subintervals; sign_change_count = 5.
    a_frac, b_frac = Fraction(10), Fraction(35)
    sweep = _sweep_samples(10, 35, 51, _PREC_SWEEP)
    # certifier expects sympy-rational-convertible a, b
    return sp.Rational(a_frac), sp.Rational(b_frac), sweep


def build() -> str:
    """Build and emit XiLineZeros.lean (all three cases: 1-zero, 2-zero, 5-zero)."""
    fam = xi_line_zeros_family(
        "XiLineZeros",
        (),
        GridSpec([("case", [0, 1, 2])]),
        lambda pt: _NAMES[pt["case"]],
        spec=_spec,
    )
    profile = LeanProfile(
        namespace=("XiLineZeros",),
        imports=("Mathlib", "LambdaLineReal"),
        prelude=XI_LINE_ZEROS_PRELUDE,
        # gLine/continuity refer to `completedRiemannZeta`, `Complex.I`, etc.;
        # `open Complex` keeps the prelude and theorems concise.  Every emitted
        # hypothesis is load-bearing, so NO unusedVariables suppression is needed.
        options=("open Complex",),
    )
    report = emit(
        certify(fam),
        profile,
        [XiLineZerosEmitter()],
        ValidationReport(checks=(("xi_line_zeros", True),)),
    )
    return next(iter(report.files.values()))


def run_interval(a, b, n_samples, prec):
    """Ad-hoc interval driver: compute certified N for [a, b] and print it.

    Does NOT write any Lean file.  Returns the certified sign-change count.
    """
    print(f"enclose_lambda sweep: [a={a}, b={b}], n_samples={n_samples}, prec={prec} bits")
    samples = _sweep_samples(a, b, n_samples, prec)
    n = sign_change_count(samples)
    print(f"certified N (sign-change count) = {n}")
    return n


def main(*, check: bool = False, a=None, b=None, n_samples: int = 51, prec: int = 300) -> int:
    # Interval driver mode: print N, do not write
    if a is not None and b is not None:
        run_interval(a, b, n_samples, prec)
        return 0

    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: XiLineZeros.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="Generate XiLineZeros.lean or query certified zero count for an interval."
    )
    ap.add_argument("--check", action="store_true",
                    help="drift check; regenerate and byte-compare; do not write")
    ap.add_argument("--a", type=str, default=None,
                    help="interval lower bound (integer or fraction, e.g. 10)")
    ap.add_argument("--b", type=str, default=None,
                    help="interval upper bound (integer or fraction, e.g. 35)")
    ap.add_argument("--n-samples", type=int, default=51,
                    help="number of evenly-spaced sample points in [a, b] (default 51)")
    ap.add_argument("--prec", type=int, default=300,
                    help="Arb working precision in bits (default 300)")
    args = ap.parse_args()
    a_val = Fraction(args.a) if args.a is not None else None
    b_val = Fraction(args.b) if args.b is not None else None
    raise SystemExit(main(
        check=args.check,
        a=a_val,
        b=b_val,
        n_samples=args.n_samples,
        prec=args.prec,
    ))
