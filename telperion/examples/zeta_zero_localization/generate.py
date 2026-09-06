"""Generate the XiLineZeros example (Stage 1 core): certify -> emit -> write.

    python examples/zeta_zero_localization/generate.py           # write lean/XiLineZeros.lean
    python examples/zeta_zero_localization/generate.py --check    # drift check (no write)

On-line zero localization of the completed Riemann zeta function `Lambda` via
alternating-sign real enclosures + the intermediate value theorem.

The demo brackets the FIRST nontrivial zero of the Riemann zeta function
(t ~ 14.1347) between the sample points t = 14 and t = 15.  Task-1's certified
Arb enclosure `enclose_lambda('1/2', t, prec)` gives the real box of
`Lambda(1/2 + i*t)`:

    t = 14:  Re Lambda ~ -2.05e-6  (negative box)
    t = 15:  Re Lambda ~ +6.27e-6  (positive box)

One sign change => one on-line zero.  The emitted theorem states: GIVEN the two
enclosure hypotheses (the documented Arb-certified NON-KERNEL input), there exists
`x in [14, 15]` with `completedRiemannZeta (1/2 + x*I) = 0`.  The proof lifts to
`gLine t := (completedRiemannZeta (1/2 + t*I)).re` (real on the line by the Task-2
kernel prelude `ZetaZeroLocalization.completedZeta_im_eq_zero`), uses its
continuity (`completedRiemannZeta` is differentiable away from {0, 1}, and the line
point `1/2 + t*I` is never 0 nor 1), and applies `intermediate_value_Icc`.

The emitted file imports `LambdaLineReal` (Task 2).  conjecture1_proved = False.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

import sympy as sp  # noqa: E402

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.arb_enclosure import enclose_lambda  # noqa: E402  (Task 1)
from telperion.emit_xi_line_zeros import (  # noqa: E402
    XI_LINE_ZEROS_PRELUDE,
    XiLineZerosEmitter,
    xi_line_zeros_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# kind "xi_line_zeros" is registered in telperion/certify.py
# (_SPECIAL_KINDS + _SPECIAL_DISPATCH).

_OUT = Path(__file__).resolve().parent / "lean" / "XiLineZeros.lean"

_PREC = 200  # Arb working precision (bits); enclosures ~ 1e-6 wide at t ~ 14-15.


def _real_box(t):
    """Real box (lo, hi) of Lambda(1/2 + i*t) from the Task-1 Arb enclosure."""
    (lo_re, hi_re), _im = enclose_lambda("1/2", str(t), _PREC)
    return (lo_re, hi_re)


def _spec(pt):
    # Bracket the first nontrivial zero (t ~ 14.1347) between t = 14 (Re < 0) and
    # t = 15 (Re > 0): one sign change -> one certified on-line zero.
    a, b = sp.Integer(14), sp.Integer(15)
    samples = [
        (sp.Integer(14), _real_box(14)),
        (sp.Integer(15), _real_box(15)),
    ]
    return a, b, samples


def build() -> str:
    fam = xi_line_zeros_family(
        "XiLineZeros",
        (),
        GridSpec([("case", [0])]),
        lambda pt: "lambda_zero_first_14_15",
        spec=_spec,
    )
    profile = LeanProfile(
        namespace=("XiLineZeros",),
        imports=("Mathlib", "LambdaLineReal"),
        prelude=XI_LINE_ZEROS_PRELUDE,
        # gLine/continuity refer to `completedRiemannZeta`, `Complex.I`, etc.;
        # `open Complex` keeps the prelude and theorems concise.
        options=(
            "open Complex",
            # The enclosure-hypothesis binders are consumed only inside term-mode
            # `linarith [...]` citations, which the unusedVariables linter does not
            # count as a lexical reference; silence that cosmetic warning.
            "set_option linter.unusedVariables false",
        ),
    )
    report = emit(
        certify(fam),
        profile,
        [XiLineZerosEmitter()],
        ValidationReport(checks=(("xi_line_zeros", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
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
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
