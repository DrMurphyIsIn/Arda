"""Generate the Li positivity ladder: enclose -> certify -> emit -> write.

    python examples/li_positivity/generate.py           # write lean/LiPositivity.lean
    python examples/li_positivity/generate.py --check    # drift check (no write)

Twenty rungs of Li's criterion (RH-roadmap Track 2), onto the upstream
already-formalized reduction (pinned in lean/lakefile.toml):

    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

Per rung n = 0..19 the emitter proves `0 ≤ (taylorCoeff riemannXi n).re` from a
certified positive rational lower bound (kind `li_positivity`); the bound comes
from `telperion.li_coeff.enclose_li_coeffs` — Arb ball arithmetic on the
pole-free series route, self-checked against the published Li–Keiper values
before any box is handed out.  The file also carries `li_neg_refutes_rh`, the
falsifiability face: a certified NEGATIVE upper bound on any rung would refute
RH outright through the same upstream equivalence (never expected to fire).

Lower bounds are rounded DOWN to 12 significant decimals before emission: a
smaller positive lower bound is still a rigorous lower bound, and the Lean
literals stay readable.

HONEST SCOPE: rungs are a finite NECESSARY-condition check; the uniform `∀ n`
IS RH and nothing here approaches it.  The enclosure hypotheses `hlo` are the
documented Arb trust seam.  conjecture1_proved = False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_li_positivity import (  # noqa: E402
    LiPositivityLadderEmitter,
    li_positivity_family,
    li_refutation_atom_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.li_coeff import enclose_li_coeffs  # noqa: E402

N_RUNGS = 20
PREC_BITS = 192
_OUT = Path(__file__).resolve().parent / "lean" / "LiPositivity.lean"


def _round_down_12sig(x: Fraction) -> Fraction:
    """Largest 12-significant-decimal fraction <= x (x > 0). Still a rigorous
    lower bound; keeps the emitted literal short."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**11:
        exp += 1
    num = (x.numerator * 10**exp) // x.denominator  # floor
    return Fraction(num, 10**exp)


def build() -> str:
    boxes = enclose_li_coeffs(N_RUNGS, prec_bits=PREC_BITS)  # self-checked inside
    los = [_round_down_12sig(lo) for lo, _hi in boxes]
    for n, lo in enumerate(los):
        assert lo > 0, f"rung {n}: rounded lower bound not positive"

    fam = li_positivity_family(
        "LiPositivity",
        GridSpec([("n", list(range(N_RUNGS)))]),
        lambda pt: f"li_rung_{pt['n']}",
        spec=lambda pt: (pt["n"], los[pt["n"]]),
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("LiPositivity",),
            imports=("Lc.LiCriterion.XiOrderBridge",),
            prelude=(
                "open LiCriterion\n\n"
                + li_refutation_atom_lean()
            ),
        ),
        [LiPositivityLadderEmitter()],
        ValidationReport(checks=(("li_positivity", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LiPositivity.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({N_RUNGS} rungs + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
