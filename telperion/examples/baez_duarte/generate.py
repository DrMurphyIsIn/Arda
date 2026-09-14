"""Generate the Báez-Duarte upper-bound sequence — Face 6 (spectral) of the RH obstruction.

    python examples/baez_duarte/generate.py           # write lean/BaezDuarte.lean
    python examples/baez_duarte/generate.py --check    # drift check (no write)

The Nyman–Beurling–Báez-Duarte criterion: RH ⟺ d²_N → 0, where
d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·{(1/k)/x}‖²_{L²(0,1)}.  Per rung N the emitter
proves ``d²_N ≤ U`` from an explicit rational coefficient vector whose quadratic
form value Q(c) ≥ d²_N is RIGOROUSLY enclosed (exact piecewise integral on [δ,1]
+ flint/Arb ln-values + a [0,δ] tail bound) to ``Uexact``; the emitted readable
``U ≥ Uexact`` is rounded UP to 12 significant decimals (a larger upper bound is
still valid).  The file also carries ``bd_neg_refutes``, the falsifiability face.

The sequence of bounds is DECREASING (0.52, 0.38, 0.31, 0.27, … as N grows) —
finite, certified evidence consistent with the spectral face's d²_N → 0.

HONEST SCOPE: each rung is a finite NECESSARY-condition check; the uniform
d²_N → 0 IS RH and nothing here approaches it.  The enclosure hypotheses
``hval`` are the documented Arb trust seam.  conjecture1_proved = False.

Dependency: python-flint + mpmath (see the `flint` manifest group in telperion.toml).
"""
import argparse
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_baez_duarte import (  # noqa: E402
    BaezDuarteEmitter,
    baez_duarte_family,
    baez_duarte_refutation_atom_lean,
    baez_duarte_upper_bound,
    optimal_coeffs,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

RUNGS = [2, 3, 4, 5, 6, 7]
PREC_BITS = 256
_OUT = Path(__file__).resolve().parent / "lean" / "BaezDuarte.lean"


def _round_up_12sig(x: Fraction) -> Fraction:
    """Smallest 12-significant-decimal fraction >= x (x > 0). Still a valid upper
    bound; keeps the emitted literal short."""
    assert x > 0
    exp = 0
    while x * 10**exp < 10**11:
        exp += 1
    num = -((-x.numerator * 10**exp) // x.denominator)  # ceil
    return Fraction(num, 10**exp)


def build() -> str:
    specs = {}
    for N in RUNGS:
        cs = optimal_coeffs(N, prec_bits=PREC_BITS)
        Uexact, _ = baez_duarte_upper_bound(cs, prec_bits=PREC_BITS)
        U = _round_up_12sig(Uexact)
        assert U >= Uexact
        specs[N] = {"coeffs": cs, "U": U}

    fam = baez_duarte_family(
        "BaezDuarte",
        GridSpec([("N", RUNGS)]),
        lambda pt: f"bd_N{pt['N']}",
        spec=lambda pt: specs[pt["N"]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("BaezDuarte",),
            prelude=baez_duarte_refutation_atom_lean(),
        ),
        [BaezDuarteEmitter()],
        ValidationReport(checks=(("baez_duarte", True),)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: BaezDuarte.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(RUNGS)} rungs + refutation atom, {len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
