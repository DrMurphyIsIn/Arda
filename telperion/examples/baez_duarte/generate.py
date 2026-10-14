"""Generate the Báez-Duarte upper-bound sequence — Face 6 (spectral) of the RH obstruction.

    python examples/baez_duarte/generate.py           # write lean/BaezDuarte.lean
    python examples/baez_duarte/generate.py --check    # drift check (no write)

The Báez-Duarte / Bagchi criterion: RH ⟺ d²_N → 0, where
d²_N = inf_c ‖1 − Σ_{k=2}^N c_k·g_k‖²_{L²(0,1)} and g_k(x) = {1/(kx)} − {1/x}/k
(Báez-Duarte 2003, arXiv:math/0202141; Bagchi, Proc. Indian Acad. Sci. 116
(2006), Thm 7 in this L²(0,1) form, Thm 1 in the unitarily equivalent weighted
ℓ² form, both reduced to Thm 2 in H²(Re s > 1/2)).  Per rung N the emitter
proves ``d²_N ≤ U`` from an explicit rational coefficient vector (the normal
equations solved on the exact Gram) whose form value
Q(c) = Σ_n (1 − Σ c_k{n/k})²/(n(n+1)) ≥ d²_N is RIGOROUSLY bounded to ``Uexact``
(exact rational head n < Y rounded up term by term + a rational tail bound);
the emitted readable ``U ≥ Uexact`` is rounded UP to 12 significant decimals (a
larger upper bound is still valid).  The file also carries ``bd_neg_refutes``,
the falsifiability face.

The certified bounds are 0.30685, 0.09575, 0.06595, 0.03632, 0.03621, 0.02439
for N = 2..7, non-increasing in N (as the nested spans force; tested over every
rung).  Only the upper bounds are certified; for N ≥ 3 they are COMPUTED
(mpmath) to be within 10⁻⁹ of the true d²_N.  At N = 2 the gap is certified
two-sided: d²_2 = 1 − ln 2 exactly and U_2 exceeds it by 6.25·10⁻¹².

EARLIER VERSIONS (main before 2026-10-14) used {1/(kx)} without the −{1/x}/k
term.  That family is not an RH criterion: its d²_N ≥ 1/2 − (ln 2)² ≈ 0.019547
for every N, unconditionally.  The theorem names bd_N2..bd_N7 and bd_neg_refutes
are unchanged; their numbers and meaning changed.

HONEST SCOPE: each rung is a finite NECESSARY-condition check; the uniform
d²_N → 0 IS RH and nothing here approaches it.  The hypotheses ``hval`` are the
documented trust seam.  conjecture1_proved = False.

Dependency: mpmath for the Gram (python-flint is in the `flint` manifest group
of telperion.toml, but this generator no longer needs Arb: the logs cancel).
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
PREC_BITS = 128
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
