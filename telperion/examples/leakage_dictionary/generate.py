"""Generate the leakage-dictionary instances: certify -> emit -> write INTO the quasicrystal island.

    python examples/leakage_dictionary/generate.py           # write the island lib
    python examples/leakage_dictionary/generate.py --check   # drift check (no write)

PROGRAM MIRRORMERE, ROUTE A item A2b.  The general dictionary

    completely-multiplicative amplitude  ==>  ZERO composite Bragg amplitude

is proved in the island's hand-written ``LeakageDictionary.lean``
(``Quasicrystal.composite_bragg_amplitude_zero``), whose content is the LOG-DERIVATIVE
COEFFICIENT FUNCTIONAL: the Dirichlet coefficients ``b`` of ``-F'/F`` pinned by the divisor
recursion ``a n * log n = sum_{d|n} b d * a (n/d)``.  What the falsification zoo consumes is the
INSTANCE -- an explicit amplitude vector with its RE-DERIVED coefficient row -- and that is this
example, emitted through the ``leakage_dictionary`` kind (``LeakageDictionaryEmitter``).

Two instances at the first composite frequency ``log 6``, one per verdict, so the negative control
bites in BOTH directions:

  * ``leak_chi5`` -- the real character mod 5, ``[1, -1, -1, 1, 0]``: COMPLETELY MULTIPLICATIVE.
    The re-derived row cancels exactly and the emitted theorem certifies ``b 6 = 0``.  This is the
    positive control: a completely-multiplicative input DOES certify a zero composite amplitude.
  * ``leak_dh``   -- Davenport-Heilbronn, ``[1, kappa, -kappa, -1, 0]`` with the exact algebraic
    ``kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1)``: NOT completely multiplicative (it is a
    SUM of two Euler products, and multiplicativity does not survive linear combination).  The
    re-derived row leaks: ``b 6 = (1 + kappa^2)(log 2 + log 3) > 0``, certified and enclosed to
    ``1.93635 < b 6 < 1.93637`` -- the roadmap's ``b(6) = +1.9364`` (QC_AXIOMS_DRAFT.md:481).
    DH is REFUSED a zero-amplitude claim, and the emitted falsification twin refutes the
    hypothesis-free dictionary in-kernel.

ANTI-PHANTOM.  Nothing here restates a published number.  ``certify`` re-derives the whole
coefficient row by running the divisor recursion in exact symbolic arithmetic, and
:func:`rederive_published_rows` below independently re-runs the SAME recursion in 50-digit
arithmetic against the published ``b(n)`` row of QC_AXIOMS_DRAFT.md:481 (DH) and its von Mangoldt
control (zeta), REFUSING the whole generation on any disagreement.  The enclosure is likewise
computed by the emitter from the island's kernel-proved atom intervals, never supplied.

conjecture1_proved = False -- a finite fact about Dirichlet coefficients of a logarithmic
derivative; nothing here concerns the zeros of anything.
"""
import argparse
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_leakage_dictionary import (  # noqa: E402
    K, LeakageDictionaryEmitter, _lg, interval_of, leakage_certificate,
    leakage_dictionary_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

# --- the island's kernel-proved atom enclosures (LeakageDictionary.lean section 5) ------------
#     (sympy atom, island lemma name, lo, hi) -- the lemma name is what the emitted proof cites,
#     and the rationals MUST match the lemma's statement or the emitted nlinarith fails.
_S24 = sum((F(-1, 2) ** (i + 1) / F(i + 1) for i in range(24)), F(0))
_L2LO, _L2HI = F(6931471803, 10 ** 10), F(6931471808, 10 ** 10)
_L3LO = _L2LO + (-_S24 - F(1, 2) ** 24)
_L3HI = _L2HI + (-_S24 + F(1, 2) ** 24)
_KLO, _KHI = F(284079041, 10 ** 9), F(142039523, 500000000)

_ATOM_BOUNDS_LEAN = (
    ("K", "Quasicrystal.dhKappa_bounds", _KLO, _KHI),
    ("Lg2", "Quasicrystal.log_two_bounds", _L2LO, _L2HI),
    ("Lg3", "Quasicrystal.log_three_bounds", _L3LO, _L3HI),
)
_ATOM_BOUNDS = {K: (_KLO, _KHI), _lg(2): (_L2LO, _L2HI), _lg(3): (_L3LO, _L3HI)}

CHI5 = [1, -1, -1, 1, 0]          # the real (quadratic) character mod 5
DH = [1, K, -K, -1, 0]            # Davenport-Heilbronn, the standing negative control

_NAMES = {0: "leak_chi5", 1: "leak_dh"}
_ISLAND = Path(__file__).resolve().parents[1] / "quasicrystal" / "lean"
_OUT = _ISLAND / "LeakageInstances.lean"

# --- the published rows this generation is held against ---------------------------------------
PUBLISHED_DH = {2: 0.1969, 3: -0.3121, 4: -1.4422, 6: 1.9364, 9: -2.2859, 25: 0.0000}
PUBLISHED_ZETA = {2: 0.6931, 3: 1.0986, 4: 0.6931, 6: 0.0000, 9: 1.0986, 25: 1.6094}
TOL = 5e-5


def _log_deriv_row(a, N):
    """Solve a(n) log n = sum_{d|n} b(d) a(n/d) for b(1..N) in 50-digit arithmetic."""
    from mpmath import log, mp

    mp.dps = 50
    b = {}
    for n in range(1, N + 1):
        acc = a(n) * log(n)
        for d in range(1, n):
            if n % d == 0:
                acc -= b[d] * a(n // d)
        b[n] = acc / a(1)
    return b


def rederive_published_rows():
    """Independently re-derive the published b(n) rows; REFUSE the generation on disagreement."""
    from mpmath import mp, sqrt

    mp.dps = 50
    kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
    c = [1, kap, -kap, -1, 0]
    dh = _log_deriv_row(lambda n: c[(n - 1) % 5], 25)
    ze = _log_deriv_row(lambda n: mp.mpf(1), 25)
    for row, published, who in ((dh, PUBLISHED_DH, "DH"), (ze, PUBLISHED_ZETA, "zeta")):
        for n, want in published.items():
            got = float(row[n])
            if abs(got - want) > TOL:
                raise SystemExit(
                    f"REFUSED: the {who} leakage row disagrees at n={n}: the divisor recursion "
                    f"gives {got:.6f}, QC_AXIOMS_DRAFT.md:481 publishes {want:.4f}")
    if abs(float(ze[6])) > 1e-30:
        raise SystemExit("REFUSED: the completely-multiplicative control did NOT certify a zero "
                         f"composite amplitude: b(6) = {float(ze[6])}")
    if abs(float(dh[6])) < 1e-3:
        raise SystemExit("REFUSED: DH was granted a zero composite amplitude; the negative "
                         f"control does not bite: b(6) = {float(dh[6])}")
    return dh, ze


def _spec(pt):
    if pt["case"] == 0:
        return {"vec": CHI5, "period": 5, "n": 6, "claim": "vanishes"}
    cert = leakage_certificate(DH, 5, 6, "leaks")
    lo, hi = interval_of(cert.row[-1][1], _ATOM_BOUNDS)
    if not (lo > F(193635, 10 ** 5) and hi < F(193637, 10 ** 5)):
        raise SystemExit(
            f"REFUSED: the DH b(6) enclosure [{float(lo)}, {float(hi)}] does not pin the "
            f"published +1.9364 to four decimals")
    return {"vec": DH, "period": 5, "n": 6, "claim": "leaks", "enclosure": (lo, hi)}


def build() -> str:
    dh, ze = rederive_published_rows()
    fam = leakage_dictionary_family(
        "LeakageInstances",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=_spec,
    )
    checks = [
        (f"rederived_dh_b{n}", abs(float(dh[n]) - w) <= TOL) for n, w in PUBLISHED_DH.items()
    ] + [
        (f"rederived_zeta_b{n}", abs(float(ze[n]) - w) <= TOL) for n, w in PUBLISHED_ZETA.items()
    ] + [
        ("control_vanishes", abs(float(ze[6])) < 1e-30),
        ("control_leaks", abs(float(dh[6])) > 1e-3),
    ]
    report = emit(
        certify(fam),
        LeanProfile(namespace=("LeakageInstances",),
                    imports=("Mathlib", "LeakageDictionary")),
        [LeakageDictionaryEmitter(atom_bounds_lean=_ATOM_BOUNDS_LEAN)],
        ValidationReport(checks=tuple(checks)),
    )
    return next(iter(report.files.values()))


def main(*, check: bool = False) -> int:
    text = build()
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: LeakageInstances.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
