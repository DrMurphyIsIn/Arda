"""General degree-n Jensen hyperbolicity via the Hermite/Hankel-minor criterion.

A real degree-d polynomial is (strictly) hyperbolic iff its Hermite form -- the
Hankel matrix of the roots' Newton power sums -- is positive definite, i.e. all
leading principal minors are > 0 (Sylvester).  HankelJensenCertificate builds
those minors as polynomials in the gamma enclosures and certifies each > 0 with
the general WorstCornerCertificate.  This subsumes turan (d=2), cubic (d=3) and
quartic (d=4) in ONE uniform emitter, and extends to any degree the tractability
of nlinarith allows.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import HankelJensenCertificate  # noqa: E402
from telperion.hankel_jensen import _power_sums, hankel_minors  # noqa: E402

# gamma_k enclosures at 1e-30 (same source as the quartic test / build.py)
ENC = tuple((Fr(lo), Fr(hi)) for lo, hi in (
    ("99424155637662821982554747937/200000000000000000000000000000", "248560389094157054956386869843/500000000000000000000000000000"),
    ("1435746519696589845953117281/125000000000000000000000000000", "11485972157572718767624938249/1000000000000000000000000000000"),
    ("123452018070318006890345791/500000000000000000000000000000", "246904036140636013780691583/1000000000000000000000000000000"),
    ("624266611039145304003569/125000000000000000000000000000", "4994132888313162432028553/1000000000000000000000000000000"),
    ("47906718616129646096703/500000000000000000000000000000", "95813437232259292193407/1000000000000000000000000000000"),
    ("1753923091213315303489/1000000000000000000000000000000", "175392309121331530349/100000000000000000000000000000"),
))


def _num_power_sums(coeffs):
    """Power sums p_0..p_{2d-2} of the roots of sum_k coeffs[k] X^k, numerically."""
    d = len(coeffs) - 1
    roots = sorted(sp.Poly(list(reversed(coeffs)), sp.symbols("x")).all_roots())
    return [sum(complex(r) ** k for r in roots) for k in range(2 * (d - 1) + 1)]


def test_newton_power_sums_match_known_roots():
    # (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6 : power sums 3,6,14,36,98
    d = 3
    g = sp.symbols(f"g0:{d + 1}", positive=True)
    p = _power_sums(d)
    # a_k = C(d,k) g_k ; choose g so that a = [-6, 11, -6, 1]
    subs = {g[0]: sp.Rational(-6), g[1]: sp.Rational(11, 3),
            g[2]: sp.Rational(-2), g[3]: sp.Rational(1)}
    got = [sp.simplify(pk.subs(subs)) for pk in p]
    assert got == [3, 6, 14, 36, 98]


def test_hankel_minors_positive_iff_hyperbolic():
    x = sp.symbols("x")
    # hyperbolic: distinct real roots
    hyp = sp.Poly((x - 1) * (x - 2) * (x - 4), x).all_coeffs()[::-1]
    # non-hyperbolic: a complex-conjugate pair
    non = sp.Poly((x - 1) * (x**2 + 1), x).all_coeffs()[::-1]
    for coeffs, want in ((hyp, True), (non, False)):
        d = len(coeffs) - 1
        g = sp.symbols(f"g0:{d + 1}", positive=True)
        subs = {g[k]: sp.Rational(coeffs[k]) / sp.binomial(d, k) for k in range(d + 1)}
        minors = [sp.simplify(m.subs(subs)) for _, m in hankel_minors(d)]
        all_pos = all(m > 0 for m in minors)
        assert all_pos == want


def test_degree3_matches_cubic_green_enclosures():
    c = HankelJensenCertificate(name="hankel_d3", enclosures=ENC, degree=3)
    assert c.check()
    assert list(c.certified_shifts()) == [0, 1, 2]


def test_degree4_matches_quartic_green_enclosures():
    c = HankelJensenCertificate(name="hankel_d4", enclosures=ENC, degree=4)
    assert c.check()
    assert list(c.certified_shifts()) == [0, 1]


def test_lean_emits_d_minus_one_minors_per_shift():
    c = HankelJensenCertificate(name="hankel_d3", enclosures=ENC, degree=3)
    lean = c.lean()
    for n in (0, 1, 2):
        assert f"hankel_d3_n{n}_H2" in lean
        assert f"hankel_d3_n{n}_H3" in lean
    # d-1 = 2 minors per shift, 3 shifts
    assert lean.count("nlinarith") == 6


def test_refuses_to_emit_when_not_certified():
    # a box that is NOT all-hyperbolic -> check() False -> lean() raises
    bad = ((Fr(1), Fr(2)),) * 5
    c = HankelJensenCertificate(name="bad", enclosures=bad, degree=4)
    if not c.check():
        try:
            c.lean()
            assert False, "expected refusal"
        except ValueError:
            pass
