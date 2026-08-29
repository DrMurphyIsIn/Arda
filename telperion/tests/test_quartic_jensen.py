"""Degree-4 Jensen hyperbolicity + general WorstCornerCertificate."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import QuarticJensenCertificate, WorstCornerCertificate  # noqa: E402

# gamma_k enclosures at 1e-30 (from examples/rh_lean/build.py _QUARTIC_GAMMAS)
ENC = tuple((Fr(lo), Fr(hi)) for lo, hi in (
    ("99424155637662821982554747937/200000000000000000000000000000", "248560389094157054956386869843/500000000000000000000000000000"),
    ("1435746519696589845953117281/125000000000000000000000000000", "11485972157572718767624938249/1000000000000000000000000000000"),
    ("123452018070318006890345791/500000000000000000000000000000", "246904036140636013780691583/1000000000000000000000000000000"),
    ("624266611039145304003569/125000000000000000000000000000", "4994132888313162432028553/1000000000000000000000000000000"),
    ("47906718616129646096703/500000000000000000000000000000", "95813437232259292193407/1000000000000000000000000000000"),
    ("1753923091213315303489/1000000000000000000000000000000", "175392309121331530349/100000000000000000000000000000"),
))


def test_worst_corner_general_on_a_simple_poly():
    g0, g1 = sp.symbols("g0 g1", positive=True)
    # g0^2 - g1 > 0 over [3,4]x[1,2]: worst corner 3^2 - 2 = 7 > 0
    c = WorstCornerCertificate(name="wc", poly=g0**2 - g1, enclosures=((3, 4), (1, 2)))
    assert c.check() and c.worst_corner_lo() == Fr(7)
    # a poly that fails: g1 - g0^2 over same box -> worst corner 1 - 16 < 0
    assert not WorstCornerCertificate(name="w", poly=g1 - g0**2, enclosures=((3, 4), (1, 2))).check()


def test_quartic_certifies_shifts_0_and_1():
    q = QuarticJensenCertificate(name="quartic_jensen_xi", enclosures=ENC)
    assert q.check()
    assert q.certified_shifts() == [0, 1]


def test_lean_has_three_conditions_per_shift():
    lean = QuarticJensenCertificate(name="quartic_jensen_xi", enclosures=ENC).lean()
    for n in (0, 1):
        assert f"quartic_jensen_xi_n{n}_disc" in lean   # Delta4 > 0
        assert f"quartic_jensen_xi_n{n}_P" in lean       # P < 0
        assert f"quartic_jensen_xi_n{n}_D" in lean       # D < 0
    assert lean.count("nlinarith") == 6                  # 3 conditions x 2 shifts
