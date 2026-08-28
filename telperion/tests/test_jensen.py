"""Degree-3 Jensen-Polya hyperbolicity certificate for xi (cubic discriminant)."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import CubicJensenCertificate  # noqa: E402
from telperion.jensen import CUBIC_JENSEN_BRIDGE_LEMMA  # noqa: E402

# gamma_k = k! a_k enclosures, k=0..5, from examples/jensen_xi/gammas.json
# (mpmath, 60 dps, two-radius cross-check).  Imported transcendental input.
ENC = (
    ("4971207781883141099127737/10000000000000000000000000", "2485603890941570549563869/5000000000000000000000000"),
    ("114859721575727187676249/10000000000000000000000000", "91887777260581750141/8000000000000000000000"),
    ("1234520180703180068903/5000000000000000000000000", "2469040361406360137807/10000000000000000000000000"),
    ("78033326379893163/15625000000000000000000", "49941328883131624321/10000000000000000000000000"),
    ("958134372322592921/10000000000000000000000000", "479067186161296461/5000000000000000000000000"),
    ("17539230912133153/10000000000000000000000000", "8769615456066577/5000000000000000000000000"),
)


def _disc(g0, g1, g2, g3):
    """Exact cubic discriminant of g0 + 3 g1 X + 3 g2 X^2 + g3 X^3."""
    return (162*g0*g1*g2*g3 + 81*g1*g1*g2*g2
            - 108*g0*g2*g2*g2 - 108*g1*g1*g1*g3 - 27*g0*g0*g3*g3)


def test_enclosures_well_formed():
    for lo, hi in ENC:
        assert 0 < Fr(lo) < Fr(hi)


def test_certificate_checks_and_shifts():
    c = CubicJensenCertificate(name="cubic_jensen_xi", enclosures=ENC)
    assert c.check()
    assert c.certified_shifts() == [0, 1, 2]
    for n in c.certified_shifts():
        assert c.disc_lo(n) > 0


def test_disc_lo_is_a_true_lower_bound_of_the_discriminant():
    # worst-corner bound <= discriminant at every corner of the box
    c = CubicJensenCertificate(name="cubic_jensen_xi", enclosures=ENC)
    import itertools
    for n in c.certified_shifts():
        box = [ (Fr(ENC[n+i][0]), Fr(ENC[n+i][1])) for i in range(4) ]
        dlo = c.disc_lo(n)
        for corner in itertools.product(*[(lo, hi) for lo, hi in box]):
            assert dlo <= _disc(*corner)         # lower bound holds at all 16 corners
        assert dlo > 0


def test_certified_cubics_are_actually_hyperbolic():
    # independent check: the cubic at the enclosure lower corner has three real roots
    np = pytest.importorskip("numpy")
    for n in (0, 1, 2):
        g = [float(Fr(ENC[n+i][0])) for i in range(4)]   # g0..g3
        # coeffs high-degree first: g3 X^3 + 3 g2 X^2 + 3 g1 X + g0
        roots = np.roots([g[3], 3*g[2], 3*g[1], g[0]])
        assert max(abs(r.imag) for r in roots) < 1e-9    # all real => hyperbolic


def test_lean_shape():
    c = CubicJensenCertificate(name="cubic_jensen_xi", enclosures=ENC)
    lean = c.lean()
    assert CUBIC_JENSEN_BRIDGE_LEMMA in lean
    assert "cubic_jensen_pos_of_enclosure" in lean
    for n in (0, 1, 2):
        assert f"theorem cubic_jensen_xi_n{n}" in lean
    # each per-shift theorem states the full discriminant is positive
    assert lean.count("0 < 162*g0*g1*g2*g3") >= 3
    assert "norm_num" in lean


def test_too_few_enclosures_refused():
    c = CubicJensenCertificate(name="t", enclosures=ENC[:3])
    assert not c.check()
    with pytest.raises(ValueError, match="refusing to emit"):
        c.lean()


def test_bogus_wide_enclosure_blocks_emission():
    bad = list(ENC)
    bad[2] = (ENC[2][0], "1")        # hi_2 = 1, wrecks the n=0,1,2 margins
    c = CubicJensenCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
    with pytest.raises(ValueError):
        c.lean()


def test_inverted_enclosure_refused():
    bad = list(ENC)
    bad[1] = (ENC[1][1], ENC[1][0])
    c = CubicJensenCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
