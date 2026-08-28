"""3x3 Toeplitz-minor (total-positivity / Polya-frequency) certificate for xi."""
import itertools
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import ToeplitzMinorCertificate  # noqa: E402
from telperion.toeplitz import TOEPLITZ3_BRIDGE_LEMMA  # noqa: E402

# a_k = [z^{2k}] xi(1/2+z) enclosures, k=0..7, from examples/toeplitz_xi/a_coeffs.json
ENC = (
    ("4971207781883141099127737/10000000000000000000000000", "2485603890941570549563869/5000000000000000000000000"),
    ("114859721575727187676249/10000000000000000000000000", "91887777260581750141/8000000000000000000000"),
    ("1234520180703180068903/10000000000000000000000000", "154315022587897508613/1250000000000000000000000"),
    ("26011108793297721/31250000000000000000000", "8323554813855270721/10000000000000000000000000"),
    ("39922265513441371/10000000000000000000000000", "9980566378360343/2500000000000000000000000"),
    ("146160257601109/10000000000000000000000000", "14616025760111/1000000000000000000000000"),
    ("427454004553/10000000000000000000000000", "213727002277/5000000000000000000000000"),
    ("1030962613/10000000000000000000000000", "515481307/5000000000000000000000000"),
)


def _minor(g0, g1, g2, g3, g4):
    return g2*g2*g2 - 2*g1*g2*g3 + g1*g1*g4 + g0*g3*g3 - g0*g2*g4


def test_enclosures_well_formed():
    for lo, hi in ENC:
        assert 0 < Fr(lo) < Fr(hi)


def test_certificate_checks_and_indices():
    c = ToeplitzMinorCertificate(name="toeplitz3_xi", enclosures=ENC)
    assert c.check()
    assert c.certified_m() == [2, 3, 4, 5]
    for m in c.certified_m():
        assert c.minor_lo(m) > 0


def test_minor_lo_is_a_true_lower_bound_at_all_corners():
    c = ToeplitzMinorCertificate(name="toeplitz3_xi", enclosures=ENC)
    for m in c.certified_m():
        box = [(Fr(ENC[m+i][0]), Fr(ENC[m+i][1])) for i in (-2, -1, 0, 1, 2)]
        mlo = c.minor_lo(m)
        for corner in itertools.product(*[(lo, hi) for lo, hi in box]):
            assert mlo <= _minor(*corner)          # lower bound holds at all 32 corners
        assert mlo > 0


def test_lean_shape():
    c = ToeplitzMinorCertificate(name="toeplitz3_xi", enclosures=ENC)
    lean = c.lean()
    assert TOEPLITZ3_BRIDGE_LEMMA in lean
    assert "toeplitz3_pos_of_enclosure" in lean
    for m in (2, 3, 4, 5):
        assert f"theorem toeplitz3_xi_m{m}" in lean
    assert lean.count("0 < g2*g2*g2") >= 4


def test_bogus_enclosure_blocks_emission():
    bad = list(ENC)
    bad[4] = (ENC[4][0], "1")
    c = ToeplitzMinorCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
    with pytest.raises(ValueError, match="refusing to emit"):
        c.lean()


def test_inverted_enclosure_refused():
    bad = list(ENC)
    bad[3] = (ENC[3][1], ENC[3][0])
    c = ToeplitzMinorCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
