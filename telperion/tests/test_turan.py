"""Turan-enclosure certificate tests (Laguerre-Polya / RH-necessary, CNV 1986)."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import TuranEnclosureCertificate  # noqa: E402
from telperion.turan import TURAN_BRIDGE_LEMMA  # noqa: E402

# Exact rational enclosures lo_k < a_k < hi_k of a_k = [z^{2k}] xi(1/2+z),
# k=0..4, from examples/turan_xi/enclosures.json (mpmath, 60 dps, radius
# cross-checked to >40 digits).  Imported data -- the transcendental input.
ENC = (
    ("4971207781883141099127737/10000000000000000000000000",
     "2485603890941570549563869/5000000000000000000000000"),
    ("114859721575727187676249/10000000000000000000000000",
     "91887777260581750141/8000000000000000000000"),
    ("1234520180703180068903/10000000000000000000000000",
     "154315022587897508613/1250000000000000000000000"),
    ("26011108793297721/31250000000000000000000",
     "8323554813855270721/10000000000000000000000000"),
    ("39922265513441371/10000000000000000000000000",
     "9980566378360343/2500000000000000000000000"),
)


def test_enclosures_well_formed():
    for lo, hi in ENC:
        assert 0 < Fr(lo) < Fr(hi)


def test_certificate_checks_and_indices():
    c = TuranEnclosureCertificate(name="turan_xi", enclosures=ENC)
    assert c.check()
    assert c.certified_indices() == [1, 2, 3]
    for k in c.certified_indices():
        assert c.margin(k) > 0            # every worst-corner margin positive


def test_margins_match_python_exact_mirror():
    # the exact rational fact each emitted `norm_num` goal will check
    c = TuranEnclosureCertificate(name="turan_xi", enclosures=ENC)
    for k in (1, 2, 3):
        lo_k = Fr(ENC[k][0])
        hi_km, hi_kp = Fr(ENC[k - 1][1]), Fr(ENC[k + 1][1])
        assert c.margin(k) == lo_k * lo_k - hi_km * hi_kp
        assert lo_k * lo_k > hi_km * hi_kp


def test_lean_shape():
    c = TuranEnclosureCertificate(name="turan_xi", enclosures=ENC)
    lean = c.lean()
    assert TURAN_BRIDGE_LEMMA in lean
    for k in (1, 2, 3):
        assert f"theorem turan_xi_k{k}" in lean
    assert "turan_from_enclosure" in lean
    assert "norm_num" in lean
    # every per-index theorem concludes the strict Turan inequality
    assert lean.count("< a") >= 3


def test_too_few_enclosures_refused():
    c = TuranEnclosureCertificate(name="t", enclosures=ENC[:2])
    assert not c.check()
    with pytest.raises(ValueError, match="refusing to emit"):
        c.lean()


def test_bogus_enclosure_blocks_emission():
    # widen a_2's window so the k=1 / k=3 margins can no longer be certified:
    # push hi_2 up above what lo_1^2 / hi_0 and lo_3^2 / hi_4 allow.
    bad = list(ENC)
    bad[2] = (ENC[2][0], "1")            # hi_2 = 1, absurdly loose
    c = TuranEnclosureCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
    with pytest.raises(ValueError):
        c.lean()


def test_inverted_enclosure_refused():
    bad = list(ENC)
    bad[1] = (ENC[1][1], ENC[1][0])      # lo > hi
    c = TuranEnclosureCertificate(name="t", enclosures=tuple(bad))
    assert not c.check()
