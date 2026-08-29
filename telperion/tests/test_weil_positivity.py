"""WeilPositivityCertificate: the PSD certifier pointed at the finite Weil form."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import WeilPositivityCertificate  # noqa: E402

# 3x3 top-left of the validated Weil-Gram matrix (entries from the explicit formula),
# bracketed to +-1e-5.
_V = {(0, 0): "2.1122372", (0, 1): "2.8679706", (0, 2): "3.3752278",
      (1, 1): "4.1785698", (1, 2): "5.1732953", (2, 2): "6.6731048"}
_HW = Fr(1, 100000)
_ENT = {k: (Fr(v) - _HW, Fr(v) + _HW) for k, v in _V.items()}


def test_weil_3x3_positive_definite():
    c = WeilPositivityCertificate(name="weil_psd_3", n=3, entries=_ENT)
    assert c.check()                       # all leading minors worst-corner > 0
    lean = c.lean()
    assert lean.count("theorem") == 3      # D_1, D_2, D_3


def test_refuses_when_a_minor_fails():
    # widen the brackets so the (thin) 3rd minor's worst-corner goes negative
    wide = {k: (v[0] - Fr(1, 100), v[1] + Fr(1, 100)) for k, v in _ENT.items()}
    c = WeilPositivityCertificate(name="w", n=3, entries=wide)
    assert not c.check()


def test_2x2_is_comfortable():
    ent2 = {k: v for k, v in _ENT.items() if max(k) <= 1}
    c = WeilPositivityCertificate(name="weil_psd_2", n=2, entries=ent2)
    assert c.check()
    assert c.lean().count("theorem") == 2
