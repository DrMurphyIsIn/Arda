"""The branching (j'>=2) g-step optimization, reduced to two rational leaves. Tests.

Pins: symmetric-argmax (global max is symmetric); per-j' max at the crossover mu*; boost(mu*) < 4/3 (from
3 mu* < 1); the two exact rational leaves (I) gamma < (10/9)^11 (mu*<1/3) and (II) W(4/3)^11 < gamma, and
their cross-multiplied integer forms; and that they bound the optimization below gamma. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    GStepReductionCertificate,
    MU_STAR,
    f_sym,
    leaf_W_four_thirds_lt_gamma,
    leaf_mu_star_lt_third,
)
from telperion.gstep_reduction import GAMMA, W  # noqa: E402


def test_rational_leaves_exact():
    assert leaf_mu_star_lt_third()                                   # gamma < (10/9)^11  (mu* < 1/3)
    assert GAMMA < Fr(10, 9) ** 11
    assert 64 ** 2 * 5 ** 11 * 9 ** 11 < 621 ** 2 * 3 ** 11 * 10 ** 11
    assert leaf_W_four_thirds_lt_gamma()                             # W(4/3)^11 < gamma
    assert 621 * 4 ** 11 < 64 * 5 ** 11
    assert MU_STAR < 1 / 3


def test_leaves_chain_below_gamma():
    # f_{j'>=2}(mu*) = W*boost^11 < W*(4/3)^11 < gamma ; binding j'=2 value ~2.107
    assert float(W * Fr(4, 3) ** 11) < float(GAMMA)
    assert f_sym(2, MU_STAR) < float(W * Fr(4, 3) ** 11)
    assert f_sym(2, MU_STAR) < float(GAMMA)


def test_reduction_certificate_and_scope():
    cert = GStepReductionCertificate()
    assert cert.symmetric_is_argmax()
    assert cert.per_jp_max_at_crossover()
    assert cert.boost_below_four_thirds()
    assert cert.rational_leaves()
    assert cert.check()
    f = cert.finding()
    assert "gamma<(10/9)^11" in f and "621*4^11 < 64*5^11" in f
    assert "chain-absorbed" in f
    assert "conjecture1_proved = False" in f
