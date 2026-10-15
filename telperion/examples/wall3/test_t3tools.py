"""Self-checks for t3tools (run: python -m pytest examples/wall3). conjecture1_proved = False."""
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(__file__))
from flint import acb, acb_series, arb, ctx, fmpz  # noqa: E402

from t3tools import BeurlingZeta, integers_from_primes, powersum_certify  # noqa: E402


def test_powersum_exact_and_refute():
    b, z = [(1, 0), (1, 0)], [(F(3, 5), F(4, 5)), (F(1), F(0))]
    assert powersum_certify(b, z, range(1, 11), lower=F(1, 10), exact=True)["certified"]
    r = powersum_certify(b, z, range(1, 11), lower=F(1, 5), exact=True)
    assert not r["certified"] and r["refuted"]


def test_beurling_zeta_contains_zeta():
    ps = [p for p in range(2, 2001) if fmpz(p).is_prime()]
    Z = BeurlingZeta(integers_from_primes([arb(p).log() for p in ps], 2000.5), 1, 1, 0, "2000.5")
    old = ctx.prec, ctx.cap
    ctx.prec, ctx.cap = 96, 1
    try:
        for s in (acb(2), acb("0.8", "10"), acb("1.5", "30")):
            v = Z(acb_series([s])).coeffs()[0]
            assert v.overlaps(s.zeta())
    finally:
        ctx.prec, ctx.cap = old
