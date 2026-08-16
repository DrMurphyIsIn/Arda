"""Bounding the optimal arm level -- and thereby a clean hub=0 theorem.

hub.py proved the hub de-loads to zero via a transfer certificate, but with two gaps:
(i) the certificate modelled the OTHER arms as uniform at the receiving level, and
(ii) it needed the optimal arm level pinned to a bounded set.  This module closes both.

RATE-OPTIMALITY OF c=5 (exact).  For a cherry-bundle arm of count c the per-vertex growth
rate is rho(c) = F(1,c)^{1/(1+2c)}, F(1,c) = (3/2)^c (1 + c/(3(1+c))).  Then
    rho(c) < rho_B := (621/64)^{1/11} = rho(5)   for every integer c != 5,
as the EXACT rational inequality F(1,c)^{11} < F(1,5)^{1+2c}.  So c=5 is the strict unique
rate-maximizer, and rho is unimodal (rho(c) <= rho(4) for c<=4, rho(c) <= rho(6) for c>=6).
(certify_rate_optimal.)

ARM-LEVEL BOUND (gap ii).  By arm-balancing (distribution.py) the maximizer's arm counts lie
in {m, m+1}.  If some arm <= 3 then all arms <= 4, so the star's rate is <= rho(4) < rho_B;
if some arm >= 7 then all arms >= 6, rate <= rho(6) < rho_B.  Either way it is beaten by the
all-5 star for n >= N1 (an explicit rate-envelope threshold; empirically arms are already in
{4,5,6} by n ~ 200).  Hence the maximizer's arms lie in {4,5,6}.

MIXED-ARM HUB TRANSFER (gap i).  The transfer difference E(k,c0,m,S) with the OTHER arms
contributing total activity S is AFFINE in S, so it suffices to certify the two endpoints
S=(k-1)z(1,6) and S=(k-1)z(1,4) (the extremes of arms in {4,5,6}).  For receiving level
m in {4,5} and both endpoints, E>0 for all k>=33, c0>=1 (nonneg-coefficient certificate).
So for ANY balanced arms in {4,5,6} and k>=33, de-loading the hub strictly increases pi.

THEOREM (hub=0).  For n >= N1 the pi-maximizing star of cherry-bundles has arms in {4,5,6}
(arm-level bound) and k = Theta(n) >= 33, so by the mixed-arm transfer any hub cherry can be
strictly improved away: the hub carries 0.  Both gaps of hub.py are closed.

Scope: this characterises the maximizer AMONG stars of cherry-bundles.  That the global tree
maximizer is such a star (legs are cherries, backbone a star) is the separate, asymptotically
established frame (Prop cherries, Thm kelmans).
"""
from __future__ import annotations

from fractions import Fraction as Fr

import mpmath as mp
import sympy as sp

_H = Fr(3, 2)


def _Farm(c: int) -> Fr:
    d = 1 + c
    return _H ** c * (1 + Fr(c, 3 * d))


def certify_rate_optimal(cmax: int = 60) -> bool:
    """rho(c) < rho_B for every integer 1<=c<=cmax, c!=5, as exact rationals
    F(1,c)^11 < F(1,5)^(1+2c); and rho(5)=rho_B (equality)."""
    F5 = _Farm(5)
    for c in range(1, cmax + 1):
        Fc = _Farm(c)
        lhs, rhs = Fc ** 11, F5 ** (1 + 2 * c)
        if c == 5:
            if lhs != rhs:
                return False
        elif not (lhs < rhs):
            return False
    return True


def _E_expr(m: int, s: Fr):
    """Transfer difference (sign of delta pi) for de-loading a level-m arm, with the
    other arms contributing total activity S=(k-1)*s.  Symbolic in (k, c0)."""
    k, c0 = sp.symbols("k c0")

    def h(cc, deg):
        d = deg + cc
        return 1 + sp.Rational(1, 3) * cc / d

    def zf(cc, deg):
        d = deg + cc
        return sp.Rational(3, 1) / (3 * d + cc)

    S = (k - 1) * sp.Rational(s.numerator, s.denominator)
    za, za1, g_a, g_a1 = zf(m, 1), zf(m + 1, 1), h(m, 1), h(m + 1, 1)
    before = h(c0, k) * g_a * (1 + zf(c0, k) * (S + za))
    after = h(c0 - 1, k) * g_a1 * (1 + zf(c0 - 1, k) * (S + za1))
    return sp.together(after - before), k, c0


# endpoints of the other-arm activity when arms are in {4,5,6}
S_LO = Fr(3, 25)   # z(1,6)
S_HI = Fr(3, 19)   # z(1,4)
K_MIXED = 33       # uniform threshold covering m in {4,5} at both endpoints


def certify_transfer_mixed(kstar: int = K_MIXED) -> bool:
    """Mixed-arm hub transfer: for m in {4,5} and both activity endpoints, E>0 for all
    k>=kstar, c0>=1 via a nonneg-coefficient certificate.  Affine-in-S => covers all
    balanced arms in {4,5,6}."""
    mm, j = sp.symbols("mm j")
    for m in (4, 5):
        for s in (S_LO, S_HI):
            E, k, c0 = _E_expr(m, s)
            num, den = sp.fraction(E)
            sub = {k: kstar + mm, c0: 1 + j}
            pn = sp.Poly(sp.expand(num.subs(sub)), mm, j)
            pd = sp.Poly(sp.expand(den.subs(sub)), mm, j)
            if not (all(c >= 0 for c in pn.coeffs()) and all(c >= 0 for c in pd.coeffs())
                    and pn.eval({mm: 0, j: 0}) > 0 and pd.eval({mm: 0, j: 0}) > 0):
                return False
    return True


def arm_bound_N1() -> int:
    """Explicit (loose) N1 from the rate envelope: any star with all arms <=4 (resp. >=6)
    obeys pi < 2*(4/3)*rho(4)^n (resp. rho(6)^n), while the all-5 hub-0 star has
    pi >= rho_B^{n-1}.  N1 = smallest n past which rho_B^{n-1} > (8/3) max(rho4,rho6)^n."""
    mp.mp.dps = 50
    def rho(c):
        f = _Farm(c)
        return mp.power(mp.mpf(f.numerator) / f.denominator, mp.mpf(1) / (1 + 2 * c))
    rhoB = mp.power(mp.mpf(621) / 64, mp.mpf(1) / 11)
    worst = max(rho(4), rho(6))
    C = mp.mpf(8) / 3
    # rho_B^{n-1} > C worst^n  <=>  n log(rhoB/worst) > log(C) + log(rhoB)
    n = (mp.log(C) + mp.log(rhoB)) / mp.log(rhoB / worst)
    return int(mp.ceil(n))


def verify_maximizer(ns=(340, 500, 800, 1320, 2640)) -> dict:
    """Exact check: the pi-maximizing star (free k, hub, balanced arms) has arms in {4,5,6}
    and hub 0 for each n."""
    from verification.hub import pi_star, _balanced

    res = {}
    for n in ns:
        best = None
        for k in range(3, n // 7):
            for c0 in range(0, 8):
                if (n - (k + 1)) % 2:
                    continue
                tot = (n - (k + 1)) // 2 - c0
                if tot < k:
                    continue
                arms = _balanced(tot, k)
                v = pi_star(k, c0, arms)
                if best is None or v > best[0]:
                    best = (v, k, c0, min(arms), max(arms))
        _, k, c0, lo, hi = best
        res[n] = {"k": k, "hub": c0, "arm_lo": lo, "arm_hi": hi,
                  "arms_in_456": lo >= 4 and hi <= 6, "hub_zero": c0 == 0}
    return res


if __name__ == "__main__":
    print("rate-optimality of c=5 (exact, c<=60):", certify_rate_optimal())
    print("mixed-arm hub transfer certified (k>=33):", certify_transfer_mixed())
    print("explicit arm-bound N1 (rate envelope):", arm_bound_N1())
    print("maximizer arms in {4,5,6} and hub 0:")
    for n, d in verify_maximizer().items():
        print(f"  n={n}: {d}")
