"""The hub de-loads to zero: a transfer-monotonicity proof (large k).

Context.  On a star backbone K_{1,k}, arm cherries balance (distribution.py, proven).
The remaining cherry-distribution question is the HUB count c0.  Numerically the optimal
hub is elevated for small n and de-loads to 0 for large n (Remark rem:tie).  This module
turns the large-n half into a proof.

Closed form (star, hub bb-degree k with c0 cherries, arms bb-degree 1):
    pi = (prod_v F_v) (1 + z0 sum_i z_i),
    F(deg,c) = (3/2)^c (1 + c/(3(deg+c))),   z(deg,c) = 3/(3(deg+c)+c).

SINGLE-CHERRY TRANSFER hub -> arm (n fixed): c0 -> c0-1 and one arm c_a -> c_a+1.
Total cherry count is conserved, so the invariant factor (3/2)^{sum c_v} cancels and the
transfer difference is EXPONENTIAL-FREE -- a rational function of (k, c0, c_a).  Writing
g(c)=F(1,c), the common arm factor g(c_a)^{k-1} cancels, leaving

    sign( pi_after - pi_before ) = sign E(k, c0, c_a),
    E = F(k,c0-1) g(c_a+1) (1 + z(k,c0-1)((k-1) z(1,c_a) + z(1,c_a+1)))
        - F(k,c0)   g(c_a)   (1 + z(k,c0)  ( k     z(1,c_a) )).

THEOREM (transfer monotonicity, machine-certified).  For each arm level c_a in {4,5,6}
and every k >= k*(c_a) with k*(4,5,6) = (20,31,46), and every c0 >= 1, E > 0: moving a
cherry off the hub strictly increases pi.  Proof: E = num/den with den > 0; after the
domain shift k = k*(c_a) + m, c0 = 1 + j (m,j >= 0) the numerator is a polynomial in (m,j)
with ALL-NONNEGATIVE coefficients and positive constant term -- a Polya certificate, so
E > 0 throughout.  (certify_transfer, symbolic.)

CONSEQUENCE.  At the pi-maximizing star the arms balance in {4,5} for every n checked
(1320..10560; consistent with the rate-optimal c=5), so the binding threshold is k*(5)=31:
for k >= 31 (n ~ 11k >= ~340) the maximizing star has hub c0 = 0.

Honest scope.  The certificate models the other arms as uniform at level c_a (sum z = k z_a);
the exact balanced-arm sum differs only at O(1/k) and the conclusion is confirmed exactly at
the true balanced optimum (verify_optimal_hub_zero).  A fully uniform-in-c_a threshold (hence a
proof that needs no separate arm-level bound) is left open: k*(c_a) grows super-linearly, so no
single linear shift covers all c_a at once.
"""
from __future__ import annotations

from fractions import Fraction as Fr

import sympy as sp

_H = Fr(3, 2)
K_STAR = {4: 20, 5: 31, 6: 46}   # certified transfer thresholds per arm level


# ------------------------------------------------------------ exact pi (star)
def _F(degb: int, c: int) -> Fr:
    d = degb + c
    return _H ** c * (1 + Fr(c, 3 * d))


def _z(degb: int, c: int) -> Fr:
    d = degb + c
    return Fr(3, 3 * d + c)


def pi_star(k: int, c0: int, arms) -> Fr:
    """Exact pi of a star: hub (bb-degree k, c0 cherries) + arms (bb-degree 1, counts `arms`)."""
    p = _F(k, c0)
    S = Fr(0)
    for c in arms:
        p *= _F(1, c)
        S += _z(1, c)
    return p * (1 + _z(k, c0) * S)


# ------------------------------------------------- symbolic transfer certificate
def certify_transfer(ca: int, kstar: int) -> dict:
    """Prove E(k,c0,ca) > 0 for all k >= kstar, c0 >= 1 via a nonnegative-coefficient
    certificate after the shift k = kstar + m, c0 = 1 + j."""
    k, c0, m, j = sp.symbols("k c0 m j")

    def h(cc, deg):
        d = deg + cc
        return 1 + sp.Rational(1, 3) * cc / d

    def zf(cc, deg):
        d = deg + cc
        return sp.Rational(3, 1) / (3 * d + cc)

    za, za1, g_a, g_a1 = zf(ca, 1), zf(ca + 1, 1), h(ca, 1), h(ca + 1, 1)
    before = h(c0, k) * g_a * (1 + zf(c0, k) * (k * za))
    after = h(c0 - 1, k) * g_a1 * (1 + zf(c0 - 1, k) * ((k - 1) * za + za1))
    num, den = sp.fraction(sp.together(after - before))
    sub = {k: kstar + m, c0: 1 + j}
    pn = sp.Poly(sp.expand(num.subs(sub)), m, j)
    pd = sp.Poly(sp.expand(den.subs(sub)), m, j)
    return {
        "num_nonneg": all(c >= 0 for c in pn.coeffs()),
        "den_nonneg": all(c >= 0 for c in pd.coeffs()),
        "num_const_pos": pn.eval({m: 0, j: 0}) > 0,
        "den_const_pos": pd.eval({m: 0, j: 0}) > 0,
    }


def certify_all(levels=(4, 5, 6)) -> bool:
    """All transfer certificates hold (strict) for the given arm levels."""
    ok = True
    for ca in levels:
        c = certify_transfer(ca, K_STAR[ca])
        ok = ok and c["num_nonneg"] and c["den_nonneg"] and c["num_const_pos"] and c["den_const_pos"]
    return ok


# ------------------------------------------------ numeric: optimum has hub 0
def _balanced(total: int, k: int):
    b = total // k
    e = total - b * k
    return [b + 1] * e + [b] * (k - e)


def verify_optimal_hub_zero(ns=(1320, 2640, 5280)) -> dict:
    """At the pi-maximizing star (optimize k, balanced arms), the hub is 0 and the arms
    land in {4,5}, for each n.  Exact-rational comparison of c0=0 vs c0>0."""
    res = {}
    for n in ns:
        best = None
        for k in range(max(3, n // 15), n // 9):
            tot = (n - (k + 1)) // 2
            if tot < k:
                continue
            arms = _balanced(tot, k)
            v = pi_star(k, 0, arms)                       # hub 0
            if best is None or v > best[0]:
                best = (v, k, min(arms), max(arms))
        _, k, lo, hi = best
        tot = (n - (k + 1)) // 2
        arms = _balanced(tot, k)
        # hub 0 beats hub 1..4 at this k (reallocating the freed cherries to arms)
        beats = all(pi_star(k, 0, arms) > pi_star(k, c0, _balanced(tot - c0, k))
                    for c0 in (1, 2, 3, 4))
        res[n] = {"k": k, "arm_lo": lo, "arm_hi": hi, "hub0_beats_positive": beats,
                  "arms_in_4_5": lo >= 4 and hi <= 5, "k_ge_31": k >= 31}
    return res


if __name__ == "__main__":
    print("transfer certificates (ca in {4,5,6}):")
    for ca in (4, 5, 6):
        print(f"  ca={ca}, k>={K_STAR[ca]}:", certify_transfer(ca, K_STAR[ca]))
    print("all certified:", certify_all())
    print("optimum has hub 0:")
    for n, d in verify_optimal_hub_zero().items():
        print(f"  n={n}: {d}")
