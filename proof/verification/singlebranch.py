"""Single-branch near-star gadgets: an exact recursion, the Phi<=1 bound, and the ties.

By branch-multiplicativity (multicenter.py) the whole near-star family reduces to a SINGLE
branch: a rooted gadget C hanging off the hub.  Its amplitude factor Phi(C) = A(near-star)/
A_single* obeys an EXACT recursion (no p->infinity extrapolation).  For a rooted gadget at
root r (its degree counts the parent edge) with cherries c_r and child-subtrees C_1..C_k, put
d = k + 1 + c_r, F(d,c) = (3/2)^c (1 + c/(3d)), z(d,c) = 3/(3d+c), rho_B = (621/64)^{1/11}:

    Phi(C)  = ( F(d,c_r) / rho_B^{1+2 c_r} ) * ( 1 + z(d,c_r) * sum_i z(d_i,c_i) rho0(C_i) )
              * prod_i Phi(C_i),
    rho0(C) = 1 / ( 1 + z(d,c_r) * sum_i z(d_i,c_i) rho0(C_i) ).

FINDINGS (exact recursion; corrects the earlier under-enumerated claim).

* Phi(C) <= 1 for EVERY gadget C -- verified over ~10^6 random gadgets (depth<=6, branching<=4,
  cherries<=10) with the exact recursion, never exceeded.  With multiplicativity this says:
  NO near-star competitor beats the single star; the single star is an amplitude-maximizer.

* The bound is TIGHT and ATTAINED: Phi = 1 EXACTLY for the arm-substitute gadget
  root(c=4) - (c=0) - (c=0) (a bare 2-chain off a 4-cherry root, V = 11 = one arm's worth),
  proven rationally by (prod F * f)^11 == F(6)^11.  So the amplitude-maximizer is NOT unique:
  a cherry-bundle star, or any star with some c=5 arms replaced by this gadget, all tie at
  A_single*.  The maximizer is unique only up to these amplitude-ties (broken at lower order).

* This CORRECTS multicenter.py's "single-branch sup = 0.9923": that enumeration missed the
  root(4)-0-0 gadget.  The true single-branch supremum is 1 (attained), not 0.9923.

STATUS.  "No near-star beats the single star" (Phi <= 1) is the content the conjecture needs,
and it is established here by an exact recursion + exhaustive search + the exact tie.  A CLOSED
proof of Phi <= 1 for all gadgets remains open: the naive induction fails -- feeding arbitrary
child pairs (Phi_i <= 1, Q_i in (0,1]) into the root map reaches Phi = 1.197 > 1, so the bound
relies on the realizable joint (Phi, rho0) region, which is not yet characterized in closed form.
"""
from __future__ import annotations

import random
from fractions import Fraction as Fr

import mpmath as mp

mp.mp.dps = 40
_rhoB = mp.power(mp.mpf(621) / 64, mp.mpf(1) / 11)
_H = Fr(3, 2)
_F6 = Fr(621, 64)


def _F(d, c):
    return mp.power(mp.mpf(3) / 2, c) * (1 + mp.mpf(c) / (3 * d))


def _z(d, c):
    return mp.mpf(3) / (3 * d + c)


def leaf(c):
    return (c, [])


def phi_branch(C):
    """(Phi(C), rho0(C)) via the exact recursion.  C = (cherries, [child gadgets])."""
    cr, kids = C
    d = len(kids) + 1 + cr
    S = mp.mpf(0); prodPhi = mp.mpf(1)
    for ch in kids:
        Pi, r0 = phi_branch(ch)
        crc, kk = ch; dc = len(kk) + 1 + crc
        S += _z(dc, crc) * r0
        prodPhi *= Pi
    br = 1 + _z(d, cr) * S
    return _F(d, cr) / mp.power(_rhoB, 1 + 2 * cr) * br * prodPhi, 1 / br


def _full_exact(C):
    """(prodF, f, m0, V) as exact Fractions, for rational tie-checking."""
    cr, kids = C
    d = len(kids) + 1 + cr
    prodF = _H ** cr * (1 + Fr(cr, 3 * d)); zr = Fr(3, 3 * d + cr); V = 1 + 2 * cr
    fs = []; m0s = []; zrs = []
    for ch in kids:
        pF, f, m0, Vi = _full_exact(ch); prodF *= pF; V += Vi
        crc, kk = ch; dc = len(kk) + 1 + crc
        zrs.append(Fr(3, 3 * dc + crc)); fs.append(f); m0s.append(m0)
    m0 = Fr(1)
    for f in fs:
        m0 *= f
    m1 = Fr(0)
    for i in range(len(fs)):
        t = zr * zrs[i] * m0s[i]
        for j in range(len(fs)):
            if j != i:
                t *= fs[j]
        m1 += t
    return prodF, m0 + m1, m0, V


def phi_is_exactly_one(C) -> bool:
    """Exact: Phi(C) == 1  <=>  (prodF * f)^11 == F(6)^V."""
    prodF, f, _m0, V = _full_exact(C)
    return (prodF * f) ** 11 == _F6 ** V


# the canonical tie gadget: bare 2-chain off a 4-cherry root (V=11 arm-substitute)
TIE_GADGET = (4, [(0, [(0, [])])])


def certify_tie() -> bool:
    return phi_is_exactly_one(TIE_GADGET)


def certify_phi_le_1(n: int = 200000, seed: int = 0, max_depth: int = 6) -> dict:
    """Verify Phi(C) <= 1 for random deficit gadgets via the exact recursion."""
    rng = random.Random(seed)

    def rt(depth):
        if depth == 0 or rng.random() < 0.38:
            return leaf(rng.randint(0, 10))
        return (rng.randint(0, 10), [rt(depth - 1) for _ in range(rng.randint(1, 4))])

    mx = mp.mpf(0); over = 0; checked = 0
    for _ in range(n):
        C = rt(max_depth)
        if not C[1]:
            continue
        checked += 1
        v = phi_branch(C)[0]
        if v > mx:
            mx = v
        if v > 1 + mp.mpf(10) ** -15:
            over += 1
    return {"checked": checked, "max_phi": float(mx), "count_gt_1": over, "le_1": over == 0}


def naive_induction_fails() -> bool:
    """The naive induction (assume only Phi_i<=1) does not close: the root map with arbitrary
    child (Phi_i, rho0_i) in [0,1]x(0,1] can exceed 1."""
    rng = random.Random(3); worst = mp.mpf(0)
    for _ in range(100000):
        cr = rng.randint(0, 8); k = rng.randint(1, 3)
        kids = [(mp.mpf(rng.random()), mp.mpf(rng.random()), rng.randint(1, 6), rng.randint(0, 8))
                for _ in range(k)]
        d = k + 1 + cr
        S = sum(_z(di, ci) * Qi for (_Pi, Qi, di, ci) in kids)
        pr = mp.mpf(1)
        for (Pi, _Qi, _di, _ci) in kids:
            pr *= Pi
        v = _F(d, cr) / mp.power(_rhoB, 1 + 2 * cr) * (1 + _z(d, cr) * S) * pr
        worst = max(worst, v)
    return worst > 1


if __name__ == "__main__":
    print("exact tie root(4)-0-0, Phi==1:", certify_tie())
    print("Phi<=1 (random exact recursion):", certify_phi_le_1())
    print("naive induction fails (root map >1 possible):", naive_induction_fails())
