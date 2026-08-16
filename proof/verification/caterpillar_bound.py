"""CATERPILLAR / LOLLIPOP family bound -- the high-cavity spine family, and its exact spine mechanism.

CONTEXT.  depth_collapse_cavity_ceiling_probe.py showed the depth-collapse cannot flatten to depth-1
mixed bushes: deep trees reach cavity -> 1/2 (the LOLLIPOP = stem + wide leaf-star) that no depth-1
mixed bush at odd V attains.  This module targets that high-cavity family directly and proves it is
<= 0, extending ChainMargin.lean (pure chains) to lollipops (chains ending in a bush) and to general
caterpillars.

  LOLLIPOP  L_s(B) = a c=0 single-child STEM of length s above a terminal mixed bush B=(c,[leaves]).
  CATERPILLAR       = a spine v_0-...-v_n where each v_i has c_i cherries + l_i pendant leaves.

============================================================================================
EXACT SPINE MECHANISM (rigorous, all values -- fractions.Fraction)
============================================================================================

(M1) CAVITY MAP.  Attaching a c=0 stem node to a subtree X of cavity kappa gives
        cav((0,[X])) = g(kappa) = 1/(2 + kappa).
(M2) logPhi INCREMENT.  logPhi((0,[X])) - logPhi(X) = -L + log(1 + kappa/2),  L = log(621/64)/11.
(M3) TELESCOPING IDENTITY.  1 + kappa/2 = 1/(2 g(kappa)).
(M4) SIGN.  increment <= 0  <=>  (1+kappa/2)^11 <= 621/64  <=>  kappa <= m* = 2(rho_B - 1) ~ 0.45895.
     (17/14 < rho_B so kappa=3/7 gives increment < 0; kappa=1/2 gives increment > 0.)
(M5) TWO-STEP CONTRACTION.  g is decreasing, g([0,1]) = [1/3,1/2], g^2([0,1]) = [2/5, 3/7], and
     [2/5,3/7] is g-invariant.  Since 3/7 <= m*, EVERY cavity kappa_i for i >= 2 lies in [2/5,3/7]
     and gives increment <= 0.  So along any spine AT MOST the first two increments can be positive.

============================================================================================
THE LOLLIPOP BOUND  logPhi(L_s(B)) <= 0  (for all s >= 0 and all mixed bushes B)
============================================================================================

Writing kappa_0 = cav(B), kappa_{i+1} = g(kappa_i),
    logPhi(L_s(B)) = logPhi(B) + sum_{i=0}^{s-1} [ -L + log(1 + kappa_i/2) ].

SPINE-DECAY LEMMA (rigorous, from M5).  For s >= 2, every increment with i >= 2 is <= 0, hence
    logPhi(L_s(B)) <= logPhi(L_2(B))   for all s >= 2.
So  sup_s logPhi(L_s(B)) = max( logPhi(L_0(B)), logPhi(L_1(B)), logPhi(L_2(B)) ).
The lollipop bound therefore REDUCES to three families:
    L_0(B) = B                         -- <= 0 by the BUSH BOUND (bush_bound_closed.py, PROVEN).
    L_1(B) = (0,[B]),  L_2(B)=(0,[(0,[B])])  -- each a uniform-gap family (max = omega at the ARM),
        verified exactly on a finite range here and escape-closable by the bush-bound method (they are
        NOT yet given an independent escape proof -- see "scope" below).

Iterating the same argument on any caterpillar whose fed cavities stay <= m* gives all-nonpositive
increments, so logPhi(caterpillar) <= logPhi(deepest bush) <= 0 in that (generic) regime.

============================================================================================
SCOPE / HONESTY
============================================================================================
* The spine MECHANISM (M1-M5) and the SPINE-DECAY lemma are rigorous for all values.
* L_1,L_2 <= 0 (and general caterpillars) are VERIFIED exactly on finite ranges with a uniform gap
  (max = omega < 0); a self-contained escape proof for L_1,L_2 is not written here.  So
  caterpillar_bound_proved is reported False (mechanism proven; the two residual stem-families are
  finite-verified, not yet escape-closed).
* This is a BUILDING BLOCK, NOT the depth-collapse.  The per-CAVITY logPhi-maximiser is NOT a
  caterpillar: over all trees with V<=13 it is a deep BRANCHY tree (typical depth 5-7) for ~80% of
  cavities.  So bounding caterpillars does not by itself close piece (i).  conjecture1_proved = False.

Depends on general_children_crux.  fractions + math.
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as Fr

import general_children_crux as GC

L = math.log(621 / 64) / 11


def _tl(C):
    c, kids = C
    return (c, [_tl(k) for k in kids])


@functools.lru_cache(maxsize=None)
def lp(C):
    return GC.log_phi(_tl(C))


@functools.lru_cache(maxsize=None)
def cav(C):
    return GC.cav(_tl(C))


def g(kappa: Fr) -> Fr:
    """Stem cavity map g(kappa) = 1/(2+kappa)."""
    return Fr(1, 1) / (2 + kappa)


def incr_nonpos(kappa: Fr) -> bool:
    """increment -L+log(1+kappa/2) <= 0  <=>  (1+kappa/2)^11 <= 621/64  (exact)."""
    return (1 + kappa / Fr(2)) ** 11 <= Fr(621, 64)


def stem(X, s: int):
    """L_s(X): s c=0 single-child stem nodes above X."""
    for _ in range(s):
        X = (0, (X,))
    return X


@functools.lru_cache(maxsize=None)
def mixed_bushes_at_V(V: int):
    out = []
    for c in range(0, V // 2 + 1):
        rem = V - 1 - 2 * c
        if rem < 0:
            break
        for k in range(rem + 1):
            if (rem - k) % 2:
                continue
            S = (rem - k) // 2

            def gen(k, S, mn=0):
                if k == 0:
                    if S == 0:
                        yield ()
                    return
                for x in range(mn, S + 1):
                    for r in gen(k - 1, S - x, x):
                        yield (x,) + r
            for ts in gen(k, S):
                out.append((c, tuple((t, ()) for t in ts)))
    return tuple(out)


def caterpillar(specs):
    """Spine (root->leaf) specs = [(c_i, l_i)]: node i has c_i cherries + l_i pendant leaves."""
    node = None
    for (c, l) in reversed(specs):
        kids = tuple((0, ()) for _ in range(l))
        if node is not None:
            kids = (node,) + kids
        node = (c, kids)
    return node


def verify(Vbush: int = 22, Vdecay: int = 16) -> dict:
    sub = [(0, ()), (1, ()), (2, ()), (0, ((0, ()),)), (0, ((0, ()), (0, ()))), (3, ()),
           (1, ((0, ()),)), (0, ((2, ()),)), (0, ((0, ()), (0, ()), (0, ()))), (2, ((0, ()), (0, ())))]
    # (M1) cavity map exact
    m1 = all(cav((0, (X,))) == g(cav(X)) for X in sub)
    # (M2) increment formula (float)
    m2 = max(abs((lp((0, (X,))) - lp(X)) - (-L + math.log(1 + float(cav(X)) / 2))) for X in sub) < 1e-9
    # (M3) telescoping identity (exact)
    m3 = all(1 + k / Fr(2) == Fr(1, 1) / (2 * g(k))
             for k in (Fr(0), Fr(1, 3), Fr(3, 7), Fr(1, 2), Fr(1), Fr(2, 5), Fr(7, 17)))
    # (M4) sign threshold: incr<=0 at 3/7, >0 at 1/2
    m4 = incr_nonpos(Fr(3, 7)) and not incr_nonpos(Fr(1, 2))
    # (M5) two-step contraction exact: g^2([0,1]) = [2/5,3/7], invariant, 3/7<=m*
    s1 = (g(Fr(1)), g(Fr(0)))            # [1/3, 1/2]
    s2 = (g(s1[1]), g(s1[0]))            # [2/5, 3/7]
    m5 = (s2 == (Fr(2, 5), Fr(3, 7)) and incr_nonpos(Fr(3, 7))
          and Fr(2, 5) <= g(Fr(3, 7)) and g(Fr(2, 5)) <= Fr(3, 7))
    # SPINE-DECAY lemma: logPhi(L_s(B)) <= logPhi(L_2(B)) for s>=2 (from M5)
    decay_ok = True
    for V in range(1, Vdecay + 1):
        for B in mixed_bushes_at_V(V):
            l2 = lp(stem(B, 2))
            for s in range(3, 12):
                if lp(stem(B, s)) > l2 + 1e-12:
                    decay_ok = False
    # reduction: L_0 = bush bound (proven elsewhere); L_1, L_2 <= 0 verified on finite range
    w1 = w2 = -9.0
    for V in range(1, Vbush + 1):
        for B in mixed_bushes_at_V(V):
            w1 = max(w1, lp(stem(B, 1)))
            w2 = max(w2, lp(stem(B, 2)))
    l1_ok, l2_ok = w1 <= 1e-12, w2 <= 1e-12
    # general caterpillar (mixed spine) finite verification
    import itertools
    worstc = -9.0
    specs_alpha = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)]
    for n in range(1, 6):
        for specs in itertools.product(specs_alpha, repeat=n):
            worstc = max(worstc, lp(caterpillar(list(specs))))
    mechanism = m1 and m2 and m3 and m4 and m5 and decay_ok
    return {
        "M1_cavity_map_1_over_2_plus_k": m1,
        "M2_increment_formula": m2,
        "M3_telescoping_identity": m3,
        "M4_sign_threshold_mstar": m4,
        "M5_two_step_contraction_le_3_7": m5,
        "spine_decay_lemma_Ls_le_L2": decay_ok,
        "mechanism_proven_all_values": mechanism,
        "L1_family_max_logphi": round(w1, 6), "L1_nonpos": l1_ok,
        "L2_family_max_logphi": round(w2, 6), "L2_nonpos": l2_ok,
        "general_caterpillar_worst_logphi": round(worstc, 6),
        "caterpillar_bound_proved": False,   # mechanism proven; L1/L2 finite-verified not escape-proved
        "conjecture1_proved": False,
        "statement": ("PROVEN (all values): the spine mechanism -- cavity map g(k)=1/(2+k), increment "
                      "-L+log(1+k/2)<=0 iff k<=m*=2(rho_B-1), telescoping 1+k/2=1/(2g(k)), and the "
                      "TWO-STEP CONTRACTION g^2([0,1])=[2/5,3/7]<=m* -- hence the SPINE-DECAY lemma "
                      "logPhi(L_s(B))<=logPhi(L_2(B)) for s>=2. This REDUCES the lollipop bound to "
                      "L_0=B (bush bound, proven) + L_1,L_2<=0 (uniform gap omega, finite-verified, "
                      "escape-closable). Building block only: the per-cavity logPhi-maximiser is a deep "
                      "BRANCHY tree, not a caterpillar, so this does NOT close the depth-collapse."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
