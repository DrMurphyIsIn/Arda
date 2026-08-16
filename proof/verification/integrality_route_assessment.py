"""Assessment of the "23-adic / integrality" route on the plain-tree inequality -- why it does NOT apply.

After the plainification theorem, Phi<=1 <=> every plain tree has logPhi<=0.  Clearing the 11th root
(rho_B^11 = 621/64 = 3^3*23/2^6) gives an EXACT rational, PER-NODE factorised form:
    W(T) := Phi(T)^{-11} = prod_v w_v,   w_v = (621/64) * ((k_v+1) * cav_v)^11,   cav_v = 1/(k_v+1+S_v),
and  Phi(T) <= 1  <=>  W(T) >= 1.  The tie N(0,5) gives W = 1 exactly (the integer identity
64*243*23 = 621*576).  This module asks whether the "arithmetic/23-adic" success of the near-star proof
can be transported to trees, and finds it CANNOT, for a structural reason.

(A1) PER-NODE FACTORISATION is exact: W = prod_v w_v = Phi^{-11}, W >= 1 iff Phi <= 1.  [verified]

(A2) W >= 1 IS AN ARCHIMEDEAN (magnitude) STATEMENT, NOT A p-ADIC ONE.  The 23-adic valuation v23(W)
     carries NO information about whether W >= 1:
       * near-tie trees have W slightly above 1 with v23(W) ranging over {1,2,5,7,9,10,12,...} and
         v23(W-1)=0 -- no valuation pattern accompanies the (tiny, positive) surplus;
       * trees with the SAME v23(W) have W spanning many orders of magnitude (e.g. v23(W)=-10 gives W
         from ~10 to ~97000).
     p-adic valuations order Q by divisibility, never by size; a magnitude inequality W>=1 is invisible
     to them.  So no 23-adic (or any p-adic) argument can prove W>=1.  The tie identity
     64*243*23=621*576 is a BOUNDARY EQUALITY (where the exact rational meets the real bound), not a
     proof mechanism for the surrounding strict inequality.

(A3) WHAT THE NEAR-STAR PROOF ACTUALLY WAS (and why it does not generalise).  near_star_arithmetic_proof
     is NOT p-adic: it clears the 11th root, then proves R(s) = RHS/LHS >= 1 by showing the REAL ratio
     R(s+1)/R(s) = (529/486)(1 - 1/(4s^2+11s+7))^11 is monotone with a single crossing, so R has its
     unique minimum at the integer s=5 with R(5)=1.  That is a 1-D REAL-ANALYTIC (archimedean)
     monotonicity argument plus a boundary integer identity.  It does NOT transport to plain trees:
     the plain value function psi is NOT monotone/unimodal over the tree poset (plain_value_function.py:
     jagged, with near-star peaks and steep inter-peak drops), so there is no single parameter on which
     to run a single-crossing ratio, and no total order making W's minimum a lone boundary point.

CONCLUSION.  BOTH previously-flagged non-inductive routes are now clarified as non-viable AS STATED:
  * smooth / smoothing-transform: PROVABLY blocked -- the smooth near-star envelope pokes to +4.17e-5>0
    (psi_envelope.py), so no continuous certificate can be <=0;
  * 23-adic / integrality: STRUCTURALLY inapplicable -- W>=1 is archimedean and p-adic valuations are
    uncorrelated with it (A2); the near-star's arithmetic was 1-D real-analytic monotonicity (A3),
    which the multivariate non-unimodal tree does not admit.
The genuine remaining need is a VALID REAL POTENTIAL (super-solution) tight at the tie -- exactly the
accumulating-LP / marginal-tie problem (potential_nonsmooth_lp, psi_envelope_induction_nogo).  That is
the open 1984 crux; no shortcut through smoothness or p-adics exists.  conjecture1_proved = False.

Self-verifying (exact-rational W).  Standard library only.
"""
from __future__ import annotations

import functools
from collections import defaultdict
from fractions import Fraction as Fr


def pcav(C) -> Fr:
    S = sum(pcav(ch) for ch in C)
    return Fr(1, len(C) + 1 + S)


def Wexact(C) -> Fr:
    """W(T) = Phi(T)^{-11} = prod_v (621/64) ((k_v+1) cav_v)^11 (exact rational)."""
    prod = Fr(1)

    def rec(nd):
        nonlocal prod
        k = len(nd)
        cv = pcav(nd)
        prod *= Fr(621, 64) * ((k + 1) * cv) ** 11
        for c in nd:
            rec(c)
    rec(C)
    return prod


@functools.lru_cache(maxsize=None)
def gen(n: int):
    if n == 1:
        return (tuple(),)
    res = []

    def parts(rem, mn):
        if rem == 0:
            yield ()
            return
        for s in range(mn, rem + 1):
            for sub in gen(s):
                for rest in parts(rem - s, s):
                    yield (sub,) + rest
    for kids in parts(n - 1, 1):
        res.append(kids)
    return tuple(res)


def v23(fr: Fr):
    if fr == 0:
        return None
    n, d = fr.numerator, fr.denominator
    v = 0
    while n % 23 == 0:
        n //= 23
        v += 1
    while d % 23 == 0:
        d //= 23
        v -= 1
    return v


def verify(nmax: int = 12) -> dict:
    tie = tuple(((),) for _ in range(5))
    tie_W = Wexact(tie)
    # (A1) W >= 1 iff Phi <= 1; W == prod w_v (by construction). check W>=1 on all plain trees.
    w_lt1 = 0
    cands = []
    for n in range(1, nmax + 1):
        for T in gen(n):
            W = Wexact(T)
            if W < 1:
                w_lt1 += 1
            if W > 1:
                cands.append(W)
    # (A2) v23(W) uncorrelated with magnitude: group by v23, show wide W-range per class
    byv = defaultdict(list)
    for W in cands:
        byv[v23(W)].append(float(W))
    multi = {vv: (round(min(ws), 4), round(max(ws), 2)) for vv, ws in byv.items() if len(ws) >= 3}
    # a class whose W spans > 10x (magnitude info absent from valuation)
    valuation_uninformative = any(hi / lo > 10 for (lo, hi) in multi.values())
    # near-tie surplus has no 23-adic signature
    near = sorted(cands, key=lambda W: float(W))[:8]
    near_v23 = [(round(float(W - 1), 6), v23(W), v23(W - 1)) for W in near]
    return {
        "A1_tie_W_is_one": tie_W == 1,
        "A1_all_plain_W_ge_1": w_lt1 == 0,
        "A2_valuation_classes_span_wide_W": multi,
        "A2_valuation_uninformative_about_magnitude": valuation_uninformative,
        "A2_near_tie_surplus_v23": near_v23,
        "route_p_adic_applicable": False,
        "conjecture1_proved": False,
        "statement": ("W=Phi^{-11}=prod_v (621/64)((k_v+1)cav_v)^11, Phi<=1 <=> W>=1. W>=1 is ARCHIMEDEAN: "
                      "v23(W) is uncorrelated with W's magnitude (same v23 spans 10x+; near-tie surplus has "
                      "v23(W-1)=0 with no pattern), so NO p-adic/23-adic argument can prove it. The near-star "
                      "proof was 1-D real-analytic monotonicity + a boundary integer identity, which the "
                      "multivariate non-unimodal tree does not admit. Both flagged routes (smooth: pokes "
                      "+4.17e-5>0; p-adic: inapplicable) are dead; the genuine need is a valid real potential "
                      "tight at the tie = the accumulating-LP / marginal-tie open crux."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
