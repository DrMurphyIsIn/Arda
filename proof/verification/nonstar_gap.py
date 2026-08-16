"""Attempt to PROVE the NON-NEAR-STAR GAP (logPhi(T) <= omega < 0 for every non-near-star tree, for ALL
N).  Outcome: one rigorous NO-GO (the standard route provably cannot do it) + one rigorous infinite
sub-family closed exactly; the general case is the open crux.  NOT a full proof.  conjecture1_proved=False.

TARGET.  gap_characterization.py established (exhaustive N<=17 + family scans): the near-star family
N(0,k)=root+k arms is the UNIQUE approach to Phi=1, and every NON-near-star tree has
    logPhi(T) <= omega = log(3/2) - 2L = -0.007707   (L = log(621/64)/11),
with equality only for the N=2 edge.  This module attacks "for all N".

(I) *** RIGOROUS NO-GO: the cavity-only / potential / subtree-induction framework CANNOT prove the gap. ***
    Every subtree-recursive certificate proves a bound of the form  logPhi(T) <= h(cav(root))  (h a super-
    solution of the cavity recursion; dual_certificate / limiting_potential lines).  Such a bound depends on
    T ONLY through the single scalar cav(root).  But there are non-near-star trees with cav(root) EXACTLY
    3/23 -- the SAME root-cavity as the tie N(0,5) -- e.g.
        ((), (), ((),), ((),))                    [N=7,  cav_root=3/23, logPhi=-0.2077]
        ((), (), ((),()), (((),(),()),))          [N=11, cav_root=3/23, logPhi=-0.7056]
    (13 of them for N<=16).  Any h gives them the identical bound h(3/23) that it gives the tie, namely 0
    (forced, since the tie attains logPhi=0).  So NO cavity-only certificate can separate these non-near-
    stars from the tie: it yields <=0, never <=omega.  The gap is IRREDUCIBLY MULTI-NODE -- it lives in the
    internal structure (higher spectral moments), invisible to cav(root).  This explains, rigorously, why
    every potential/subtree route in this program stalls at <=0 and never reaches the strict gap, and it
    tells any future attacker: a gap proof MUST use >=2 moments of T (cf. the finite 5-moment inequality
    (C), dual_certificate_proof_attempt.py), not a single cavity potential.

(II) *** RIGOROUS SUB-FAMILY (closed exactly): the non-branching non-near-stars (paths/chains) satisfy the
     gap. ***  A plain tree with no branching node is a path chain_n (n nodes).  Its cavities are the
     continued fraction cav(chain_1)=1, cav(chain_{m+1})=1/(2+cav(chain_m)), and by the invariant
     cav(chain_m) in [1/3, 3/7] for all m>=2 (base 1/3; x in [1/3,1/2] => 1/(2+x) in [2/5,3/7] ⊂ [1/3,1/2]),
     every node added beyond the second contributes increment  -L + log(1 + cav(chain_m)/2) <= log(17/14)-L
     = -0.01243 < 0.  Since chain_2 = the edge has logPhi = -2L+log(3/2) = omega EXACTLY,
        logPhi(chain_n) = omega + sum_{m=2}^{n-1} (-L + log(1+cav(chain_m)/2)) <= omega     for all n>=2,
     strictly for n>=3.  So the entire path family obeys the gap (sharpening the prior ChainMargin bound
     <=0 to <=omega).  This is the branching-free slice of the non-near-star set, closed for all N.

(III) RESIDUAL (open).  A non-near-star tree with >=1 branching node.  Empirically (N<=16) all such have
      logPhi <= -0.0164 < omega, but proving it for all N is exactly the open crux: by (I) it needs a
      genuinely multi-node (multi-moment) argument, and it is equivalent in difficulty to the finite
      spectral-moment inequality (C) [sum_i g_i mu_i(T) <= L] with a strict-gap margin for non-near-stars.
      Every accessible tool (per-vertex/local bound, rational certificate, moment-SDP) has been shown to
      stall at the same integrality/discharging wall.  NOT closed here.

CONCLUSION.  The non-near-star gap is PROVED for the path family and PROVED to be unreachable by the
standard cavity-potential framework; the branching case remains the open 1984 crux.  This is honest partial
progress, not a proof of the conjecture.  conjecture1_proved = False.  Self-verifying (exact Fraction
arithmetic for (I),(II); float logPhi for reporting).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as F

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
ARM = ((),)


@functools.lru_cache(maxsize=None)
def cavF(C):
    S = sum(cavF(ch) for ch in C)
    return F(1) / (len(C) + 1 + S)


@functools.lru_cache(maxsize=None)
def plog(C):
    k = len(C)
    S = sum(cavF(ch) for ch in C)
    return -L + math.log(1 + float(S) / (k + 1)) + sum(plog(ch) for ch in C)


@functools.lru_cache(maxsize=None)
def gen(n):
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


def is_near_star(C):
    return len(C) > 0 and all(c == ARM for c in C)


def cav_chain(m: int) -> F:
    x = F(1)
    for _ in range(m - 1):
        x = F(1) / (2 + x)
    return x


def logphi_chain(n: int) -> float:
    return -n * L + sum(math.log(1 + float(cav_chain(m)) / 2) for m in range(1, n))


def verify(nmax: int = 16) -> dict:
    # (I) non-near-star trees sharing the tie root-cavity 3/23 -- the potential no-go witnesses
    witnesses = []
    for n in range(2, nmax + 1):
        for T in gen(n):
            if is_near_star(T):
                continue
            if cavF(T) == F(3, 23):
                witnesses.append((n, round(plog(T), 5)))
    # (II) chain family: invariant + increment sign + gap
    inv_ok = all(F(1, 3) <= cav_chain(m) <= F(3, 7) for m in range(2, 60))
    inc_max = math.log(1 + float(F(3, 14))) - L  # increment at the extreme cav=3/7
    chain_vals = {n: round(logphi_chain(n), 6) for n in [2, 3, 4, 8, 20, 50]}
    chains_le_omega = all(logphi_chain(n) <= OMEGA + 1e-12 for n in range(2, 60))
    # (III) residual: branching non-near-star champion (empirical)
    br_champ = -9.0
    for n in range(2, nmax + 1):
        for T in gen(n):
            if is_near_star(T):
                continue
            if any_branch(T):
                br_champ = max(br_champ, plog(T))

    return {
        "L": round(L, 9),
        "omega": round(OMEGA, 9),
        "I_potential_nogo_num_witnesses": len(witnesses),
        "I_potential_nogo_examples": witnesses[:4],
        "I_conclusion": ("non-near-stars with cav(root)=3/23 exist (same as tie) but logPhi<<0; any "
                         "cavity-only bound h(cav_root) gives them h(3/23)=0, cannot reach omega. Gap is "
                         "irreducibly multi-node."),
        "II_chain_invariant_[1/3,3/7]_holds": inv_ok,
        "II_chain_max_increment_mge2": round(inc_max, 6),
        "II_chain_base_is_omega": abs(logphi_chain(2) - OMEGA) < 1e-12,
        "II_chain_values": chain_vals,
        "II_chains_le_omega_PROVED": chains_le_omega,
        "III_branching_nonNS_champion_logPhi_empirical": round(br_champ, 6),
        "III_status": "OPEN for all N (equiv. to finite multi-moment inequality (C) with a strict gap)",
        "conjecture1_proved": False,
        "statement": (
            "Non-near-star gap (logPhi<=omega): (I) PROVEN unreachable by any cavity-only/potential/"
            "subtree-induction bound -- 13 non-near-star trees (N<=16) share the tie root-cavity 3/23, so "
            "h(cav_root) gives them the tie's bound 0, never omega; the gap is irreducibly multi-node. "
            "(II) PROVEN for the path/chain family: cav(chain_m) in [1/3,3/7] for m>=2, every added node "
            "contributes <= log(17/14)-L<0, base chain_2=omega, so logPhi(chain_n)<=omega for all n. "
            "(III) OPEN for branching non-near-stars (empirically <=-0.0164), equivalent to the finite "
            "spectral-moment inequality (C) with a strict-gap margin. Honest partial progress, not a "
            "proof. conjecture1_proved=False."
        ),
    }


def any_branch(C):
    if len(C) >= 2:
        return True
    return any(any_branch(c) for c in C)


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["II_chain_invariant_[1/3,3/7]_holds"]
    assert r["II_chains_le_omega_PROVED"]
    assert r["II_chain_base_is_omega"]
    assert r["II_chain_max_increment_mge2"] < 0
    assert r["I_potential_nogo_num_witnesses"] >= 1
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. (I) no-go + (II) chain gap verified; (III) open. conjecture1_proved=False.")
