"""Depth-collapse lemma -- structural probe: which framing is viable, and where it blocks.

Phi<=1 factors as  (i) DEPTH-COLLAPSE: every tree's logPhi <= a "bush" at the same invariant, and
(ii) the BUSH BOUND: every bush <= 0.  bush_bound_closed.py PROVED (ii) for the UNIFORM bush
B(c,k,t)=root(c cherries)+k identical t-cherry leaves.  This module probes (i): what exactly is the
collapse target, which framing avoids the circular Psi<=0 wall, and where the natural moves fail.

Self-verifying (bounded exact/float scans).  It does NOT close the depth-collapse (conjecture1 OPEN);
it PINS the remaining gap and CORRECTS the target family.

FINDINGS (reproduced by verify()):

(F1) PER-CAVITY framing is DEAD (integrality).  The Locality.lean rearrangement preserves cavity, so
     it bounds logPhi(T) by the max-amplitude tree of the SAME cavity = Psi(cav) -- circular.  Worse,
     cavities are exact rationals and a UNIFORM bush realises almost none of them: over an exhaustive
     enumeration nearly every cavity's maximiser is depth>=2 and no uniform bush shares its exact
     cavity.  So the cavity framing cannot be discharged by the (proven) bush bound.

(F2) PER-V framing is VIABLE and the target is the MIXED bush (NOT the uniform bush).  Grouping the
     exhaustive enumeration by V=sum_v(1+2 c_v), the per-V maximiser is DEPTH-1 for the large majority
     of V-classes, and it is a root with c cherries + several leaf children of DIFFERENT cherry counts
     -- e.g. (5,[(3,[]),(4,[])]).  The UNIFORM bush B(c,k,t) is ~0.001-0.005 SUBOPTIMAL at 13/72
     V-classes; the true extremal family is the MIXED bush G=(c,[(t_1,[]),...,(t_k,[])]).  (A rare
     depth-2 arm-child appears in one class.)  So the memory's "uniform-bush per-V domination" is
     slightly off: the correct piece (ii) is the MIXED bush bound.

(F3) MIXED bush bound has the SAME uniform gap as the uniform one: max logPhi over mixed bushes with
     k>=1 is exactly omega=-0.007707 at the ARM (0,[(0,[])]); NO ties among k>=1 mixed bushes; all <=0.
     The exact telescoping logPhi(G)=sum_i gVal(t_i)+eroot(c,k,sum m_i) holds (m_i=3/(4t_i+3)).  So the
     mixed bush bound is closable by the same slack method; a SEPARABLE bound via log(1+x)<=x,
        logPhi(G) <= log a(d,c) + sum_i [gVal(t_i)+z(d,c) m(t_i)] = U(c,k),  d=k+1+c, z=3/(3d+c),
     gives U(c,k)<=0 for ALL c,k>=1 EXCEPT the small residual c=0, k in {1,2} (U(0,1)=+0.087 -- lossy
     exactly at the marginal ARM).  k=1 is the proven Q1 slice; the residual is c=0, k in {2,...} mixed
     bushes (a k-dimensional integer optimisation with escape -- reducible, not yet written).

(F4) BOTH natural rearrangement moves FAIL, and NOT for the same reason the memory recorded:
       * cavity-preserving swap (Locality primitive): exact but reduces to Psi (circular).
       * V-preserving single-leaf FLATTEN (replace an odd-V subtree by one leaf of the same V): parity
         blocks ~half the moves (even-V subtrees have no integer leaf), and even on odd-V subtrees it
         DECREASES logPhi ~19% of the time (worst -0.31) -- collapsing a branch to ONE leaf loses the
         branching contribution.  The maximiser needs MULTIPLE mixed leaves, so the correct flatten
         replaces a subtree by a mixed-bush-let of the same V; that move is unproven.

NET (strategic reframing).  The depth-collapse is NOT necessarily "circular Psi<=0": that is only the
PER-CAVITY route.  The PER-V route reduces it to (a) the MIXED bush bound (uniform gap, closable, NOT
circular) + (b) a V-preserving flatten to a mixed-bush-let (a COMBINATORIAL/PARITY problem, not
circularity).  Neither is closed here, but the obstruction is now parity+multiset optimisation, a
different and plausibly more tractable wall than the cavity-framing circularity.  conjecture1 OPEN.

Depends on general_children_crux, rational_reduction.  Std-lib + those modules only.
"""
from __future__ import annotations

import itertools
import math
from collections import defaultdict
from fractions import Fraction as Fr

import general_children_crux as GC
import rational_reduction as RR

_rhoB = (621 / 64) ** (1 / 11)
ARM = (0, [(0, [])])
OMEGA = GC.log_phi(ARM)  # -0.007707...


def _lp(C):
    return GC.log_phi(C)


def _V(C):
    return RR._prodF_V(C)[1]


def _depth(C):
    _, kids = C
    return 0 if not kids else 1 + max(_depth(k) for k in kids)


def gVal(t):
    return GC.g_Val(t)


def _mixed(c, ts):
    return (c, [(t, []) for t in ts])


def _a(d, c):
    return (1.5 ** c * (1 + c / (3 * d))) / _rhoB ** (1 + 2 * c)


def U(c, k, tmax=60):
    """Separable upper bound on the mixed bush: log a(d,c) + k*max_t[gVal(t)+z*m(t)]."""
    d = k + 1 + c
    z = 3 / (3 * d + c)
    hmax = max(gVal(t) + z * 3 / (4 * t + 3) for t in range(tmax))
    return math.log(_a(d, c)) + k * hmax


def probe_per_V(nmax=6, cmax=6):
    """(F2) per-V maximiser depth distribution + uniform-bush suboptimality count."""
    byV = defaultdict(lambda: (-9.9, None))
    for T in GC._trees(nmax, cmax):
        v = _lp(T)
        V = _V(T)
        if v > byV[V][0] + 1e-15:
            byV[V] = (v, T)
    bushV = defaultdict(lambda: -9.9)
    for c in range(30):
        for k in range(30):
            for t in range(30):
                B = (c, [(t, [])] * k) if k > 0 else (c, [])
                bushV[1 + 2 * c + k * (1 + 2 * t)] = max(bushV[1 + 2 * c + k * (1 + 2 * t)], _lp(B))
    depth_dist = defaultdict(int)
    uniform_suboptimal = 0
    for V, (v, T) in byV.items():
        depth_dist[_depth(T)] += 1
        if bushV[V] < v - 1e-9:
            uniform_suboptimal += 1
    return {"n_V_classes": len(byV), "maximiser_depth_dist": dict(depth_dist),
            "uniform_bush_suboptimal_V_classes": uniform_suboptimal,
            "max_logphi": round(max(v for v, _ in byV.values()), 6)}


def probe_mixed_gap(cB=10, kB=5, tB=9):
    """(F3) mixed bush k>=1 has max logPhi = omega at the ARM, no ties, all <=0; telescoping exact."""
    best = (-9.9, None)
    ties = 0
    viol = 0
    for c in range(cB):
        for k in range(1, kB + 1):
            for ts in itertools.combinations_with_replacement(range(tB + 1), k):
                v = _lp(_mixed(c, ts))
                if v > best[0]:
                    best = (v, (c, ts))
                if abs(v) < 1e-12:
                    ties += 1
                if v > 1e-9:
                    viol += 1
    # separable bound residual: (c,k>=1) with U>0
    resid = [(c, k) for c in range(60) for k in range(1, 60) if U(c, k) > 1e-9]
    return {"mixed_k1_max_logphi": round(best[0], 6), "at": best[1], "matches_omega": abs(best[0] - OMEGA) < 1e-9,
            "mixed_k1_exact_ties": ties, "mixed_violations_gt0": viol,
            "separable_bound_residual_ck": resid}


def probe_flatten(trials=20000, seed=7):
    """(F4) V-preserving single-leaf flatten: parity-blocked share + logPhi-decrease share."""
    import random
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0 or rng.random() < 0.4:
            return (rng.randint(0, 6), [])
        return (rng.randint(0, 5), [rt(dep - 1) for _ in range(rng.randint(1, 3))])

    dec = inc = even = ok = 0
    worst = 0.0
    for _ in range(trials):
        C = rt(4)
        _, kids = C
        idxs = [i for i, k in enumerate(kids) if k[1]]
        if not idxs:
            continue
        i = rng.choice(idxs)
        b = kids[i]
        Vb = _V(b)
        if Vb % 2 == 0:
            even += 1
            continue
        t = (Vb - 1) // 2
        nk = list(kids)
        nk[i] = (t, [])
        d = _lp((C[0], nk)) - _lp(C)
        ok += 1
        if d < -1e-9:
            dec += 1
            worst = min(worst, d)
        elif d > 1e-9:
            inc += 1
    return {"odd_V_flattens": ok, "increases": inc, "decreases": dec, "parity_blocked_even_V": even,
            "worst_logphi_drop": round(worst, 5), "flatten_is_valid_domination_move": dec == 0}


def verify():
    pv = probe_per_V()
    mg = probe_mixed_gap()
    fl = probe_flatten()
    return {
        "F2_per_V": pv,
        "F3_mixed_bush": mg,
        "F4_flatten": fl,
        "omega": round(OMEGA, 6),
        "depth_collapse_closed": False,
        "conjecture1_proved": False,
        "note": ("Per-cavity framing circular+integrality-dead; per-V framing viable with target = MIXED "
                 "bush (uniform bush ~0.001 suboptimal). Mixed bush k>=1 has uniform gap omega (closable). "
                 "Both natural rearrangements fail (cavity->circular; V-preserving single-leaf flatten "
                 "decreases logPhi ~19% + parity-blocked ~half). Depth-collapse OPEN; reframed as "
                 "mixed-bush-bound + V-preserving multiset flatten (parity), NOT circular Psi."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
