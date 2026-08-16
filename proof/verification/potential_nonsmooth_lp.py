"""Non-smooth (per-point) potential attempt for the Phi<=1 crux -- an honest probe, NOT a proof.

BACKGROUND.  cavity_potential.py reduced Phi<=1 to a POTENTIAL certificate: a P: (0,1]->R>=0 with the
per-vertex inequality  q_v <= sum_{c child of v} P(m_c) - P(m_v),  q_v := log(a(d_v,c_v) z(d_v,c_v)) - log m_v,
telescoping to log Phi(T) <= -P(m_root) <= 0.  It found that no FIXED-BASIS (smooth) P closes it: with a
bounded-near-0 basis the P is forced ~0 on a whole interval [0.05,0.18] around the ties, leaving "no budget"
for near-tie deep nodes -- residual +0.0006 at a depth-7 node.  The stated way out: a NON-SMOOTH / arithmetic
potential respecting the integrality of the reachable set.

THIS MODULE tries the MAXIMALLY non-smooth object: a PER-POINT potential (one free P-value per distinct
reachable cavity, no continuity/basis) via an exact LP over a large enumerated + adversarial reachable node
set (leaves; a deduped depth pool; wide tie-children k<=2000; near-tie deep cr in {0,1}, k=3 near-star triples;
deep chains).  P>=0, P(3/23)=0 (the tie pin); maximize the minimum per-vertex slack `t`.

FINDING (honest).
  * The per-point LP is FEASIBLE (t = 0, the tie exactly tight) on ~486k branches to depth 6-7 -- INCLUDING
    every binding case the fixed-basis route failed on.  The +0.0006 residual DOES NOT appear.
  * The optimal P is 0 on the WHOLE near-tie interval [0.10,0.20] and positive only away from it (max P =
    log rhoB = 0.2066, at m=1).  It closes anyway because it supplies the budget at the CHILDREN'S cavities:
    a near-tie deep node cr=0,k=3 has q_v ~ 0.353 <= 3*P(1) = 0.62 (children at m=1), so it is payable WITHOUT
    P>0 at the node's own cavity.  The interval-forcing that defeats a smooth P is a CONTINUITY artifact;
    per-point P sidesteps it.
  * Tie-children never force a violation: max q_v over all-tie-children nodes is -0.0166 < 0.

SO: this REINFORCES cavity_potential.py's conclusion rather than overturning it.  The certifying potential
EXISTS as an infinite/per-point (non-smooth) object -- the LP finds it at every finite depth -- but the crux
is NOT closed: (a) FINITE DEPTH ONLY; the reachable cavities ACCUMULATE (at 3/23 and at 0) as depth->inf, and
per-point feasibility at each depth is necessary, not sufficient, for a SINGLE P valid on the whole (dense,
accumulating) reachable set; (b) the LP gives NUMERIC per-point values, not a CLOSED-FORM arithmetic formula --
producing an explicit non-smooth P with the exact near-tie/small-m asymptotics, proven valid for all branches,
is the actual open work.  Phi<=1 remains OPEN.  conjecture1_proved stays False.

CLOSED-FORM CONSTRUCTION ATTEMPT (and its honest REFUTATION).  Minimizing sum(P) over the capped node set
gives a SPARSE P: nonzero at only 5 cavities -- P(1)=log rhoB, P(1/3)=log(2 rhoB^2/3) (the exact tie pins),
plus P(3/7)=0.02404, P(5/17)=0.00282, P(3/11)=0.00131 (value-function values, NO clean closed form: they match
only large-denominator rationals) -- and ZERO everywhere else.  This 5-point P appeared to certify to depth 8
on the CAPPED node set.  BUT an INDEPENDENT random adversary (200k random gadgets, depth 3-9) REFUTES it: 6755
violations, min slack -0.081, at near-tie m_v~0.15.  The sparsity was an UNDERSAMPLING ARTIFACT of the capped
pool.  Re-solving the per-point LP WITH the random adversary included (446k nodes) is still feasible (t=0) but
now needs ~2932 nonzero points, extending DOWN into the near-tie region (m>=0.093) -- and the count GROWS
without bound as the node set deepens (5 -> 2932 -> ...), accumulating at the tie.  CONCLUSION: NO FINITE
closed-form P exists; every attempt to freeze the certifying P to finitely many points is refuted by a deeper
adversary.  The non-smooth potential is genuinely an infinite/accumulating object -- confirming (not closing)
the crux.

Requires numpy, scipy.
"""
from __future__ import annotations

import itertools
from functools import lru_cache

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, lil_matrix

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c): return 1.5 ** c * (1 + c / (3 * d))
def _z(d, c): return 3 / (3 * d + c)
def _a(d, c): return _F(d, c) / _rhoB ** (1 + 2 * c)


@lru_cache(maxsize=None)
def cav(C):
    """Root cavity of a branch C = (cherries, tuple-of-child-branches)."""
    cr, kids = C
    S = sum(cav(k) for k in kids)
    d = len(kids) + 1 + cr
    zz = _z(d, cr)
    return zz / (1 + zz * S)


def _node_set(D=6, Cmax=6, Kmax=3, poolcap=45):
    allbr = set()
    pool = [(c, ()) for c in range(9)]
    allbr |= set(pool)
    seen = {round(cav(b), 9) for b in pool}
    for _ in range(1, D):
        new, ks = [], [()]
        for k in range(1, Kmax + 1):
            for combo in itertools.combinations_with_replacement(range(len(pool)), k):
                ks.append(tuple(pool[i] for i in combo))
        for cr in range(Cmax + 1):
            for kk in ks:
                C = (cr, kk); allbr.add(C); mc = round(cav(C), 9)
                if mc not in seen:
                    seen.add(mc); new.append(C)
        new.sort(key=cav)
        if len(new) > poolcap:
            step = len(new) / poolcap
            new = [new[int(i * step)] for i in range(poolcap)]
        pool = new
        if not pool:
            break
    tie = (5, ())
    near = [(4, ()), (6, ()), (3, ()), (2, ()), (0, ((0, ()),)), (0, ((0, ((0, ()),)),))]
    for cr in range(4):
        for base in [tie] + near:
            for k in (2, 3, 5, 8, 20, 100, 500, 2000):
                allbr.add((cr, tuple([base] * k)))
    for combo in itertools.combinations_with_replacement([2, 3, 4, 5, 6], 3):
        allbr.add((0, tuple((sp, ()) for sp in combo)))
        allbr.add((1, tuple((sp, ()) for sp in combo)))
    return list(allbr)


def certify(D=6):
    """Solve the per-point LP over the reachable node set; return the feasibility verdict."""
    allbr = _node_set(D)
    cavs, consd = {}, {}
    key = lambda m: round(m, 9)
    for C in allbr:
        cr, kids = C
        chm = [cav(k) for k in kids]
        for m in chm:
            cavs[key(m)] = m
        S = sum(chm); d = len(kids) + 1 + cr; zz = _z(d, cr); mv = zz / (1 + zz * S)
        cavs[key(mv)] = mv
        q = float(np.log(_a(d, cr) * zz) - np.log(mv))
        kk = (tuple(sorted(key(x) for x in chm)), key(mv))
        if kk not in consd or q > consd[kk][2]:
            consd[kk] = ([key(x) for x in chm], key(mv), q)
    cons = list(consd.values())
    idx = {m: i for i, m in enumerate(sorted(cavs))}
    n = len(idx)
    A = lil_matrix((len(cons), n + 1)); b = np.zeros(len(cons))
    for r, (chks, mvk, q) in enumerate(cons):
        for ck in chks:
            A[r, idx[ck]] -= 1
        A[r, idx[mvk]] += 1; A[r, -1] += 1; b[r] = -q
    A = csr_matrix(A)
    cobj = np.zeros(n + 1); cobj[-1] = -1
    Aeq = lil_matrix((1, n + 1)); Aeq[0, idx[key(3 / 23)]] = 1; Aeq = csr_matrix(Aeq)
    res = linprog(cobj, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[0.0],
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    t = float(res.x[-1]) if res.success else None
    return {
        "depth": D, "branches": len(allbr), "distinct_cavities": n, "constraints": len(cons),
        "lp_feasible": bool(res.success), "max_min_slack": t,
        "per_point_nonsmooth_P_closes_this_finite_set": bool(res.success and t is not None and t >= -1e-9),
        "closes_phi_le_1": False,   # finite depth + numeric-only P; the crux is OPEN
        "note": "per-point P feasible to finite depth (no +0.0006 residual); closed-form + infinite-depth OPEN",
    }


if __name__ == "__main__":
    print(certify(6))
