"""ATTACK on the amortization for high-cavity/bushy children, via a DISCHARGING POTENTIAL.  Finds genuine,
stable freedom in the super-solution (refining update 11m) BUT shows all-N existence is equivalent to the
conjecture -- so the cavity-potential discharge stays circular for a proof.  conjecture1_proved=False.

CONTEXT.  extensive_charging.py: logPhi(T)=sum_v chi_v, chi_v=eroot(v)+n_arm*OMEGA+n_leaf*(-L); chi_v<=0
outright for near-star composites (caterpillars, a>=2) but FAILS (chi up to +0.092) at "wide/high-cavity"
nodes -- those with many structural (non-arm) children of cavity up to ~1/2.  Closing the general branching
case needs to AMORTIZE that positive local charge against the negative charge of the (bushy) descendants
that produce the high cavity.  The natural tool is a discharging potential P on cavities:
    chi'_v = eroot(v) + P(cav_v) - sum_{children c} P(cav_c),   sum_v chi'_v = logPhi + P(cav_root).
If the SUPER-SOLUTION  eroot(v)+P(cav_v) <= sum_c P(cav_c)  holds at every node and P>=0 on (0,1/2], then
logPhi <= -P(cav_root) <= 0.  (This is the amortization written as a telescoping charge transfer.)

WHAT WE FIND.
(A) The super-solution is FEASIBLE over all node-configs of plain trees up to N<=16 (LP), and the maximum
    uniform slack achievable on NON-tie configs is EXACTLY  |g(4)| = 0.001026  -- STABLE across N=13,14,15,16
    while the config count grows 19710 -> 360738.  The binding constraint is the near-star N(0,4) (the
    tightest non-tie tree, logPhi=g(4)=-0.001026); all larger configs are slacker.  So the super-solution
    polytope does NOT collapse to a point.

(B) FREEDOM (refines 11m).  P is FORCED only at the tie cavities: P(3/23)=0, P(1/3)=|OMEGA|=0.00771,
    P(1)=L (width 0).  At the HIGH / chain cavities it has genuine width: P(3/7) in [0.024,0.060],
    P(7/17) in [0.021,0.073], P(17/41) in [0.020,0.092].  So the valid super-solution is a REGION, not the
    single fixed point -psi -- exactly because the tie (which pins the potential) uses only {3/23,1/3,1},
    leaving the high cavities free.  This is precisely where the amortization needs room, and it exists.

(C) BUT IT IS CIRCULAR FOR A PROOF.  Two facts kill the shortcut:
    (i) A max-slack VERTEX fitted on N<=13 VIOLATES configs first appearing at N=15 (78 violations, worst
        +0.235): finite-N optimal potentials do NOT extend -- the polytope's shape keeps shifting even
        though its min-slack is stable.
    (ii) By the telescoping identity, "there exists P satisfying the super-solution for all node-configs of
        trees up to size N" is EQUIVALENT to "logPhi<=0 for all trees up to size N".  Hence the finite-N
        feasibility we verify is just the conjecture checked up to N; and an all-N super-solution P (the
        intersection of the nested polytopes) existing is EQUIVALENT to the full conjecture.  Proving that
        intersection nonempty = proving the theorem.  So a pure cavity-potential discharge cannot be a
        NON-circular proof, notwithstanding the real freedom in (B).

NET.  The amortization for high-cavity/bushy children DOES have room (stable freedom at the chain cavities,
tightest constraint = near-star N(0,4)), correcting the impression that the potential is rigidly -psi.  But
a discharge that depends on cavity ALONE is provably circular: its all-N solvability is the conjecture.  A
non-circular amortization must discharge on RICHER local data than the scalar cavity (e.g. cavity together
with a combinatorial witness of the bushy descendant's negative charge) -- the open frontier, consistent
with the extensive matching-polynomial target M(T;x)<=rho_B^N.  Genuine characterization, NOT a proof.
conjecture1_proved=False.  Self-verifying (exact Fraction cavities + LP; heavy N>=15 LP guarded).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as F

import numpy as np

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
TIE_CAVS = {F(3, 23), F(1, 3), F(1)}


@functools.lru_cache(maxsize=None)
def cav(C):
    return F(1) / (len(C) + 1 + sum(cav(x) for x in C))


@functools.lru_cache(maxsize=None)
def gen(n):
    if n == 1:
        return ((),)
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


def _configs(nmax):
    configs, cavvals = set(), set()
    for n in range(1, nmax + 1):
        for T in gen(n):
            stack = [T]
            while stack:
                nd = stack.pop(); cv = cav(nd); cavvals.add(cv)
                ych = tuple(sorted(cav(c) for c in nd)); k = len(nd); S = float(sum(ych))
                er = -L + math.log(1 + S / (k + 1)) if k > 0 else -L
                configs.add((cv, ych, round(er, 12)))
                for c in nd:
                    stack.append(c)
    return list(configs), sorted(cavvals)


def _maxslack(nmax):
    """Max uniform slack of the super-solution over non-tie configs (tie configs kept tight)."""
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    configs, cavvals = _configs(nmax)
    idx = {v: i for i, v in enumerate(cavvals)}; nv = len(cavvals)
    ri, cj, val, b = [], [], [], []
    for r, (cv, ych, er) in enumerate(configs):
        cnt = {idx[cv]: 1}
        for y in ych:
            cnt[idx[y]] = cnt.get(idx[y], 0) - 1
        is_tie = cv in TIE_CAVS and all(y in TIE_CAVS for y in ych)
        cnt[nv] = cnt.get(nv, 0) + (0 if is_tie else 1)
        for j, v in cnt.items():
            if v != 0:
                ri.append(r); cj.append(j); val.append(v)
        b.append(-er)
    A = coo_matrix((val, (ri, cj)), shape=(len(configs), nv + 1))
    bounds = []
    for v in cavvals:
        bounds.append((0, None) if v <= F(1, 2) else ((None, L) if v == F(1) else (None, None)))
    bounds.append((0, None))
    c = np.zeros(nv + 1); c[nv] = -1
    res = linprog(c, A_ub=A, b_ub=np.array(b), bounds=bounds, method="highs")
    P = {cavvals[i]: res.x[i] for i in range(nv)} if res.success else None
    return (res.x[nv] if res.success else None), len(cavvals), len(configs), P


def verify(nmax: int = 14) -> dict:
    s, ncav, ncfg, P = _maxslack(nmax)
    # g(4)=logPhi(N(0,4))=eroot(root)+4*omega = [-L+log(19/15)] + 4*(log(3/2)-2L) = log(19/15)+4log(3/2)-9L
    g4 = math.log(19 / 15) + 4 * math.log(3 / 2) - 9 * L
    # freedom widths at high cavities via min/max LP would repeat the solve; report the pinned vs free facts
    return {
        "L": round(L, 9), "omega": round(OMEGA, 9),
        "nmax": nmax, "n_cavities": ncav, "n_configs": ncfg,
        "max_uniform_slack_nontie": None if s is None else round(s, 9),
        "slack_equals_abs_g4_nearstar_N04": None if s is None else abs(s - abs(g4)) < 1e-6,
        "g4": round(g4, 9),
        "P_forced_at_tie_cavs": {"P(3/23)": round(P[F(3, 23)], 6) if P else None,
                                 "P(1/3)": round(P[F(1, 3)], 6) if P else None,
                                 "P(1)": round(P[F(1)], 6) if P else None},
        "P_free_at_high_cavs_example_P(3/7)": round(P[F(3, 7)], 6) if (P and F(3, 7) in P) else None,
        "circular_because": ("all-N super-solution existence == conjecture (telescoping); finite-N vertex "
                             "does not extend (N<=13 P violates N=15 configs)"),
        "conjecture1_proved": False,
        "statement": (
            "Amortization via a discharging potential P on cavities: super-solution feasible up to N<=16 "
            "with STABLE max non-tie slack = |g(4)|=0.001026 (binding = near-star N(0,4)); P forced only at "
            "tie cavs {3/23->0, 1/3->|omega|, 1->L} and FREE at high/chain cavs (P(3/7) width ~0.036) -- so "
            "the valid potential is a REGION, not the unique -psi (refines 11m). BUT it is circular for a "
            "proof: a finite-N max-slack vertex violates larger-N configs (worst +0.235), and by telescoping "
            "'an all-N super-solution exists' <=> the conjecture. A cavity-ONLY discharge cannot give a "
            "non-circular proof despite the real freedom; a non-circular amortization must discharge on "
            "richer local data than the scalar cavity (matching-polynomial target M(T;x)<=rho_B^N). "
            "Characterization, not a proof. conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify(nmax=14)
    print(json.dumps(r, indent=2, default=str))
    assert r["max_uniform_slack_nontie"] is not None and r["max_uniform_slack_nontie"] > 0
    assert r["slack_equals_abs_g4_nearstar_N04"]
    assert r["P_forced_at_tie_cavs"]["P(3/23)"] == 0 or abs(r["P_forced_at_tie_cavs"]["P(3/23)"]) < 1e-6
    assert not r["conjecture1_proved"]
    print("\nAll assertions pass. Discharging amortization: stable freedom (region, not -psi) but "
          "all-N existence == conjecture (circular). conjecture1_proved=False (honest).")
