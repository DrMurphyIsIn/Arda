"""Invariant-MEASURE dual of Phi<=1 -- the occupation-measure LP, and what it reveals (a run, not a proof).

The nonlinear-JSR audit (nonlinear_jsr_probe.py) flagged the ONE untried ingredient: the invariant-
measure dual on the tie variety.  This module builds and solves it.

FORMULATION.  logPhi(T) = sum_v eroot(v), eroot(v)=log a(d,c)+log(1+z*S), S=sum child cavities.  An
OCCUPATION MEASURE x over node-configs (c, k, child-cavity multiset) is a stationary distribution of
node-types in a tree.  FLOW conservation (each node is produced once as an output cavity and consumed
once as a child) reads, per cavity mu:
    sum_config x[config] 1[out(config)=mu]  =  sum_config x[config] * (#children of config at mu).
Summing over mu forces  sum_config x*k = sum_config x*1 = 1, i.e. MEAN OFFSPRING = 1: the extremal
measure is a CRITICAL branching process -- exactly the "boundary/critical smoothing transform".
The invariant-measure dual is the LP
    maximize  sum_config x[config] * eroot(config)   s.t. flow(mu)=0 all mu,  sum x = 1,  x>=0.

FINDINGS (verify(), scipy LP on a reachable-cavity discretization; exact eroot):
 (M1) MAX average eroot = ~ -0.003, STABLE and rising toward 0 as the discretization refines
      (-0.00335, -0.00322, -0.00300 at |M|=42,71,103).  It does NOT exceed 0.
 (M2) the maximizing measure is FINITELY SUPPORTED (~5 configs) and has MEAN OFFSPRING EXACTLY 1
      (e.g. leaf k=0 mass .40, arm k=1 mass .40, branching k=3 mass .20 -> mean k = 1.0): a critical
      branching measure, the near-star tie structure (leaves + arms + branch).
 (M3) LP DUALITY: the dual of this measure LP is a per-point POTENTIAL V on the finite cavity set with
      eroot - V(out) + sum V(children) <= opt for every config -- exactly the sub-action /
      cavity_potential.py object, feasible on finite truncations (potential_nonsmooth_lp.py).

HONEST STATUS -- this is a RUN, NOT a proof.  The LP restricts to a FINITE config set (bounded c,k;
children cavities in a finite M; out-cavity snapped), so its optimum is a LOWER bound on the true
max-over-all-invariant-measures (which is 0, attained by the tie).  A restriction cannot certify
"<= 0".  The matching UPPER bound is the dual potential, which must extend to the DENSE, ACCUMULATING
cavity set -- the same infinite-limit wall every prior route hit.  What the invariant-measure view
ADDS is structural and genuinely useful: the extremal object is a FINITELY-SUPPORTED CRITICAL (mean-
offspring-1) branching measure = the tie, with NO accumulation in the MEASURE (only in the potential).
So the promising direction is a rigorous "the critical branching measure is the unique maximiser"
argument (branching-process / smoothing-transform boundary theory), not a potential.  Phi<=1 OPEN.

Requires scipy (verify() returns {"skipped": ...} if unavailable).
"""
from __future__ import annotations

import itertools
import math


def eroot(c, k, S):
    d = k + 1 + c
    z = 3 / (3 * d + c)
    a = (1.5 ** c * (1 + c / (3 * d))) / (621 / 64) ** ((1 + 2 * c) / 11)
    return math.log(a) + math.log(1 + z * S)


def outmu(c, k, S):
    return 3 / (3 + 3 * k + 4 * c + 3 * S)


def _leaf_cav(c):
    return 3 / (4 * c + 3)


def solve(res_dec=3, cap=42, CMAX=6):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import lil_matrix
    M = set(round(_leaf_cav(c), res_dec) for c in range(0, 30))
    for _ in range(5):
        Ms = sorted(M)
        add = set()
        for c in range(0, 7):
            for k in (1, 2, 3):
                sub = Ms if len(Ms) < 20 else Ms[::max(1, len(Ms) // 20)]
                for combo in itertools.combinations_with_replacement(sub, k):
                    add.add(round(outmu(c, k, sum(combo)), res_dec))
        M |= add
    M = sorted(M)
    tie = round(3 / 23, res_dec)
    if len(M) > cap:
        keep = set(M[::max(1, len(M) // (cap - 8))])
        keep.add(tie)
        keep.update(round(_leaf_cav(c), res_dec) for c in range(0, 8))
        M = sorted(keep)
    if tie not in M:
        M.append(tie)
        M = sorted(M)
    idx = {m: i for i, m in enumerate(M)}
    nM = len(M)
    def snap(x):
        return M[min(range(nM), key=lambda j: abs(M[j] - x))]
    configs = []
    for c in range(0, CMAX + 1):
        configs.append((c, 0, snap(outmu(c, 0, 0.0)), eroot(c, 0, 0.0), ()))
        for k in (1, 2, 3):
            for combo in itertools.combinations_with_replacement(M, k):
                S = sum(combo)
                configs.append((c, k, snap(outmu(c, k, S)), eroot(c, k, S), combo))
    nC = len(configs)
    A = lil_matrix((nM + 1, nC))
    b = np.zeros(nM + 1)
    obj = np.zeros(nC)
    for j, (c, k, om, er, combo) in enumerate(configs):
        obj[j] = -er
        A[idx[om], j] += 1.0
        for mu in combo:
            A[idx[snap(mu)], j] -= 1.0
        A[nM, j] = 1.0
    b[nM] = 1.0
    res = linprog(obj, A_eq=A.tocsr(), b_eq=b, bounds=[(0, None)] * nC, method="highs")
    opt = None if res.x is None else -res.fun
    mean_k = None
    supp = []
    if res.x is not None:
        mass = res.x
        mean_k = float(sum(mass[j] * configs[j][1] for j in range(nC)))
        supp = sorted([(configs[j][0], configs[j][1], round(configs[j][3], 4), round(mass[j], 4))
                       for j in range(nC) if mass[j] > 1e-5], key=lambda t: -t[-1])
    return {"nM": nM, "nC": nC, "max_avg_eroot": None if opt is None else round(opt, 6),
            "mean_offspring": None if mean_k is None else round(mean_k, 6), "support": supp}


def verify():
    try:
        import scipy  # noqa: F401
    except Exception as e:  # pragma: no cover
        return {"skipped": f"scipy unavailable: {e}", "conjecture1_proved": False}
    r = solve(res_dec=3, cap=42)
    return {
        "lp": r,
        "opt_le_0": (r["max_avg_eroot"] is not None and r["max_avg_eroot"] <= 1e-9),
        "mean_offspring_is_1": (r["mean_offspring"] is not None and abs(r["mean_offspring"] - 1.0) < 1e-4),
        "finitely_supported": (len(r["support"]) <= 12),
        "depth_collapse_closed": False,
        "conjecture1_proved": False,
        "note": ("Invariant-measure dual: max avg eroot ~ -0.003 (->0 from below as M refines), maximiser "
                 "is a FINITELY-SUPPORTED CRITICAL branching measure (mean offspring = 1) = the tie. This "
                 "is a RUN not a proof: the LP is a finite RESTRICTION => its optimum LOWER-bounds the true "
                 "max (=0), so it cannot certify <=0; its dual is the per-point potential (dense/accumulating "
                 "= the wall). Value added: the extremal object is a finite critical measure with no "
                 "accumulation in the MEASURE -> the promising rigorous route is a smoothing-transform / "
                 "branching-process boundary uniqueness argument, not a potential. conjecture1 OPEN."),
    }


if __name__ == "__main__":
    import json
    print(json.dumps(verify(), indent=2, default=str))
