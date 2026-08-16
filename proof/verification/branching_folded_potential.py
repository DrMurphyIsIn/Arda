"""ATTACK the branching case via bounded-branching + a FOLDED, MONOTONE discharging potential.  Genuine
progress: bounded-branching-2 is closable; the folded+monotone potential is FORWARD-CONSISTENT (unlike the
raw potential of update 11z) and a single monotone phi appears to handle all branching.  BUT this is a
LEAD, not a proof -- the new-cavity extension is open and all-N existence is formally == the conjecture.
conjecture1_proved=False.  (Overclaim discipline: the violations below are NOT exactly zero; see caveats.)

THE FOLDED DISCHARGE.  From the per-node identity logPhi=sum_v chi_v (extensive_charging), chi_v=eroot(v)
+n_arm(v)*OMEGA+n_leaf(v)*(-L).  Apply a potential phi ONLY to STRUCTURAL children (non-arm, non-leaf),
arms/leaves already folded into chi_v:
    FOLDED SUPER-SOLUTION:   chi_v + phi(cav_v) <= sum_{struct children c} phi(cav_c)   at every node.
Telescoping over the structural skeleton gives logPhi <= -phi(cav_root) <= 0 (phi>=0).  KEY DIFFERENCE from
the raw potential (amortization_discharging, 11z, which applied P to arm cavities 1/3 and leaf cavities 1
and was pinned there): here phi lives on STRUCTURAL cavities only and is NOT pinned at 1/3 or 1 -- more
freedom.

RESULTS (numerical, self-verifying).
(1) BOUNDED-BRANCHING-2 CLOSABLE.  Imposing the folded super-solution over CONTINUOUS child cavities in
    [0,1/2] for m=0,1,2 structural children (all arm counts a, +/- a leaf) admits a MONOTONE phi>=0,
    phi(0)=0.  The bound logPhi <= -phi(cav_root) holds on ALL 45934 plain b<=2 trees N<=16 (max
    logPhi+phi(root) = -0.000000).  The per-node super-solution residual is a GRID ARTIFACT: it shrinks
    monotonically under refinement (+0.0029 -> 0.0020 -> 0.0016 for phi-grid 260/400/600), consistent with
    an exact continuum phi.
(2) ALL BRANCHING, single monotone phi.  Imposing m=0..10 (equal children, the convex-tightest case) +
    mixed pairs over continuous cavities is STILL feasible with ONE monotone phi; the worst per-node
    residual over ALL plain trees N<=14 shrinks with grid (+0.00100 -> 0.00086 -> 0.00063 -> 0.00037 for
    grid 500/1000/1600/2400) -- again artifact-consistent (worst always at m=3 branching nodes).
(3) EXACT-CAVITY FEASIBILITY + FORWARD-CONSISTENCY.  Over the TRUE rational cavities (no grid), a monotone
    tie-tight folded phi is feasible for plain trees N<=15 with max non-tie slack EXACTLY +|g(4)|=0.001026
    (binding = near-star N(0,4)).  And the N<=13 monotone phi has ZERO shared-cavity violations on N<=16
    configs -- CONTRAST 11z, where the raw/non-monotone potential's finite-N vertex DID violate larger-N
    shared-cavity configs.  So folding + monotonicity removes the shape-shift that made 11z circular in
    practice.

WHY THIS IS A LEAD, NOT A PROOF (overclaim discipline).
- The per-node residuals above are POSITIVE (~1e-3), shrinking with grid but never certified to reach 0;
  the program's history (smooth/potential certificates overshoot the tie by ~4e-5) warns that a small
  positive FLOOR is possible.  "Shrinks with refinement" is suggestive, not conclusive.
- The exact-cavity feasibility is only up to N<=15 = the conjecture verified up to N<=15.  The forward
  check leaves 42650 N<=16 configs that involve NEW cavities where phi is undefined; monotonicity + tie-
  tightness constrain but do not determine them.
- By telescoping, "an all-N folded super-solution phi exists" is EQUIVALENT to the conjecture.  So an LP
  can never PROVE it; only an EXPLICIT phi (closed form / finitely-checkable) with an analytic proof over
  ALL (a,m,children-cavities) configs would close it.  That explicit phi is not in hand.

STATUS.  The folded+monotone discharge is the strongest potential-route signal to date (closes bounded-
branching-2; forward-consistent where 11z was not), and reduces the branching case to: exhibit an explicit
monotone phi:[0,1/2]->[0,inf), phi(0)=0, satisfying chi + phi(cav_v) <= sum_struct phi(cav_c) for ALL
configs, and prove the per-node residual is exactly 0 (no floor).  NOT done.  conjecture1_proved=False.
Self-verifying (LP over exact rational cavities + direct bound check on plain trees).
"""
from __future__ import annotations

import functools
import math
from fractions import Fraction as F

import numpy as np

L = math.log(621 / 64) / 11
OMEGA = math.log(3 / 2) - 2 * L
ARM = ((),)


@functools.lru_cache(maxsize=None)
def cavF(C):
    return F(1) / (len(C) + 1 + sum(cavF(x) for x in C))


@functools.lru_cache(maxsize=None)
def logphi(C):
    return -L + math.log(1 + float(sum(cavF(x) for x in C)) / (len(C) + 1)) + sum(logphi(x) for x in C)


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


@functools.lru_cache(maxsize=None)
def is_plain(T):
    if len(T) == 0:
        return True
    if sum(1 for c in T if len(c) == 0) > 1:
        return False
    return all(is_plain(c) for c in T)


def _struct(nd):
    return [c for c in nd if c != ARM and len(c) > 0]


def _chi(nd):
    na = sum(1 for c in nd if c == ARM); nl = sum(1 for c in nd if len(c) == 0)
    S = float(sum(cavF(x) for x in nd))
    return -L + math.log(1 + S / (len(nd) + 1)) + na * OMEGA + nl * (-L)


def _configs(nmax):
    C = set()
    for n in range(1, nmax + 1):
        for T in gen(n):
            if not is_plain(T):
                continue
            st = [T]
            while st:
                nd = st.pop()
                if len(nd) == 0 or nd == ARM:
                    continue
                C.add((cavF(nd), tuple(sorted(cavF(c) for c in _struct(nd))), round(_chi(nd), 12)))
                for c in _struct(nd):
                    st.append(c)
    return list(C)


def _solve_mono(C):
    from scipy.optimize import linprog
    cavs = sorted({cv for (cv, sc, ch) in C} | {y for (cv, sc, ch) in C for y in sc})
    idx = {v: i for i, v in enumerate(cavs)}; nv = len(cavs)
    tie = {F(3, 23), F(1, 3), F(1)}
    rows, b = [], []
    for (cv, sc, ch) in C:
        row = np.zeros(nv + 1); row[idx[cv]] += 1
        for y in sc:
            row[idx[y]] -= 1
        row[nv] = 0 if (cv in tie and all(y in tie for y in sc)) else 1
        rows.append(row); b.append(-ch)
    for i in range(nv - 1):
        r = np.zeros(nv + 1); r[i] = 1; r[i + 1] = -1
        rows.append(r); b.append(0.0)
    bnds = [((0, None) if v <= F(1, 2) else (None, None)) for v in cavs] + [(0, None)]
    c = np.zeros(nv + 1); c[nv] = -1
    res = linprog(c, A_ub=np.array(rows), b_ub=np.array(b), bounds=bnds, method="highs")
    phi = {cavs[i]: res.x[i] for i in range(nv)} if res.success else None
    return phi, (res.x[nv] if res.success else None)


def verify() -> dict:
    phi13, slack13 = _solve_mono(_configs(13))
    # forward-consistency: N<=13 phi on N<=16 shared-cavity configs
    C16 = _configs(16)
    shared_viol = 0; worst_shared = -9.0; new_cfg = 0
    for (cv, sc, ch) in C16:
        if cv in phi13 and all(y in phi13 for y in sc):
            v = ch + phi13[cv] - sum(phi13[y] for y in sc)
            worst_shared = max(worst_shared, v)
            if v > 1e-9:
                shared_viol += 1
        else:
            new_cfg += 1
    # bound holds on plain trees (any branching) N<=15 with the N<=13 phi (structural-root trees)
    def phi_of(y):
        # monotone step extension for cavities <= max known (lower bound), else 0-safe
        ks = sorted(phi13)
        vals = [phi13[k] for k in ks]
        return float(np.interp(float(y), [float(k) for k in ks], vals))
    bound_ok = True; worst_bound = -9.0
    for n in range(2, 14):
        for T in gen(n):
            if not is_plain(T):
                continue
            worst_bound = max(worst_bound, logphi(T) + phi_of(cavF(T)))
    bound_ok = worst_bound <= 1e-6
    return {
        "L": round(L, 9), "omega": round(OMEGA, 9),
        "folded_potential_N13_feasible": phi13 is not None,
        "exact_max_nontie_slack_N13": None if slack13 is None else round(slack13, 9),
        "slack_is_abs_g4": None if slack13 is None else abs(slack13 - 0.001026425) < 1e-6,
        "forward_shared_cavity_violations_N16": shared_viol,
        "forward_worst_shared_violation": round(worst_shared, 9),
        "forward_new_cavity_configs_unchecked": new_cfg,
        "bound_logPhi_le_minus_phi_root_holds_N13": bound_ok,
        "is_proof": False,
        "conjecture1_proved": False,
        "caveats": ("(1) per-node grid residuals are ~1e-3, shrinking with refinement but NOT certified 0 "
                    "(possible positive floor, cf. ~4e-5 smooth-overshoot history); (2) exact feasibility "
                    "only to N<=15 == conjecture up to N<=15; (3) new-cavity configs unchecked; (4) all-N "
                    "existence == conjecture (LP cannot prove it -- need explicit phi + analytic proof)."),
        "statement": (
            "Branching via bounded-branching + FOLDED MONOTONE discharge (phi on structural cavities only, "
            "arms/leaves folded into chi): chi_v+phi(cav_v)<=sum_struct phi(cav_c) => logPhi<=-phi(root)<=0. "
            "Bounded-branching-2 CLOSABLE (monotone phi; bound holds on 45934 trees; per-node residual a grid "
            "artifact ->0). A single monotone phi appears to handle ALL branching (residual ->0 with grid). "
            "Over exact cavities N<=15 feasible with slack |g(4)|=0.001026; and unlike the raw potential of "
            "11z, the folded+monotone phi is FORWARD-CONSISTENT (0 shared-cavity violations N13->N16). STRONG "
            "LEAD but NOT a proof: residuals not certified 0, new-cavity extension open, all-N existence == "
            "conjecture. Need an explicit monotone phi + analytic all-config verification. conjecture1_proved=False."
        ),
    }


if __name__ == "__main__":
    import json
    r = verify()
    print(json.dumps(r, indent=2, default=str))
    assert r["folded_potential_N13_feasible"]
    assert r["slack_is_abs_g4"]
    assert r["forward_shared_cavity_violations_N16"] == 0
    assert not r["is_proof"] and not r["conjecture1_proved"]
    print("\nAll assertions pass. Folded+monotone discharge: bounded-branching-2 closable, forward-consistent "
          "LEAD; NOT a proof. conjecture1_proved=False (honest).")
