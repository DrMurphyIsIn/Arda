"""Extending the arithmetic proof to ARBITRARY children: the general inductive step, how far it goes,
and the exact remaining gap (which is the open Brualdi-Goldwasser crux).

near_star_arithmetic_proof.py rigorously proves Phi<=1 on the near-star family N(c,k) (children = bare
cherry-arms) via a 1-variable (s=c+k) ratio-unimodality argument.  This module addresses the general
case: a root with cr cherries and ARBITRARY children C_1..C_k.

THE EXACT TELESCOPING STEP.  With cavity fields m_i and log-amplitudes log Phi_i of the children,
    log Phi(node) = sum_i log Phi_i + e_root,    e_root = log a(d,cr) + log(1 + z(d,cr) * sum_i m_i),
    d = k+1+cr,  z(d,cr) = 3/(3d+cr).
So the whole conjecture is the inductive statement: if every child has log Phi_i <= 0, the node has
log Phi <= 0 (with equality confined to the tie locus).

WHY "log Phi_i <= 0" ALONE IS NOT ENOUGH (the naive induction overshoots).  e_root can be POSITIVE, and
must be paid for by the children's NEGATIVE log Phi_i.  If one only assumes log Phi_i <= 0 and puts the
children at the WORST hypothetical spot (log Phi_i = 0 with large cavity m_i), the node overshoots:
a cr=0 root with k hypothetical children at (m=1, log Phi=0) has e_root -> -log rho_B + log 2 = +0.486
as k->inf.  Such children are UNREACHABLE (a real m=1 leaf has log Phi = -log rho_B = -0.207); the
induction MUST use the quantitative, cavity-dependent bound  log Phi_i <= Psi(m_i) = -P*(m_i),  where
Psi(m) = sup{log Phi : root cavity = m} is the value function (cavity_potential.py).

THE GAP, PRECISELY.  Proving the step for arbitrary children is equivalent to producing a valid
potential P (per-vertex inequality q_v <= sum_children P(m_c) - P(m_v)) with P >= 0.  Three facts pin
the difficulty:
  * The tightest such P is P* = -Psi -- but P* >= 0 IS the conjecture (circular).
  * NO smooth / fixed-complexity P works: the continuous relaxation of the amplitude exceeds 1 between
    integer configurations (near_tie_asymptotics.py), so any smooth P is defeated at the marginal tie.
  * The proven families do NOT capture Psi: over reachable cavities, sup{log Phi over ALL gadgets}
    exceeds sup{log Phi over near-stars + tie-children + brooms} by up to +0.197 (at m=1/15), and the
    optimal child is non-monotone (a bare leaf can beat a cherry-arm at large parent activity), so there
    is no single dominating child-family to reduce to.
Hence the near-star ratio-unimodality argument (a GLOBAL proof for one family, bypassing P) does not
directly extend; the general case needs either a NON-smooth/arithmetic potential respecting the
integrality of (cherries, degree), or a family-by-family global argument covering the true (mixed,
non-monotone) maximizers.  This is exactly the open crux.

WHAT DOES extend (verified here).  (i) leaves: log Phi(c,[]) = log a(1+c,c) <= 0, = 0 iff c=5.
(ii) the near-star family N(c,k) (proven, near_star_arithmetic_proof).  (iii) the tie-children family
(cr,[TIE]*k) (TIE a c5-leaf, log Phi=0): log Phi <= 0 for all cr,k, equality only at the trivial tie --
same cancellation + ratio structure, verified over a large range.  Empirically the FULL step holds
(worst node log Phi over real children = -0.0015, <= 0, tie only at equality).  A full proof is OPEN.

Requires numpy.
"""
from __future__ import annotations

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)
_TIE = (5, [])          # c5-leaf tie: cavity 3/23, log Phi = 0
ARM = (0, [(0, [])])


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return (1.5 ** c * (1 + c / (3 * d))) / _rhoB ** (1 + 2 * c)


def node_log_phi(cr, children_states):
    """log Phi of a node with cr cherries and children given as (cavity m_i, log Phi_i)."""
    ms = [m for (m, _) in children_states]
    lps = [lp for (_, lp) in children_states]
    k = len(children_states)
    d = k + 1 + cr
    z = _z(d, cr)
    S = sum(ms)
    mv = z / (1 + z * S)
    e_root = float(np.log(_a(d, cr) * z) - np.log(mv))      # = log a + log(1 + z S)
    return sum(lps) + e_root, mv


def _mlp(C):
    cr, kids = C
    ch = [_mlp(k) for k in kids]
    lp, mv = node_log_phi(cr, ch)
    return (mv, lp)


def naive_induction_overshoots():
    """Assuming only log Phi_i <= 0 and placing children at the UNREACHABLE spot (m=1, log Phi=0), a
    cr=0 root overshoots: e_root -> +0.486 as k->inf. Justifies why a cavity-dependent bound is needed."""
    vals = []
    for k in (1, 2, 5, 20, 100, 1000):
        lp, _ = node_log_phi(0, [(1.0, 0.0)] * k)          # hypothetical m=1, log Phi=0 children
        vals.append((k, lp))
    limit = -np.log(_rhoB) + np.log(2)
    return {"node_log_phi_by_k": [(k, round(v, 5)) for k, v in vals],
            "limit_as_k_to_inf": float(limit), "overshoots": vals[-1][1] > 0}


def general_step_holds_on_real_children(n=200000, seed=0):
    """Empirically the true step holds: over nodes built from REAL gadget children (each log Phi_i<=0),
    the node log Phi is <= 0 (worst ~ -0.0015, at a near-tie config)."""
    import random
    from verification import curve_search as CS
    rng = random.Random(seed)
    pool = [_mlp(g) for D in range(1, 5) for g in CS._gadgets(D, mc=4, mcher=6)]
    worst, wc = -9.0, None
    for _ in range(n):
        cr = rng.randint(0, 7)
        k = rng.randint(1, 8)
        kids = [pool[rng.randrange(len(pool))] for _ in range(k)]
        lp, mv = node_log_phi(cr, kids)
        if lp > worst:
            worst, wc = lp, (cr, k, round(mv, 4))
    return {"worst_node_log_phi": worst, "step_holds": worst <= 1e-9, "worst_ctx": wc}


def tie_children_family_le_zero(cmax=6, kmax=10):
    """The tie-children family (cr, [TIE]*k) is <= 0 for all cr,k, equality only at the trivial tie
    (cr=5,k=0). A second family the arithmetic technique covers (same cancellation + ratio structure)."""
    worst, argmax = -9.0, None
    for cr in range(0, cmax + 1):
        for k in range(0, kmax + 1):
            _, lp = _mlp((cr, [_TIE] * k))
            if lp > worst:
                worst, argmax = lp, (cr, k)
    return {"max_log_phi": worst, "all_le_zero": worst <= 1e-12,
            "argmax": argmax, "tie_only_at_trivial": argmax == (5, 0)}


def certify():
    return {
        "naive_induction_overshoots": naive_induction_overshoots()["overshoots"],
        "tie_children_family_le_zero": tie_children_family_le_zero()["all_le_zero"],
        "general_step_holds_empirically": general_step_holds_on_real_children(n=50000)["step_holds"],
        "full_extension_proven": False,     # arbitrary children = open Brualdi-Goldwasser crux
        "gap": "need a non-smooth/arithmetic valid potential (smooth fails; tightest P*=-Psi is circular)",
    }


if __name__ == "__main__":
    print("naive induction overshoots:", naive_induction_overshoots())
    print("tie-children family <= 0:", tie_children_family_le_zero())
    print("general step on real children:", general_step_holds_on_real_children())
    print("verdict:", certify())
