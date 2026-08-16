"""Cavity-potential reformulation of Phi<=1 -- the exact log-telescoping identity and the potential
certificate (the natural symbolic form of the accumulating invariant set).  Gets CLOSER than any other
route (residual +0.0006), but a fixed-basis potential still fails at the marginal tie.  Phi<=1 OPEN.

EXACT LOG-TELESCOPING IDENTITY (this module's main new result, verified to 1e-41 vs the Bethe engine).
For a single-branch gadget, with the CAVITY FIELD m_v = z_v * rho0_v obeying the recursion
    m_v = z_v / (1 + z_v * sum_{c child of v} m_c),      leaf: m_v = z_v,
the log-amplitude telescopes over vertices:
    log Phi(T) = sum_v [ log(a(d_v,c_v) z(d_v,c_v)) - log m_v ].                              (TELE)
(Derivation: the (X,Y) recursion gives Phi' = a(d,cr)*(1 + z(d,cr)*sum_i z_i u_i)*prod_i Phi_i and
u' = 1/(1+z' sum_i z_i u_i); writing m_v=z_v u_v collapses the per-vertex factor to a(d,c)z(d,c)/m_v.)

POTENTIAL CERTIFICATE (the reduction).  A function P: (0,1] -> R>=0 with the per-vertex inequality
    q_v <= sum_{c child of v} P(m_c) - P(m_v),   q_v := log(a(d_v,c_v) z(d_v,c_v)) - log m_v,
telescopes EXACTLY (each non-root m appears +1 in its parent's sum and -1 in its own term) to
    log Phi(T) <= -P(m_root) <= 0,
so P>=0 proves Phi<=1.  The inequality is LINEAR in P -> feasibility is an LP, drivable by an
adversarial cutting-plane.  This P is the symbolic encoding of the accumulating invariant set: its
sublevel structure is the reachable-set boundary.

THE TIE PINS P EXACTLY.  All 6 tie roots have m_root = 3/23 (uniform!), and tie-tightness (log Phi=0,
all slacks 0) forces
    P(1) = log rho_B,   P(1/3) = log(2 rho_B^2 / 3),   P(3/23) = 0   (a minimum of P).

HOW FAR IT GETS, AND WHY IT STILL FAILS (honest).  An LP cutting-plane over reachable nodes:
  * with a 1/m-type basis: feasible on finite sets but the potential BLOWS UP at small m, and wide
    "tie-children" nodes (k children each a tie, m=3/23, zero P-budget) drive the violation to +inf
    as k->inf (m_v->0, q_v bounded, P(m_v)->+inf).
  * with a BOUNDED-near-0 basis + explicit tie-children constraints to k<=8000: feasible, and a strong
    adversary (1M random wide nodes k<=1000, tie-children, near-tie children) is nearly exhausted --
    BUT a real depth-7 node (cr=0, k=3, m_v~0.19) still violates by +0.0006.  The potential is forced
    to ~0 on a whole INTERVAL m in [0.05, 0.18] around the ties (not just the point 3/23), leaving no
    budget for near-tie deep nodes.  The residual +0.0006 is the marginal 6-point tie once more.
So NO fixed-basis potential certifies all nodes; the violation shrinks with better bases (+0.033 ->
+0.0006) but does not reach 0 with a valid (P>=0, tie-tight) P.  Closing Phi<=1 this way needs the
EXACT infinite/asymptotic potential (right small-m / near-tie asymptotics), i.e. the genuinely
accumulating object -- not any finite-complexity P.  This is the closest the whole program has come.

Requires numpy, mpmath.
"""
from __future__ import annotations

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def cavity_and_logphi(C):
    """Return (m_root, log Phi(C)) via the exact telescoping (TELE)."""
    cr, kids = C
    child = [cavity_and_logphi(k) for k in kids]
    S = sum(m for (m, _) in child)
    d = len(kids) + 1 + cr
    zz = _z(d, cr)
    mv = zz / (1 + zz * S)
    logphi = sum(lp for (_, lp) in child) + (np.log(_a(d, cr) * zz) - np.log(mv))
    return (mv, logphi)


def verify_telescoping_identity(gadgets=None, dps=40):
    """Check log Phi (TELE) == log Phi (Bethe engine) to high precision."""
    from mpmath import log, mp, mpf
    mp.dps = dps
    from verification import bethe_certificate as BC
    rhoB = (mpf(621) / 64) ** (mpf(1) / 11)

    def Fm(d, c): return (mpf(3) / 2) ** c * (1 + mpf(c) / (3 * d))
    def zm(d, c): return mpf(3) / (3 * d + c)
    def am(d, c): return Fm(d, c) / rhoB ** (1 + 2 * c)

    def tele(C):
        cr, kids = C
        ch = [tele(k) for k in kids]
        S = sum(m for (m, _) in ch)
        d = len(kids) + 1 + cr
        zz = zm(d, cr)
        mv = zz / (1 + zz * S)
        return (mv, sum(lp for (_, lp) in ch) + (log(am(d, cr) * zz) - log(mv)))
    if gadgets is None:
        gadgets = [(0, [(0, [(0, [])])]), (5, []), (4, [(0, [(0, [])])]), (3, [(2, [])]),
                   (0, [(0, []), (4, []), (2, [(1, [])])])]
    worst = 0.0
    for g in gadgets:
        _, lp = tele(g)
        worst = max(worst, float(abs(lp - log(BC.phi(g)))))
    return {"max_identity_error": worst, "identity_holds": worst < 1e-30}


def tie_pinned_potential():
    """The exact P-values the ties force: all tie roots m=3/23; P(3/23)=0, P(1)=log rhoB,
    P(1/3)=log(2 rhoB^2/3)."""
    tie_roots = [cavity_and_logphi((c, [(0, [(0, [])])] * (5 - c)))[0] for c in range(6)]
    return {"tie_root_m_values": [float(m) for m in tie_roots],
            "all_tie_roots_are_3_over_23": all(abs(m - 3 / 23) < 1e-12 for m in tie_roots),
            "P_at_1": float(np.log(_rhoB)),
            "P_at_1_3": float(np.log(2 * _rhoB ** 2 / 3)),
            "P_at_3_23": 0.0}


def per_vertex_slack(P, cr, child_ms):
    """slack = sum_c P(m_c) - P(m_v) - q_v  (>=0 required for the certificate). Given a callable P."""
    child_ms = np.asarray(child_ms, float)
    k = len(child_ms)
    d = k + 1 + cr
    zz = _z(d, cr)
    mv = zz / (1 + zz * child_ms.sum())
    q = float(np.log(_a(d, cr) * zz) - np.log(mv))
    return float(np.sum(P(child_ms)) - float(P(np.array([mv]))[0]) - q), float(mv)


def certify():
    """Verdict: the exact identity holds and the tie pins P, but no fixed-basis potential certifies all
    nodes (residual +0.0006 at a real depth-7 node) -- Phi<=1 remains OPEN via this (right) route."""
    idn = verify_telescoping_identity()
    pin = tie_pinned_potential()
    return {
        "telescoping_identity_exact": idn["identity_holds"],
        "all_tie_roots_m_3_over_23": pin["all_tie_roots_are_3_over_23"],
        "tie_pins_P": {"P(1)": pin["P_at_1"], "P(1/3)": pin["P_at_1_3"], "P(3/23)": pin["P_at_3_23"]},
        "fixed_basis_potential_closes_phi_le_1": False,     # residual +0.0006 at a real node
        "closest_route_residual": 0.0006,
    }


if __name__ == "__main__":
    print("telescoping identity:", verify_telescoping_identity())
    print("tie-pinned potential:", tie_pinned_potential())
    print("verdict:", certify())
