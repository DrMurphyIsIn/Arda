"""Transfer-matrix reduction of the chain-gadget bound, and why it is a marginal constrained JSR.

By branch-multiplicativity (multicenter.py) the near-star family reduces to a single branch, and
the supremum Phi = 1 is attained on a CHAIN (path gadget: the tie root(4)-0-0).  This module
carries out the global/transfer-matrix route toward a closed proof of Phi <= 1 for chains, and
reports precisely where it stands.

CHAIN = TRANSFER-MATRIX PRODUCT.  In the normalized state (X,Y) = (Phi0, Phi1) (root un/matched
parts), a chain link with parent cherries c and child (cherries c', leaf?) acts LINEARLY:
    (X,Y) <- M(c,c',leaf) (X,Y),    M = a * [[1, 1], [z_r z_c, 0]],
    a = F(2+c,c)/rho_B^{1+2c},  z_r = z(2+c,c),  z_c = z(1+c',c') or z(2+c',c').
The leaf seeds (X,Y) = ((rho(c)/rho_B)^{1+2c}, 0), and Phi = X + Y.  So a chain is
M_1 M_2 ... M_L applied to a leaf vector, and Phi <= 1 is a bound on this matrix product.

DIAGNOSIS (this is why it is hard).
* Every REPEATABLE link (uniform chain, child = same-cherry interior link) has spectral radius
  <= 0.98181 < 1 (max at c=0): uniform chains strictly decay.
* But SOME individual links have spectral radius > 1 (up to 1.1135): a single link can expand.
* Nonetheless every chain product satisfies X + Y <= 1 (verified over 10^6 chains; the tie
  attains 1).
So the chain family is a MARGINALLY STABLE, CONSTRAINED joint-spectral-radius problem: individual
links may expand, but the linkage constraint (a link's child-activity z_c must equal the activity
of its actual child link) forbids chaining the expanding ones, and the critical (JSR = 1)
trajectory is exactly the tie.  A single quadratic Lyapunov certificate CANNOT exist for such a
family (confirmed: no P with M^T P M <= P on the positive cone, dominating (1,1), with leaves in
the unit ball -- 0 feasible over a fine (P) grid).  A closed proof therefore needs a
graph-constrained (path-complete) Lyapunov function or an exact invariant-region argument -- the
standard, and genuinely hard, tools for marginal constrained JSR.  This is the residual of
Conjecture main, now identified as a constrained-JSR = 1 certification problem.
"""
from __future__ import annotations

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def M(c: int, cc: int, child_leaf: bool) -> np.ndarray:
    a = _F(2 + c, c) / _rhoB ** (1 + 2 * c)
    zr = _z(2 + c, c)
    dc = (1 + cc) if child_leaf else (2 + cc)
    return a * np.array([[1.0, 1.0], [zr * _z(dc, cc), 0.0]])


def spectral_radius_repeatable(cmax: int = 60) -> float:
    """Max spectral radius of a repeatable (uniform-chain) link M(c,c,interior)."""
    return max(float(max(abs(np.linalg.eigvals(M(c, c, False))))) for c in range(cmax + 1))


def spectral_radius_any(cmax: int = 20) -> float:
    """Max spectral radius over all single links (some exceed 1)."""
    return max(float(max(abs(np.linalg.eigvals(M(c, cc, cl)))))
               for c in range(cmax + 1) for cc in range(cmax + 1) for cl in (True, False))


def certify_diagnosis() -> dict:
    """The transfer-matrix diagnosis: repeatable links decay (<1); some links expand (>1);
    no single quadratic Lyapunov certificate exists on the cone."""
    import math

    rep = spectral_radius_repeatable()
    anyl = spectral_radius_any()
    # confirm no quadratic cone-Lyapunov P=[[1,p],[p,q]] (A' non-expansion + C' dominates (1,1))
    fam = [M(c, cc, cl) for c in range(12) for cc in range(12) for cl in (True, False)]
    leaves = [np.array([_F(1 + c, c) / _rhoB ** (1 + 2 * c), 0.0]) for c in range(12)]
    ones = np.array([[1.0, 1.0], [1.0, 1.0]])

    def copos(S):
        a, b, g = S[0, 0], S[0, 1], S[1, 1]
        if a < -1e-12 or g < -1e-12:
            return False
        return b >= 0 or b + math.sqrt(max(a * g, 0.0)) >= -1e-12

    feasible = False
    for p in np.linspace(-1.0, 3.0, 200):
        for q in np.linspace(0.0, 6.0, 200):
            P = np.array([[1.0, p], [p, q]])
            if (all(copos(P - Mi.T @ P @ Mi) for Mi in fam)
                    and all(v @ P @ v <= 1 + 1e-9 for v in leaves)
                    and copos(P - ones)):
                feasible = True
                break
        if feasible:
            break
    return {"repeatable_rho_le_1": rep < 1.0, "repeatable_rho": rep,
            "some_link_rho_gt_1": anyl > 1.0, "max_link_rho": anyl,
            "quadratic_lyapunov_exists": feasible,
            "marginal_constrained_JSR": (rep < 1.0 and anyl > 1.0 and not feasible)}


def path_complete_linear_lyapunov(C: int = 18, dominate: bool = True) -> int:
    """Attempt a path-complete linear Lyapunov certificate for Phi<=1 (the bounded-depth /
    contraction route).  Assign each child-class c a functional (p_c,q_c) and require the
    transition inequalities l_c M(c,z_{c'}) <= l_{c'} and the leaf-base bound; with dominate=True
    also require (p_c,q_c) >= (1,1) so that V_c(X,Y) >= Phi = X+Y on the FULL positive cone.
    Returns the scipy linprog status (0 feasible, 2 infeasible).

    FINDING: with dominate=True the LP is INFEASIBLE (for all C tried) -- no path-complete linear
    Lyapunov dominates Phi on the full cone.  With dominate=False (contraction + leaf only) it is
    FEASIBLE.  So the contraction structure exists, but cannot be combined with full-cone
    domination of Phi: the obstruction is exactly that a certificate must dominate Phi only on the
    REACHABLE cone (an exact invariant polytope tailored to the tie).  This is the generic
    signature of an exactly-marginal JSR (=1): finite Lyapunov certificates (quadratic, above, and
    linear, here) fail even though Phi<=1 holds.  Requires scipy.
    """
    import numpy as np
    from scipy.optimize import linprog

    n = C + 1
    A, b = [], []
    lb = 1.0 if dominate else 0.0
    for c in range(n):
        for cp in range(n):
            r = [0.0] * (2 * n)
            r[c] += _af(c); r[n + c] += _af(c) * _zr(c) * _zint(cp); r[cp] += -1
            A.append(r); b.append(0.0)
            r = [0.0] * (2 * n)
            r[c] += _af(c); r[n + cp] += -1
            A.append(r); b.append(0.0)
        for cl in range(n):
            r = [0.0] * (2 * n)
            r[c] = _af(c) * _aleaf(cl); r[n + c] = _af(c) * _aleaf(cl) * _zr(c) * _zleaf(cl)
            A.append(r); b.append(1.0)
    res = linprog([1.0] * (2 * n), A_ub=np.array(A), b_ub=np.array(b),
                  bounds=[(lb, None)] * (2 * n), method="highs")
    return res.status


def _af(c):
    return _F(2 + c, c) / (621 / 64) ** ((1 + 2 * c) / 11)


def _zr(c):
    return _z(2 + c, c)


def _zint(c):
    return _z(2 + c, c)


def _zleaf(c):
    return _z(1 + c, c)


def _aleaf(c):
    return _F(1 + c, c) / (621 / 64) ** ((1 + 2 * c) / 11)


def chain_depth_profile(C: int = 14, depth: int = 8) -> dict:
    """Per-class (path-complete) reachable-frontier iteration for the constrained chain family.

    Tracks the state (Phi, rho0, z_child) and iterates the single-child map
    Phi' = a(c_par) Phi (1 + z_r z_c rho0), rho0' = 1/(1 + z_r z_c rho0), keeping the top-Phi
    states per child-activity bucket.  Returns the max Phi at each depth.  Finding: the
    supremum Phi = 1 is attained at DEPTH 2 (the tie root(4)-0-0), and max Phi decreases
    strictly with depth beyond it -- the recursion contracts past the tie, so the sup is hit
    at a bounded-depth chain, not approached asymptotically.  (This is why 'bounded-depth check
    + eventual contraction' is the natural remaining route to a closed proof.)
    """
    _rB = (621 / 64) ** (1 / 11)

    def af(c):
        return _F(2 + c, c) / _rB ** (1 + 2 * c)

    def zint(c):
        return _z(2 + c, c)

    def zleaf(c):
        return _z(1 + c, c)

    S = [(af0, 1.0, zleaf(c)) for c in range(C + 1)
         for af0 in (_F(1 + c, c) / _rB ** (1 + 2 * c),)]
    profile = [max(p[0] for p in S)]
    for _ in range(depth):
        nxt = []
        for (Phi, rho0, zc) in S:
            for cp in range(C + 1):
                zr = zint(cp)
                br = 1 + zr * zc * rho0
                nxt.append((af(cp) * Phi * br, 1.0 / br, zint(cp)))
        from collections import defaultdict
        buck = defaultdict(list)
        for p in nxt:
            buck[round(p[2], 6)].append(p)
        S = []
        for ps in buck.values():
            ps.sort(key=lambda t: -t[0])
            S.extend(ps[:40])
        profile.append(max(p[0] for p in S))
    return {"max_phi_by_depth": [round(x, 8) for x in profile],
            "sup": round(max(profile), 8),
            "sup_at_depth": int(max(range(len(profile)), key=lambda i: profile[i])),
            "decays_after_sup": all(profile[i] >= profile[i + 1] - 1e-9
                                    for i in range(2, len(profile) - 1))}


if __name__ == "__main__":
    print("chain transfer-matrix diagnosis:", certify_diagnosis())
    print("chain depth profile:", chain_depth_profile())
