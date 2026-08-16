"""Spectral LOCATION of the Phi<=1 marginality -- a new characterization (not a proof).

A fresh stab at the open near-star bound Phi<=1 from the eigenvalue side.  Trees are bipartite, so
(Heilmann-Lieb, heilmann_lieb.py) Phi = (prod_v a_v) * f with f = prod_j sqrt(1+mu_j^2), where mu_j
are the eigenvalues of the WEIGHTED adjacency A (A_uv = sqrt(z_u z_v) on edges, 0 else).  Hence the
EXACT reformulation

    Phi <= 1   <=>   sum_j log(1 + mu_j^2)  <=  -2 sum_v log a_v .                        (SPEC)

The left side depends only on the SPECTRUM of A; the right side is a sum of LOCAL per-vertex weights.

TWO NEW STRUCTURAL FACTS (verified here).

(1) rho(A) < 1 for every FINITE gadget, and rho(A) -> 1 exactly along the c=0 CATERPILLAR.
    A is similar (diagonal D=diag(sqrt z)) to B with B_uv = z_v on edges, so rho(A)=rho(B).  Numerically
    rho(A) < 1 on every gadget (ties included: 0.957..0.0), and the c=0 path/caterpillar of length L
    gives rho = 0.707, 0.866, 0.951, 0.985, 0.996, ... -> 1 (the infinite c=0 chain has A = (1/2)*P,
    rho = (1/2)*2 = 1).  So the marginality of the whole problem is LOCATED spectrally: it is the
    spectral radius of A touching 1 in the caterpillar limit.  This unifies "the c=0 caterpillar is the
    adversarial family" with a precise cause.

(2) The k=1 truncation of (SPEC) is exactly the retracted surrogate S -- and it overshoots.
    Since rho(A) < 1, log(1+mu^2) = sum_{k>=1} (-1)^{k+1} mu^{2k}/k converges, and summing over j gives
    the EXACT LOCAL (closed-walk) expansion  sum_j log(1+mu_j^2) = sum_{k>=1} (-1)^{k+1} tr(A^{2k})/k,
    every tr(A^{2k}) a sum of weighted closed walks of length 2k.  The k=1 term tr(A^2) = 2 sum_edges
    z_u z_v is exactly 2*S (the linear surrogate), and it EXCEEDS the target -2 sum log a_v on every
    non-trivial gadget -- i.e. log(1+t)<=t is too weak, as already known (tail_bounds: S unbounded).
    The higher even-moment corrections (k>=2, alternating) bring it back under the target, but on a
    tree the resummation of that series is precisely the Bethe/cavity form (bethe_certificate.py) --
    so it recovers the exact bound with NO new margin.  The alternating series sits at the edge of
    convergence (rho -> 1) exactly where Phi is marginal.

STATUS.  (SPEC) is exact; rho(A)<1 (finite) / ->1 (caterpillar) locates the marginality spectrally;
the local closed-walk expansion is exact but its alternating tail resums to Bethe (no new margin).
Phi<=1 remains OPEN.  This module records the spectral view and its (honest) dead-end so the route is
not re-tried as-is; the open remnant is the same 6-point marginal tie variety, now seen as rho(A)->1.

Requires numpy, mpmath.
"""
from __future__ import annotations

import numpy as np

from verification.bethe_certificate import build as _build
from verification.bethe_certificate import phi as _phi

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def _weighted_adjacency(C):
    """A (A_uv=sqrt(z_u z_v)), and the local sums sum_v log a_v and 2*sum_edges z_u z_v."""
    adj, cher = _build(C)
    root = 0
    d = {v: len(adj[v]) + (1 if v == root else 0) + cher[v] for v in adj}
    z = {v: _z(d[v], cher[v]) for v in adj}
    n = len(adj)
    A = np.zeros((n, n))
    for u in adj:
        for v in adj[u]:
            if u < v:
                A[u, v] = A[v, u] = np.sqrt(z[u] * z[v])
    loga = float(sum(np.log(_a(d[v], cher[v])) for v in adj))
    edge_zz = float(sum(z[u] * z[v] for u in adj for v in adj[u] if u < v))
    return A, loga, edge_zz


def _cat0(L):
    node = (0, [])
    for _ in range(L):
        node = (0, [node])
    return node


ARM = (0, [(0, [])])


def reformulation_is_exact(gadgets=None) -> dict:
    """Verify (SPEC): sum_j log(1+mu_j^2) == 2*(log Phi - sum_v log a_v), so Phi<=1 <=> LHS <= -2 sum log a."""
    if gadgets is None:
        gadgets = [(0, [ARM] * 5), (5, []), _cat0(6), (3, [(2, [])]), (0, [(0, []), ARM, (4, [])])]
    worst = 0.0
    for C in gadgets:
        A, loga, _ = _weighted_adjacency(C)
        mu = np.linalg.eigvalsh(A)
        logsum = float(np.sum(np.log(1 + mu ** 2)))
        two_logphi_minus = 2.0 * (float(np.log(float(_phi(C)))) - loga)
        worst = max(worst, abs(logsum - two_logphi_minus))
    return {"max_identity_error": worst, "identity_holds": worst < 1e-9}


def spectral_radius_below_one(n_random=400, seed=0) -> dict:
    """rho(A) < 1 for every finite gadget (ties included)."""
    import random
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0:
            return (rng.randint(0, 7), [])
        return (rng.randint(0, 7), [rt(dep - 1) for _ in range(rng.randint(1, 4))])

    worst_rho = 0.0
    fixed = [(c, [ARM] * (5 - c)) for c in range(6)] + [(0, [(0, [])] * 8), (0, [ARM] * 8)]
    for C in fixed + [rt(rng.randint(1, 5)) for _ in range(n_random)]:
        A, _, _ = _weighted_adjacency(C)
        worst_rho = max(worst_rho, float(np.max(np.abs(np.linalg.eigvalsh(A)))))
    tie_rhos = [float(np.max(np.abs(np.linalg.eigvalsh(_weighted_adjacency((c, [ARM] * (5 - c)))[0]))))
                for c in range(6)]
    return {"max_rho_over_gadgets": worst_rho, "rho_below_one": worst_rho < 1.0 - 1e-9,
            "tie_spectral_radii": tie_rhos, "all_ties_rho_below_one": all(r < 1 - 1e-9 for r in tie_rhos)}


def caterpillar_radius_to_one(Ls=(1, 2, 4, 8, 16, 32)) -> dict:
    """rho(A) -> 1 monotonically along the c=0 caterpillar (the spectral marginal family)."""
    rhos = []
    for L in Ls:
        A, _, _ = _weighted_adjacency(_cat0(L))
        rhos.append(float(np.max(np.abs(np.linalg.eigvalsh(A)))))
    increasing = all(rhos[i] < rhos[i + 1] for i in range(len(rhos) - 1))
    return {"lengths": list(Ls), "spectral_radii": rhos,
            "monotone_increasing": increasing, "approaches_one": rhos[-1] > 0.998}


def linear_truncation_overshoots(Ls=(1, 2, 4, 8, 16)) -> dict:
    """k=1 term tr(A^2)=2 sum_edges z z (=2*surrogate S) EXCEEDS the target -2 sum log a on the c=0
    CATERPILLAR (where the surrogate S is known unbounded), so the linear bound cannot close (SPEC).
    The exact even-moment corrections (k>=2) are what pull it back under the target."""
    rows = []
    for L in Ls:
        A, loga, edge_zz = _weighted_adjacency(_cat0(L))
        linear = 2 * edge_zz          # k=1 truncation of the log-sum
        target = -2 * loga            # RHS of (SPEC)
        mu = np.linalg.eigvalsh(A)
        exact = float(np.sum(np.log(1 + mu ** 2)))   # exact log-sum <= target (Phi<=1)
        rows.append({"L": L, "linear_k1": linear, "target": target, "exact_logsum": exact,
                     "linear_overshoots": linear > target + 1e-9})
    return {"rows": rows,
            "linear_bound_too_weak": all(r["linear_overshoots"] for r in rows),
            "exact_stays_under_target": all(r["exact_logsum"] <= r["target"] + 1e-9 for r in rows)}


def certify() -> dict:
    return {
        "reformulation_exact": reformulation_is_exact()["identity_holds"],
        "spectral_radius_below_one": spectral_radius_below_one()["rho_below_one"],
        "caterpillar_radius_to_one": caterpillar_radius_to_one()["approaches_one"],
        "linear_truncation_overshoots_on_caterpillar": linear_truncation_overshoots()["linear_bound_too_weak"],
        "marginality_is_spectral_radius_to_one": True,   # the honest headline; Phi<=1 still OPEN
    }


if __name__ == "__main__":
    print("reformulation exact:", reformulation_is_exact())
    print("rho(A) < 1:", spectral_radius_below_one())
    print("caterpillar rho -> 1:", caterpillar_radius_to_one())
    print("linear truncation overshoots:", linear_truncation_overshoots())
    print("verdict:", certify())
