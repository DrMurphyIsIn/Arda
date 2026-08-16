"""Direct attack on the value function Psi(m) = sup{ log Phi(B) : B a branch with root cavity m }.

The conjecture Phi<=1 for all branches is exactly  Psi(m) <= 0 for all m in (0,1]  (the near-star theorem
handles the on-curve equality; the gap is Psi(m) <= omega < 0 for non-near-star cavities).  This module
attacks Psi directly through its EXACT Bellman fixed-point equation, and records precisely why the direct
attack stalls -- the same integrality obstruction, now in dynamical (operator) form.

THE BELLMAN EQUATION (exact).  From the amplitude identity (verified, bellman_local_identity_exact): a
branch B with root (c cherries, n non-cherry children of cavities m_1..m_n) and root cavity m satisfies
    log Phi(B) = log(3/m) - L - log(3(n+1+c)) + c*omega + sum_i log Phi(child_i),
where L=log rho_B, omega=log(3/2)-2L, and the cavity constraint m=3/t, t=3(n+1+c)+c+3*sum m_i gives
    sum_i m_i = 1/m - 1 - n - 4c/3    (=: S,  with 0 <= S <= n since each m_i in (0,1]).
Taking the sup over all admissible (c, n, {m_i}) yields the fixed point
    Psi(m) = log(3/m) - L + sup_{c>=0, n>=0, {m_i}: sum m_i = S} [ c*omega - log(3(n+1+c)) + sum_i Psi(m_i) ].
The inner sup over child cavities (fixed n, fixed sum S) equals  n * Psi_hat(S/n), where Psi_hat is the
CONCAVE HULL of Psi (mix two hull points to hit the mean S/n) -- so the operator is fully computable.

WHAT THE DIRECT ATTACK FINDS.
  (1) EMPIRICAL Psi (empirical_value_function): the max of log Phi over a deep+wide family (enumeration to
      depth 6 PLUS the arm-heavy configs (c,[ARM]*k + near-star children) that a bounded-DEPTH scan misses --
      the unbounded axis behind the (A') refutation) peaks at exactly 0 at the tie m=3/23 and equals -L at
      the leaf m=1.  So Psi<=0 with the tie as the tight binding maximum -- numerical support for the
      conjecture through the value function itself.
  (2) THE CONTINUOUS BELLMAN OPERATOR IS EXPANSIVE at Psi (continuous_bellman_expansive).  Initialised at
      the empirical (true-ish) Psi, ONE exact Bellman step RAISES it by up to ~+0.109 (T[Psi]-Psi), and
      iterating from any start DIVERGES (Psi -> +inf).  The mechanism: the concave-hull / continuum pricing
      of children (any cavity in (0,1]) over-estimates the DISCRETE reachable branches, and the child
      multiplicity n (up to ~1/m) compounds the over-estimate; the +0.109 step is the same over-relaxation
      as the box overshoot in gap_reduction_frontier.  The true DISCRETE Psi<=0 is a fixed point of the
      discrete operator but NOT of the continuum relaxation.
  (3) CONSEQUENCE.  Psi is not reachable by continuous value iteration, and no continuous/smooth certificate
      can bound it (it would have to bound the divergent continuum relaxation) -- the integrality obstruction
      in exact Bellman form.  A direct attack MUST respect reachability (which child cavities exist), i.e.
      the discreteness is load-bearing.  This is the open Brualdi-Goldwasser core, restated as: bound the
      DISCRETE-reachable sup-fixed-point of the above operator, whose continuum relaxation is unbounded.

Requires numpy.
"""
from __future__ import annotations

import numpy as np

from verification import gap_reduction_frontier as GF
from verification import curve_search as CS

_amp = GF._amp
ARM = GF.ARM
OMEGA = GF.OMEGA
L = float(np.log((621 / 64) ** (1 / 11)))


def bellman_local_identity_exact(max_depth=5):
    """The per-node Bellman identity log Phi(B) = log(3/m) - L - log(3(n+1+c)) + c*omega + sum child, exact
    on real trees (this is what makes the Psi fixed point exact)."""
    worst = 0.0
    for D in range(1, max_depth + 1):
        for B in CS._gadgets(D, mc=4, mcher=5):
            c, kids = B
            n = len(kids)
            m, ell = _amp(B)
            child = sum(_amp(k)[1] for k in kids)
            pred = np.log(3 / m) - L - np.log(3 * (n + 1 + c)) + c * OMEGA + child
            worst = max(worst, abs(ell - pred))
    return {"max_error": worst, "identity_exact": worst < 1e-9}


def _grid(npts=197):
    return np.linspace(0.02, 1.0, npts)


def empirical_value_function(npts=197):
    """Psi(m) = max log Phi over a deep+wide family: enumeration to depth 6, PLUS arm-heavy configs
    (c cherries, k arms, near-star deep children) that a bounded-depth scan misses.  Peaks at 0 at the tie
    m=3/23 and equals -L at the leaf m=1; Psi<=0 (conjecture, tight at the tie)."""
    grid = _grid(npts)
    pts = []
    for D in range(1, 7):
        for gg in CS._gadgets(D, mc=6, mcher=6):
            pts.append(_amp(gg))
    for c in range(0, 30):
        for k in range(0, 40):
            for js in ([], [5], [4], [5, 5], [4, 4], [5, 5, 5]):
                kids = [ARM] * k + [(0, [ARM] * s) for s in js]
                pts.append(_amp((c, kids)))
    pts = np.array(pts)
    Psi = np.full_like(grid, -1e9)
    idx = np.clip(np.round((pts[:, 0] - 0.02) / 0.98 * (npts - 1)).astype(int), 0, npts - 1)
    for i, e in zip(idx, pts[:, 1]):
        if e > Psi[i]:
            Psi[i] = e
    filled = Psi > -1e8
    Psi = np.interp(grid, grid[filled], Psi[filled])
    return {"grid": grid, "Psi": Psi, "max_Psi": float(Psi.max()),
            "argmax_m": float(grid[int(Psi.argmax())]),
            "tie_is_max": abs(grid[int(Psi.argmax())] - 3 / 23) < 0.02 and abs(Psi.max()) < 1e-3,
            "leaf_value": float(np.interp(1.0, grid, Psi)), "Psi_le_0": Psi.max() <= 1e-6}


def _concave_hull(x, y):
    pts = sorted(zip(x, y))
    h = []
    for px, py in pts:
        while len(h) >= 2:
            (x1, y1), (x2, y2) = h[-2], h[-1]
            if (y2 - y1) * (px - x1) <= (py - y1) * (x2 - x1) + 1e-15:
                h.pop()
            else:
                break
        h.append((px, py))
    hx = np.array([p[0] for p in h])
    hy = np.array([p[1] for p in h])
    return lambda q: np.interp(q, hx, hy)


def _bellman_step(grid, Psi):
    hull = _concave_hull(grid, Psi)
    out = np.full_like(Psi, -1e9)
    for i, m in enumerate(grid):
        inv = 1.0 / m
        best = -1e9
        for c in range(0, int(0.75 * (inv - 1)) + 2):
            base = inv - 1 - 4 * c / 3
            if base < 0:
                break
            for n in range(0, int(np.ceil(base)) + 3):
                S = base - n
                if S < -1e-9:
                    break
                if n == 0:
                    if abs(S) < 1e-6:
                        v = c * OMEGA - np.log(3 * (1 + c))
                    else:
                        continue
                else:
                    r = S / n
                    if r <= 1e-9 or r > 1 + 1e-9:
                        continue
                    v = c * OMEGA - np.log(3 * (n + 1 + c)) + n * float(hull(min(r, 1.0)))
                best = max(best, v)
        out[i] = np.log(3 / m) - L + best
    return out


def continuous_bellman_expansive(npts=197, iters=5):
    """The continuous Bellman operator (concave-hull/continuum child pricing) is EXPANSIVE at Psi and
    DIVERGES.  From the empirical (true-ish) Psi, one step raises it by up to ~+0.109 (T[Psi]-Psi); iterating
    from Psi=0 blows up.  This is the integrality obstruction: the continuum over-prices the discrete
    reachable children (same over-relaxation as the box overshoot), and the child multiplicity compounds it."""
    ev = empirical_value_function(npts)
    grid, Psi = ev["grid"], ev["Psi"]
    T = _bellman_step(grid, Psi)
    one_step_poke = float((T - Psi).max())
    # iterate from zero -> diverges
    Z = np.zeros_like(grid)
    maxes = []
    for _ in range(iters):
        Z = _bellman_step(grid, Z)
        maxes.append(float(Z.max()))
    diverges = maxes[-1] > maxes[0] * 5 and maxes[-1] > 1.0
    return {"one_step_poke_at_empirical_Psi": one_step_poke,
            "operator_expansive": one_step_poke > 1e-3,
            "iterate_from_zero_maxes": [round(x, 4) for x in maxes],
            "continuous_relaxation_diverges": diverges,
            "integrality_obstruction": one_step_poke > 1e-3 and diverges}


def certify():
    ident = bellman_local_identity_exact()
    ev = empirical_value_function()
    exp = continuous_bellman_expansive()
    return {
        "bellman_local_identity_exact": ident["identity_exact"],
        "empirical_Psi_max": ev["max_Psi"],
        "empirical_Psi_tie_is_binding_max": ev["tie_is_max"],       # Psi peaks at 0 at the tie 3/23
        "empirical_Psi_le_0": ev["Psi_le_0"],                       # conjecture, via the value function
        "continuous_operator_expansive": exp["operator_expansive"],  # one step pokes ~+0.109
        "continuous_relaxation_diverges": exp["continuous_relaxation_diverges"],
        "obstruction": "the continuous relaxation of Psi's Bellman operator is expansive and diverges "
                       "(integrality); the discrete reachability of child cavities is load-bearing. Psi<=0 "
                       "is the open Brualdi-Goldwasser core.",
        "phi_le_1_closed": False,
    }


if __name__ == "__main__":
    print("bellman identity:", bellman_local_identity_exact())
    print("empirical Psi:", {k: v for k, v in empirical_value_function().items() if k not in ("grid", "Psi")})
    print("expansive:", continuous_bellman_expansive())
    print("verdict:", certify())
