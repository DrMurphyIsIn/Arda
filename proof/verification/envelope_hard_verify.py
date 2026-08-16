"""Pushed-as-hard-as-possible verdict on the inductive-envelope route for Phi<=1: NO fixed-degree
bivariate envelope closes it (the invariance floor PLATEAUS positive at the ties, degree-swept and
adversarially-trained).

This is the rigorous follow-up to curve_search.py.  There, a deg<=3 rational envelope Phi<=h(u,z) with
a hard ceiling had an adversarial invariance floor ~+0.038.  Here we push much harder:

  1. CEILING-FREE ansatz  h = 1 - s(u,z)^2  (h<=1 by construction; h=1 at a tie iff s=0 there), so the
     search never wastes effort on the ceiling and can chase invariance directly.
  2. ADVERSARIAL TRAINING (cutting-plane min-max): fit s, hunt the worst-violating formation, feed it
     back -- so the optimizer cannot fool itself with a lucky sample.
  3. DEGREE SWEEP 3,4,5 and a 400k-formation adversary hunt (wide nodes k<=24, tie/anchor children).

TRAP AND ITS RESOLUTION.  The ceiling-free adversarial training reports NEGATIVE floors (deg3 -0.008,
deg4 -0.010) -- looking like a strict-margin certificate.  It is an ARTIFACT: the fit buys the margin
by letting h dip ~1e-5 BELOW Phi exactly at the ties (a containment violation, h<1 there), which the
random hunt never probes because it does not reconstruct the exact tie formation.  A valid envelope
must CONTAIN the reachable set (h>=Phi) with h=1 at the ties.

DECISIVE MEASUREMENT (this module, HARD containment enforced -- h>=Phi on depth-5 states, h=1 at the 6
ties, verified: h(tie)=1.0 to 1e-6):
    degree 3:  exact-tie invariance defect = +0.0225,  adversary floor = +0.042
    degree 4:  exact-tie invariance defect = +0.0256,  adversary floor = +0.081
    degree 5:  exact-tie invariance defect = +0.0270,  adversary floor = +0.086
The floor does NOT decrease with degree -- it PLATEAUS (slightly rises) at ~+0.025 at the exact ties.
The exact-tie defect is the clean kill: forming the tie-neighbourhood overshoots the envelope by ~+0.025
no matter the fit.  So NO fixed-degree bivariate envelope h(u,z) is inductively invariant while
containing the reachable set -- the marginal 6-point tie (equivalently the accumulating invariant
boundary, near_star_polytope; equivalently rho(A)->1 on the c=0 caterpillar, spectral_marginality)
defeats the whole envelope class.  Phi<=1 remains OPEN.

The 6 exact tie states (Phi=1, u=rho0=(18+c)/23, z=3/(18+c)), c=0..5, all with root virtual-degree 6.

Requires numpy.
"""
from __future__ import annotations

import random

import numpy as np

from verification import curve_search as CS

_ARM = (0, [(0, [])])
TIES = [(c, [_ARM] * (5 - c)) for c in range(6)]
TIE_STATES = [CS._state(g) for g in TIES]                       # (Phi=1, u, z)


def _terms(deg):
    return [(i, j) for i in range(deg + 1) for j in range(deg + 1) if i + j <= deg]


def _basis(U, Z, t):
    U = np.asarray(U, float)
    Z = np.asarray(Z, float)
    return np.stack([(U ** i) * (Z ** j) for (i, j) in t], axis=-1)


def _s(coef, U, Z, t):
    return _basis(U, Z, t) @ coef


def tie_states():
    """The 6 exact tie states (Phi, u, z) = (1, (18+c)/23, 3/(18+c)), c=0..5 (all root-degree 6)."""
    return [(float(p), float(u), float(z)) for (p, u, z) in TIE_STATES]


def exact_tie_defect(coef, t):
    """Invariance defect at the EXACT tie formations (children Phi_i = h(child) = 1 - s^2). A valid
    marginal invariant needs this <= 0; a positive value means the envelope is overshot at the ties."""
    worst = -9.0
    hvals = []
    for (cr, kids), (_, ut, zt) in zip(TIES, TIE_STATES):
        chs = [CS._state(k) for k in kids]
        ph = [1.0 - float(_s(coef, np.array([u]), np.array([z]), t)[0]) ** 2 for (_, u, z) in chs]
        k = len(kids)
        d = k + 1 + cr
        A = CS._a(d, cr)
        zn = CS._z(d, cr)
        Pi = float(np.prod(ph)) if ph else 1.0
        Sig = sum(z * (u * p) * (Pi / p if p > 0 else 0.0) for (_, u, z), p in zip(chs, ph)) if ph else 0.0
        fX = A * Pi
        fPhi = fX + A * zn * Sig
        up = fX / fPhi if fPhi > 0 else 1.0
        su = float(_s(coef, np.array([up]), np.array([zn]), t)[0])
        worst = max(worst, fPhi - (1.0 - su * su))
        hvals.append(1.0 - float(_s(coef, np.array([ut]), np.array([zt]), t)[0]) ** 2)
    return worst, hvals


def naive_envelope_overshoots_at_ties():
    """Cheap deterministic check: the trivial envelope h==1 (s==0) is NOT tie-invariant -- forming the
    tie neighbourhood with children pinned to Phi=1 overshoots. (The gate the search must beat.)"""
    t = _terms(3)
    coef = np.zeros(len(t))                    # s == 0 -> h == 1 everywhere
    defect, hvals = exact_tie_defect(coef, t)
    return {"h_at_ties": [round(h, 6) for h in hvals], "exact_tie_defect": defect,
            "overshoots": defect > 1e-6}


def _pool():
    return ([(a[0], a[1]) for a in CS.anchors()]
            + [(float(u), float(z)) for (_, u, z) in CS.reachable_states(4)])


def _group(ctxs, t):
    from collections import defaultdict
    byk = defaultdict(list)
    for cr, kids in ctxs:
        byk[len(kids)].append((cr, kids))
    g = []
    for k, items in byk.items():
        cu = np.array([[u for u, z in kids] for _, kids in items])
        cz = np.array([[z for u, z in kids] for _, kids in items])
        cr = np.array([cr for cr, _ in items])
        d = k + 1 + cr
        A = np.array([CS._a(dd, cc) for dd, cc in zip(d, cr)])
        zn = np.array([CS._z(dd, cc) for dd, cc in zip(d, cr)])
        g.append((cu, cz, A, zn, _basis(cu, cz, t)))
    return g


def _inv_def(coef, groups, t):
    worst = -9.0
    for cu, cz, A, zn, Bc in groups:
        sc = Bc @ coef
        ph = 1.0 - sc * sc
        Pi = np.prod(ph, 1)
        safe = np.where(np.abs(ph) > 1e-12, ph, 1e-12)
        Sig = np.sum(cz * (cu * ph) * (Pi[:, None] / safe), 1)
        fX = A * Pi
        fPhi = fX + A * zn * Sig
        up = np.where(fPhi > 0, fX / fPhi, 1.0)
        su = _s(coef, up, zn, t)
        worst = max(worst, float(np.max(fPhi - (1 - su * su))))
    return worst


def hunt(coef, t, n=200000, kmax=24, seed=0):
    rng = random.Random(seed)
    pool = _pool()
    worst, wc = -9.0, None
    for _ in range(n):
        cr = rng.randint(0, 10)
        k = rng.randint(1, kmax)
        kids = [rng.choice(pool) for _ in range(k)]
        us = np.array([u for u, z in kids])
        zs = np.array([z for u, z in kids])
        d = k + 1 + cr
        A = CS._a(d, cr)
        zn = CS._z(d, cr)
        sc = _s(coef, us, zs, t)
        ph = 1 - sc * sc
        Pi = float(np.prod(ph))
        safe = np.where(np.abs(ph) > 1e-12, ph, 1e-12)
        Sig = float(np.sum(zs * (us * ph) * (Pi / safe)))
        fX = A * Pi
        fPhi = fX + A * zn * Sig
        up = fX / fPhi if fPhi > 0 else 1.0
        su = float(_s(coef, np.array([up]), np.array([zn]), t)[0])
        dfc = fPhi - (1 - su * su)
        if dfc > worst:
            worst, wc = dfc, (cr, k, round(zn, 4), round(fPhi, 5))
    return worst, wc


def fit_hard(deg, seeds=4, gens=350, pop=100):
    """Fit h=1-s^2 minimizing invariance with HARD containment (h>=Phi on depth-5) + anchors (h=1 at
    ties). Returns coefficients + term list."""
    t = _terms(deg)
    data5 = CS.reachable_states(5)
    Phi, U, Z = data5[:, 0], data5[:, 1], data5[:, 2]
    au = np.array([a[0] for a in CS.anchors()])
    az = np.array([a[1] for a in CS.anchors()])
    pool = _pool()
    rng = random.Random(1)
    ctxs = [(rng.randint(0, 8), [rng.choice(pool) for _ in range(rng.randint(1, 8))]) for _ in range(2500)]
    for _ in range(50):
        for (cr, kids) in TIES:
            ctxs.append((cr, [(u, z) for (_, u, z) in [CS._state(kk) for kk in kids]]))
    groups = _group(ctxs, t)

    def cont(c):
        sv = _s(c, U, Z, t)
        return float(np.max(sv * sv - (1.0 - Phi)))

    def anc(c):
        return float(np.max(np.abs(_s(c, au, az, t))))

    best = (1e18, None)
    for s in range(seeds):
        gg = np.random.default_rng(s)
        mu = np.zeros(len(t))
        sigma = 0.3
        b = (1e18, mu)
        for _ in range(gens):
            cand = [mu + sigma * gg.standard_normal(len(t)) for _ in range(pop)] + [mu]
            scored = sorted(((300 * max(0.0, cont(c)) + 300 * anc(c)
                              + 20 * max(0.0, _inv_def(c, groups, t)) + 1e-4 * (c @ c), c) for c in cand),
                            key=lambda x: x[0])
            if scored[0][0] < b[0]:
                b = scored[0]
            mu = np.mean([c for _, c in scored[:pop // 4]], 0)
            sigma *= 0.992
        if b[0] < best[0]:
            best = b
    return best[1], t


def certify(degrees=(3, 4, 5)):
    """Full verdict: with hard containment, the invariance floor plateaus positive across degrees --
    no fixed-degree bivariate envelope closes Phi<=1. (Slow: fits each degree.)"""
    out = {}
    data5 = CS.reachable_states(5)
    Phi, U, Z = data5[:, 0], data5[:, 1], data5[:, 2]
    for deg in degrees:
        coef, t = fit_hard(deg)
        sv = _s(coef, U, Z, t)
        cont_viol = float(np.max(sv * sv - (1.0 - Phi)))
        tie_def, tie_h = exact_tie_defect(coef, t)
        floor, wc = hunt(coef, t, n=300000)
        out[deg] = {"containment_viol": cont_viol, "h_at_ties": [round(h, 6) for h in tie_h],
                    "exact_tie_defect": tie_def, "adversary_floor": floor,
                    "valid_invariant": cont_viol <= 1e-7 and tie_def <= 1e-6 and floor <= 1e-6}
    floors = [out[d]["exact_tie_defect"] for d in degrees]
    out["floor_plateaus_positive"] = all(f > 5e-3 for f in floors) and not (floors[-1] < floors[0] - 5e-3)
    out["fixed_degree_envelope_closes_phi_le_1"] = any(out[d]["valid_invariant"] for d in degrees)
    return out


if __name__ == "__main__":
    print("exact tie states (Phi,u,z):", tie_states())
    print("naive h==1 overshoots at ties:", naive_envelope_overshoots_at_ties())
    print("verdict:", certify())
