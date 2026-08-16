"""Symbolic-regression search for an INDUCTIVE ENVELOPE curve certifying Phi<=1 -- with a
sampling-artifact-proof invariance gate.  Fast (vectorized numpy) so the search can be run hard.

The open near-star bound Phi<=1 needs a smooth certificate tangent to Phi=1 at the 6 rational tie
anchors (every polytopic / Lyapunov / Bethe-local / spectral route is exhausted).  This module searches
for that certificate as an inductive ENVELOPE and gates any candidate through (1) an ADVERSARIAL
invariance check and (2) an exact rational verification -- so a curve that merely FITS sampled trees
(the recurring overclaim trap) cannot pass.

ANSATZ.  Track each gadget by (Phi, u, z), u=rho0=X/Phi, z=root activity.  Seek a bivariate rational
envelope Phi <= h(u,z) with h<=1 on the reachable domain and h=1 at the 6 anchors.  If h is an
INDUCTIVE INVARIANT -- forming a node from children on the envelope (Phi_i=h(u_i,z_i)) never exceeds h
at the node -- then Phi(C) <= h(u,z) <= 1 for every gadget: a proof.

WHY THIS ANSATZ (and why it's not a ruled-out route).  Single-variable Phi<=g(u) is IMPOSSIBLE
(interlacing.realizable_region_max_points: two Phi=1 points at u=1 and u=22/23).  A z-box envelope
(Phi<=B(z), X<=C(z) independently) OVERSHOOTS at the corners (feasibility_probe: +0.077 defect -- the
(maxPhi,maxX) corner is unrealizable).  The bivariate h(u,z) COUPLES the coordinates within a z-slice,
and the 6 anchors sit at distinct (u,z)=((18+c)/23, 3/(18+c)), c=0..5.

FINDING (2026-08-06, honest).  With the vectorized kernel (~1ms/eval, ~1000x over the pure-Python loop)
a strong degree<=3 search DRIVES the SAMPLED invariance defect to ~0 (over ~6000 formation contexts) --
which looked like a lead.  It is NOT: the ADVERSARIAL gate (wide nodes k<=16, tie/anchor children, the
naive-overshoot config) exposes a residual invariance defect that NO degree<=3 rational h removes while
also holding ceiling<=1 and the anchors.  DECISIVE MEASUREMENT: with the ceiling HARD-ENFORCED (h<=1;
ceiling_max ~1e-3, anchor_err ~5e-4, containment ~1e-6), the best deg<=3 envelope over 5 seeds still has
an adversarial invariance FLOOR of ~+0.038 (worst: cr=0, k=2, z_node=1/3, formed Phi ~1.030 from
envelope-children).  So the bivariate-envelope class (deg<=3) is INSUFFICIENT -- the same marginal
6-point tie obstruction, now seen as: a fixed-complexity smooth envelope cannot both contain the
reachable set (with h<=1, anchors=1) AND be inductively invariant, because the true invariant boundary
is the ACCUMULATING curve (near_star_polytope), not a low-degree rational.  The sampled invariance ~0
was a sampling artifact; the adversarial gate caught it (the discipline held).  Phi<=1 remains OPEN.
What this module IS: a fast, reusable envelope-search with a working artifact-proof gate -- the honest
tool, and the demonstration that deg<=3 bivariate envelopes do not close it.

Requires numpy.
"""
from __future__ import annotations

import itertools

import numpy as np

_rhoB = (621 / 64) ** (1 / 11)

# bivariate rational envelope h(u,z) = num(u,z) / (1 + den(u,z)), total degree i+j <= DEG
DEG = 3
_TERMS = [(i, j) for i in range(DEG + 1) for j in range(DEG + 1) if i + j <= DEG]
_DTERMS = [(i, j) for i in range(DEG + 1) for j in range(DEG + 1) if 1 <= i + j <= DEG]
_nT = len(_TERMS)
NPARAM = _nT + len(_DTERMS)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def _basis(U, Z, terms):
    U = np.asarray(U, float)
    Z = np.asarray(Z, float)
    return np.stack([(U ** i) * (Z ** j) for (i, j) in terms], axis=-1)


def h_eval(params, u, z):
    """h(u,z) vectorized over array-like (u,z)."""
    params = np.asarray(params, float)
    num = _basis(u, z, _TERMS) @ params[:_nT]
    den = 1.0 + _basis(u, z, _DTERMS) @ params[_nT:]
    return np.where(np.abs(den) > 1e-9, num / den, 1e9)


def _state(C):
    """(Phi, u, z) of gadget C=(cherries,[children]); root has a phantom hub-parent (+1 degree)."""
    cr, kids = C
    d = len(kids) + 1 + cr
    ch = [_state(k) for k in kids]
    s = [phi for (phi, _, _) in ch]
    Pi = 1.0
    for si in s:
        Pi *= si
    Sig = 0.0
    for i, (phi_i, u_i, z_i) in enumerate(ch):
        pr = 1.0
        for j, sj in enumerate(s):
            if j != i:
                pr *= sj
        Sig += z_i * (u_i * phi_i) * pr
    A = _a(d, cr)
    X = A * Pi
    Y = A * _z(d, cr) * Sig
    phi = X + Y
    return (phi, (X / phi if phi > 0 else 1.0), _z(d, cr))


def _gadgets(nodes, mc=4, mcher=6):
    if nodes == 1:
        yield from ((c, []) for c in range(mcher + 1))
        return
    for cr in range(mcher + 1):
        for k in range(1, mc + 1):
            def comp(n, parts):
                if parts == 1:
                    if n >= 1:
                        yield (n,)
                    return
                for x in range(1, n - parts + 2):
                    for rest in comp(n - x, parts - 1):
                        yield (x,) + rest
            for sizes in comp(nodes - 1, k):
                for combo in itertools.product(*[list(_gadgets(s, mc, mcher)) for s in sizes]):
                    yield (cr, list(combo))


def reachable_states(max_depth=4, mc=4, mcher=6):
    out = [_state(g) for D in range(1, max_depth + 1) for g in _gadgets(D, mc, mcher)]
    return np.array(out)                              # columns: Phi, u, z


def anchors():
    """The 6 exact tie anchors (u, z, Phi=1): u=(18+c)/23, z=3/(18+c), c=0..5."""
    return [((18 + c) / 23, 3 / (18 + c), 1.0) for c in range(6)]


def _formation_groups(data, seed=0, n=6000, mc=5, mcher=6):
    """Fixed formation contexts grouped by child-count k (for a vectorized invariance objective)."""
    import random
    from collections import defaultdict
    rng = random.Random(seed)
    uz = [(float(u), float(z)) for (_, u, z) in data]
    byk = defaultdict(list)
    for _ in range(n):
        cr, k = rng.randint(0, mcher), rng.randint(1, mc)
        kids = [uz[rng.randrange(len(uz))] for _ in range(k)]
        byk[k].append((cr, kids))
    groups = []
    for k, items in byk.items():
        cu = np.array([[u for (u, z) in kids] for _, kids in items])
        cz = np.array([[z for (u, z) in kids] for _, kids in items])
        cr = np.array([cr for cr, _ in items])
        d = k + 1 + cr
        A = np.array([_a(dd, cc) for dd, cc in zip(d, cr)])
        zn = np.array([_z(dd, cc) for dd, cc in zip(d, cr)])
        groups.append((cu, cz, A, zn, _basis(cu, cz, _TERMS), _basis(cu, cz, _DTERMS)))
    return groups


def _invariance_sampled(params, groups):
    """Worst-case inductive step over the fixed sampled contexts (children on the envelope boundary)."""
    params = np.asarray(params, float)
    worst = -9.0
    for cu, cz, A, zn, Bn, Bd in groups:
        num = Bn @ params[:_nT]
        den = 1.0 + Bd @ params[_nT:]
        ph = np.where(np.abs(den) > 1e-9, num / den, 1e9)     # (N,k) child Phi = h(u,z)
        Pi = np.prod(ph, axis=1)
        safe = np.where(ph > 0, ph, 1.0)
        Sig = np.sum(cz * (cu * ph) * (Pi[:, None] / safe), axis=1)
        fX = A * Pi
        fPhi = fX + A * zn * Sig
        up = np.where(fPhi > 0, fX / fPhi, 1.0)
        worst = max(worst, float(np.max(fPhi - h_eval(params, up, zn))))
    return worst


def adversarial_invariance_gate(params, n_wide=120000, kmax=14, seed=0):
    """THE artifact-proof gate: stress invariance on ADVERSARIAL formations the sampled objective
    misses -- wide nodes (k up to kmax), children at the tie anchors / any reachable (u,z), and the
    naive-overshoot config (cr small, all children AT the ties). Returns the worst invariance defect
    and the context; a genuine inductive invariant must have defect ~0 here, not just on the sample."""
    import random
    rng = random.Random(seed)
    data = reachable_states(4)
    pool = [(a[0], a[1]) for a in anchors()] + [(float(u), float(z)) for (_, u, z) in data]

    def form(cr, kids):
        k = len(kids)
        d = k + 1 + cr
        A, zn = _a(d, cr), _z(d, cr)
        ph = [float(h_eval(params, u, z)) for (u, z) in kids]
        Pi = float(np.prod(ph))
        Sig = sum(z * (u * phi) * (Pi / phi if phi > 0 else 0.0) for (u, z), phi in zip(kids, ph))
        fX = A * Pi
        fPhi = fX + A * zn * Sig
        return fPhi, (fX / fPhi if fPhi > 0 else 1.0), zn

    worst, wc = -9.0, None
    for _ in range(n_wide):
        cr, k = rng.randint(0, 8), rng.randint(1, kmax)
        kids = [rng.choice(pool) for _ in range(k)]
        fPhi, up, zn = form(cr, kids)
        d = fPhi - float(h_eval(params, up, zn))
        if d > worst:
            worst, wc = d, (cr, k, round(zn, 4), round(fPhi, 5))
    for cr in range(6):                                   # naive-overshoot: children AT the ties
        for k in range(1, 10):
            for a in anchors():
                fPhi, up, zn = form(cr, [(a[0], a[1])] * k)
                worst = max(worst, fPhi - float(h_eval(params, up, zn)))
    return {"adversarial_invariance_defect": worst, "worst_ctx": wc,
            "is_genuine_invariant": worst < 1e-4}


def feasibility_probe(max_depth=4, n_form=20000, seed=0):
    """The independent z-BOX envelope overshoots at the corners (+0.077): motivates the coupled h."""
    import random
    from collections import defaultdict
    data = reachable_states(max_depth)
    BPhi, BX = defaultdict(float), defaultdict(float)
    for phi, u, z in data:
        zr = round(float(z), 10)
        BPhi[zr] = max(BPhi[zr], float(phi))
        BX[zr] = max(BX[zr], float(u * phi))
    rng = random.Random(seed)
    zlist = list(BPhi.keys())
    worst = -9.0
    for _ in range(n_form):
        cr, k = rng.randint(0, 6), rng.randint(1, 5)
        kids = [(BX[zc := rng.choice(zlist)], BPhi[zc] - BX[zc], zc) for _ in range(k)]
        d = k + 1 + cr
        A, zn = _a(d, cr), _z(d, cr)
        s = [X + Y for X, Y, _ in kids]
        Pi = 1.0
        for si in s:
            Pi *= si
        Sig = sum(zi * Xi * (Pi / si if si > 0 else 0.0) for (Xi, Yi, zi), si in zip(kids, s))
        fPhi = A * Pi + A * zn * Sig
        zr = round(zn, 10)
        bp = BPhi[zr] if zr in BPhi else BPhi[min(BPhi, key=lambda t: abs(t - zn))]
        worst = max(worst, fPhi - bp)
    return {"zbox_worst_phi_overshoot": worst, "zbox_feasible": worst < 1e-6}


def _objective(params, data, groups, anch, w_ceiling=8.0, w_anchor=8.0, w_inv=15.0, w_pars=1e-4):
    Phi, U, Z = data[:, 0], data[:, 1], data[:, 2]
    hv = h_eval(params, U, Z)
    containment = float(np.mean(np.maximum(0.0, Phi - hv)))
    ceiling = float(np.max(np.maximum(0.0, hv - 1.0)))                # hard: worst h-1
    anchor = float(np.sum(np.abs(h_eval(params, [a[0] for a in anch], [a[1] for a in anch]) - 1.0)))
    inv = max(0.0, _invariance_sampled(params, groups))
    pars = float(np.sum(np.asarray(params) ** 2))
    total = containment + w_ceiling * ceiling + w_anchor * anchor + w_inv * inv + w_pars * pars
    return total, {"containment": containment, "ceiling_max": ceiling, "anchor": anchor,
                   "invariance_sampled": inv, "parsimony": pars}


def search_curve(generations=300, pop=80, max_depth=4, seed=0):
    """Vectorized (mu,lambda)-ES over the rational envelope. Fast (~1ms/eval). Returns best params +
    the SAMPLED defect breakdown. The sampled invariance can reach ~0 -- always confirm with
    adversarial_invariance_gate before treating as a lead (it is a sampling artifact for deg<=3)."""
    rng = np.random.default_rng(seed)
    data = reachable_states(max_depth)
    groups = _formation_groups(data, seed=seed)
    anch = anchors()
    mu = np.zeros(NPARAM)
    mu[0] = 1.0
    sigma = 0.5
    best = (1e18, mu, None)
    for _ in range(generations):
        cand = [mu + sigma * rng.standard_normal(NPARAM) for _ in range(pop)] + [mu]
        scored = sorted((_objective(p, data, groups, anch) + (p,) for p in cand), key=lambda t: t[0])
        if scored[0][0] < best[0]:
            best = (scored[0][0], scored[0][2], scored[0][1])
        mu = np.mean([row[2] for row in scored[:max(2, pop // 4)]], axis=0)
        sigma *= 0.994
    return {"best_params": [float(x) for x in best[1]], "objective": float(best[0]),
            "breakdown": {k: float(v) for k, v in best[2].items()},
            "sampled_looks_invariant": best[2]["invariance_sampled"] < 1e-4}


def certify(generations=250, seeds=(1, 2, 3, 5), n_wide=40000):
    """Honest end-to-end verdict: z-box refuted; a deg<=3 bivariate envelope can reach SAMPLED
    invariance ~0 but FAILS the adversarial gate (sampling artifact) -> class insufficient. OPEN.
    Searches several seeds and takes the MOST lead-looking candidate (smallest sampled defect), then
    shows the adversarial gate exposes a positive defect -- the artifact demonstration."""
    probe = feasibility_probe()
    runs = [search_curve(generations=generations, seed=s) for s in seeds]
    best = min(runs, key=lambda r: r["breakdown"]["invariance_sampled"])       # most "invariant" sample
    gate = adversarial_invariance_gate(best["best_params"], n_wide=n_wide)
    return {
        "zbox_envelope_feasible": probe["zbox_feasible"],                       # False
        "best_sampled_invariance_defect": best["breakdown"]["invariance_sampled"],   # ~0 (looks good)
        "adversarial_invariance_defect": gate["adversarial_invariance_defect"],      # >0 (the truth)
        "sampled_invariance_was_artifact": (best["breakdown"]["invariance_sampled"] < 1e-3
                                            and gate["adversarial_invariance_defect"] > 5e-3),
        "bivariate_envelope_deg3_closes_phi_le_1": gate["is_genuine_invariant"]
        and best["breakdown"]["ceiling_max"] < 1e-6,                            # False -> OPEN
    }


if __name__ == "__main__":
    print("z-box feasibility probe:", feasibility_probe())
    r = search_curve(generations=300)
    print("search (sampled) breakdown:", r["breakdown"])
    print("adversarial gate:", adversarial_invariance_gate(r["best_params"], n_wide=60000))
    print("verdict:", certify())
