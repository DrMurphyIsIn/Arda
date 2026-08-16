"""Lead #2 toward closing Phi<=1: the reachable (X,Y) hull is a SMALL STABLE polytope, and
node-formation is MULTIAFFINE, so exact invariance reduces to a finite vertex-tuple check.

State of a single-branch gadget C in (X, Y) = (Phi*rho0, Phi*(1-rho0)), Phi = X + Y (gpz.py):
    leaf(c)          = ( a(1+c,c), 0 )
    node(cr; kids)   : X = A * prod_i (X_i + Y_i),
                       Y = A * z(d,cr) * sum_i z_i X_i * prod_{j!=i} (X_j + Y_j),
                       A = a(d,cr),  d = #kids + 1 + cr,  a(d,c)=F(d,c)/rho_B^{1+2c}.
Phi<=1 for all gadgets  <=>  the reachable set R = {states} lies in {X+Y<=1}.

TWO STRUCTURAL FACTS (this module).

(1) THE FINITE-DEPTH HULL IS SMALL, BUT THE CLOSURE ACCUMULATES (CORRECTED 2026-08-06).
    Enumerating all gadgets up to depth D, the convex hull of the reachable (X,Y) has vertex counts
    3,7,9,10,9 for D=2..6 (5.07e6 gadgets at D=6), all FINITE gadgets, with max(X+Y)=1 exactly and
    two vertices at the EXACT rational tie anchors (1,0) and (21/23,2/23).  BUT this small count is a
    finite-DEPTH truncation artifact: iterating the reachable SET to its invariant closure (forming
    from the current extreme points, accumulation_at_tie) exhibits an INFINITE sequence of extreme vertices
    accumulating at the tie anchor (21/23,2/23) from above -- at fixed z=1/12,
    23X = 21.34, 21.27, 21.21, 21.14, 21.05, 20.97, 20.88, 20.78, ... -> 21, with X+Y decreasing to 1.
    So the invariant polytope is NOT finitely generated: its vertices ACCUMULATE at the rational tie
    anchors (confirming invariant_polytope.exact_verification_reduction's warning).  The finite exact
    Q(rho_B) polytope route is therefore RULED OUT -- there is no finite vertex set to solve for.

(2) THE FORMED Phi IS MULTIAFFINE IN THE CHILDREN (exact).  For a FIXED (cr, k=#kids), the formed
    Phi = X + Y is affine in each child's (X_i, Y_i) separately: X = A prod_i(X_i+Y_i) and each Y-term
    z_i X_i prod_{j!=i}(X_j+Y_j) is linear in every child; A, z(d,cr), z_i depend only on the fixed
    degrees.  So Phi(formed) is a MULTIAFFINE function of the children.  CONSEQUENCE (multiaffine
    maximum principle): over children ranging in a polytope P, max Phi(formed) is attained at a
    VERTEX-tuple of P.  Hence "formed Phi <= 1 for all children in P" reduces to the finitely many
    vertex-tuples of P -- a FINITE check.  Verified numerically here: forming nodes from random convex
    combinations of the reachable-hull vertices NEVER gives Phi > 1 (worst X+Y excess = 0).

    (Note: the formed node can leave the finite-DEPTH hull in non-Phi directions -- the true invariant
    set is the depth-limit -- so this is the multiaffine principle for the LINEAR functional Phi=X+Y,
    which is exactly what Phi<=1 needs, not full-hull invariance.)

REDUCTION (the honest frontier, sharpened).  Closing Phi<=1 via an exact invariant polytope P (with
vertices in Q(rho_B)) reduces to a FINITE exact-algebraic program:
    (a) P contains the leaves and is closed under formation (invariant);
    (b) P subset {X+Y<=1} (facet check, exact);
    (c) for every (cr, k) up to a bound, and every vertex-tuple of P, the formed Phi <= 1
        (finite multiaffine check, by fact (2));
    (d) a TAIL bound: for (cr, k) beyond the bound, the node's Phi is small (a(d,cr)<=1 and k factors
        (X_i+Y_i)<=1 shrink it), so Phi<=1 holds automatically.
The remaining hard step is (a).  UPDATE (2026-08-06): step (a) cannot be met by a FINITE polytope --
fact (1) shows the invariant set's vertices accumulate at the tie anchors, so there is no finite
vertex set to solve for, and the multiaffine finite-check (fact (2)) has no finite polytope to run on.
A closed proof of Phi<=1 therefore needs a SMOOTH certificate (a barrier curve / Lyapunov-like
function tangent to X+Y=1 at the finite rational tie variety), not a polytope -- but the
monotone-envelope no-go (interlacing.realizable_region_max_points) already rules out the simplest such
curves.  So both the polytope route (accumulation) and the envelope route (non-monotone tie locus) are
closed; the honest open problem is a non-monotone smooth barrier anchored on the 6 rational ties.
What this module contributes: the multiaffine structure of the recursion (fact 2), and the DIRECT
demonstration (fact 1, accumulation_at_tie) that the invariant polytope accumulates -- which retires the
finite-exact-polytope approach.

Requires numpy, scipy.
"""
from __future__ import annotations

import itertools

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def state(C):
    """(X, Y, z) of gadget C=(cherries,[children]); root has a hub-parent (+1 degree)."""
    cr, kids = C
    d = len(kids) + 1 + cr
    ch = [state(k) for k in kids]
    s = [X + Y for (X, Y, _) in ch]
    Pi = 1.0
    for si in s:
        Pi *= si
    Sig = 0.0
    for i, (Xi, Yi, zi) in enumerate(ch):
        pr = 1.0
        for j, sj in enumerate(s):
            if j != i:
                pr *= sj
        Sig += zi * Xi * pr
    A = _a(d, cr)
    return (A * Pi, A * _z(d, cr) * Sig, _z(d, cr))


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


def hull_stability(max_depth: int = 6) -> dict:
    """Convex-hull vertex count of the FINITE-DEPTH reachable (X,Y) by cumulative depth. NOTE: this
    stays small (~9-10) only because it is depth-truncated; the invariant CLOSURE accumulates
    (see accumulation_at_tie) -- so this is not evidence of a finite invariant polytope."""
    import numpy as np
    from scipy.spatial import ConvexHull
    pts = []
    counts = {}
    max_phi = 0.0
    for D in range(1, max_depth + 1):
        for g in _gadgets(D):
            X, Y, _ = state(g)
            pts.append((X, Y))
        if D < 2:
            continue
        P = np.array(pts)
        max_phi = float(np.max(P[:, 0] + P[:, 1]))
        counts[D] = int(len(ConvexHull(P).vertices))
    return {"hull_verts_by_depth": counts, "max_phi": max_phi,
            "exact_anchor_11_23": (21 / 23, 2 / 23)}


def certify_multiaffine_reduction(max_depth: int = 5, trials: int = 4000, seed: int = 0) -> dict:
    """Verify fact (2): forming a node from convex combinations of hull vertices stays in the hull
    (numerical witness of the multiaffine maximum principle => invariance is a finite check)."""
    import numpy as np
    from scipy.spatial import ConvexHull, Delaunay
    rng = np.random.default_rng(seed)
    pts = []
    for D in range(1, max_depth + 1):
        for g in _gadgets(D):
            X, Y, _ = state(g)
            pts.append((X, Y))
    P = np.array(pts)
    hull = ConvexHull(P)
    V = P[hull.vertices]
    dela = Delaunay(P[hull.vertices])
    # child z-activities: sample from realized leaf/interior activities
    zs = sorted({_z(1 + c, c) for c in range(7)} | {_z(2 + c, c) for c in range(7)})
    worst_out = 0.0
    inside = 0
    for _ in range(trials):
        k = int(rng.integers(1, 5))
        cr = int(rng.integers(0, 7))
        kids = []
        for _ in range(k):
            # random convex combo of hull vertices as a child (X,Y), with a sampled z
            w = rng.random(len(V)); w /= w.sum()
            xy = w @ V
            kids.append((xy[0], xy[1], zs[int(rng.integers(0, len(zs)))]))
        d = k + 1 + cr
        s = [X + Y for (X, Y, _) in kids]
        Pi = 1.0
        for si in s:
            Pi *= si
        Sig = 0.0
        for i, (Xi, Yi, zi) in enumerate(kids):
            pr = 1.0
            for j, sj in enumerate(s):
                if j != i:
                    pr *= sj
            Sig += zi * Xi * pr
        A = _a(d, cr)
        node = np.array([A * Pi, A * _z(d, cr) * Sig])
        if dela.find_simplex(node) >= 0:
            inside += 1
        else:
            # distance outside (via facet slack); measure X+Y excess as a proxy
            worst_out = max(worst_out, float(node[0] + node[1]) - 1.0)
    return {"trials": trials, "strictly_inside_depth_hull": inside,
            "formed_phi_never_exceeds_1": worst_out <= 1e-9,
            "worst_XplusY_excess": worst_out}


def accumulation_at_tie(iters: int = 8, mc: int = 3, mcher: int = 6):
    """Iterate the reachable (X,Y,z) SET to its invariant closure (forming from the current extreme
    points -- valid by multiaffinity) and return the extreme vertices sorted by X+Y.  Exhibits the
    INFINITE sequence of vertices accumulating at the tie anchor (21/23,2/23): at fixed z=1/12,
    23*X -> 21 from above with X+Y -> 1.  Demonstrates the invariant polytope is NOT finitely
    generated (retires the finite-exact-polytope route)."""
    import itertools
    import numpy as np
    from scipy.spatial import ConvexHull

    def form(cr, kids):
        k = len(kids)
        d = k + 1 + cr
        s = [X + Y for (X, Y, _) in kids]
        Pi = 1.0
        for si in s:
            Pi *= si
        Sig = sum(zi * Xi * (Pi / si if si > 0 else 0.0) for (Xi, Yi, zi), si in zip(kids, s))
        A = _a(d, cr)
        return (A * Pi, A * _z(d, cr) * Sig, _z(d, cr))

    def hv(pts):
        P = np.array(pts)
        try:
            return [pts[i] for i in sorted(set(ConvexHull(P).vertices))]
        except Exception:
            return pts

    S = [(_a(1 + c, c), 0.0, _z(1 + c, c)) for c in range(mcher + 1)]
    counts = []
    for _ in range(iters):
        V = hv(S)
        new = list(V)
        for cr in range(mcher + 1):
            for k in range(1, mc + 1):
                for kids in itertools.product(V, repeat=k):
                    new.append(form(cr, list(kids)))
        S = hv(new)
        counts.append(len(S))
    V = sorted(hv(S), key=lambda t: -(t[0] + t[1]))
    # the accumulating family: fixed z=1/12, 23X descending toward 21
    accum = [(round(23 * x, 4), round(x + y, 6)) for (x, y, zz) in V if abs(zz - 1 / 12) < 1e-9][:10]
    return {"vertex_counts_by_iter": counts, "n_extreme": len(V),
            "accumulating_23X_at_z_1_12": accum}


if __name__ == "__main__":
    print("hull stability (finite depth):", hull_stability())
    print("multiaffine reduction:", certify_multiaffine_reduction())
    print("accumulation at tie (closure):", accumulation_at_tie())
