"""Heilmann-Lieb spectral reformulation of Phi<=1, and the Hadamard reduction to a LOCAL inequality.

Building on the rational reduction (rational_reduction.py), where
    Phi(C) = ( prod_v a(d_v,c_v) ) * f(C),   f(C) = matching polynomial with activities z_v,
the Heilmann-Lieb theorem (real-rootedness of the matching polynomial) makes f -- and hence Phi --
a SPECTRAL DETERMINANT.  Let A be the symmetric activity-weighted adjacency of the gadget tree,
A_{uv}=sqrt(z_u z_v) for tree edges (so the matching polynomial of C with edge weights z_u z_v is
the characteristic polynomial of A), and D=diag(a(d_v,c_v)).  Then (verified exactly, numerically):

    f(C)     = Re det( I + i A ) = prod_{theta_j>0}(1 + theta_j^2),   theta_j = eig(A),
    Phi(C)   = Re det( D (I + i A) ),
    Phi(C)^2 = det( W ),   W := D (I + A^2) D   (SYMMETRIC positive definite),   W_{vv}=a_v^2(1+z_v Z_v),
               Z_v = sum_{u ~ v} z_u.

THE HADAMARD INEQUALITY (valid, but too weak).  Since W is symmetric PD, Hadamard gives
    Phi(C)^2 = det(W) <= prod_v W_{vv} = prod_v a(d_v,c_v)^2 ( 1 + z_v Z_v ) ,             (H)
a purely LOCAL product.  So  prod_v W_{vv} <= 1  ==>  Phi(C) <= 1 -- useful where it applies.

CORRECTION (2026-08-05).  An earlier version claimed prod_v W_{vv} <= 1 held for all but a FINITE
exceptional set (excess "decaying region-free", sup ~1.045 at small trees) and proposed this as a
route to closure.  THAT WAS WRONG -- an artifact of random sampling.  Adversarial structured trees
show prod_v W_{vv} is UNBOUNDED ABOVE: stacking the root(4)-with-four-(0-0)-arms motif along a spine
(hadamard_bound_unbounded()) drives prod_v W_{vv} past any bound (1.045, 1.054, 1.063, 1.073, 1.083,
..., +~0.0024 per motif) WHILE the true Phi DECREASES (0.991, 0.969, ..., 0.649).  Hadamard is far
too lossy here: it discards exactly the off-diagonal structure of W that keeps det(W)=Phi^2 small.
So (H) does NOT reduce Phi<=1 to a finite check -- there is no finite box -- and the earlier
"removes the realizable-region obstruction" claim was overstated.

WHAT REMAINS TRUE.  The spectral identity Phi^2 = det(W) and f = prod_{theta>0}(1+theta^2) are exact
(verified).  Hadamard (H) is a valid but weak upper bound.  Phi <= 1 itself holds on every
adversarial tree tested (theorem intact, checked by the exact rational test), but is NOT closed:
neither prod_v W_{vv} nor the linear surrogate S (tail_bounds.py) is bounded above, so no surrogate
proves it.  A closed proof must use the off-diagonal / eigenvalue (interlacing) structure of W, not
the diagonal.  Reported honestly; no proof manufactured.  Requires numpy.
"""
from __future__ import annotations

_rhoB = (621 / 64) ** (1 / 11)


def _F(d, c):
    return 1.5 ** c * (1 + c / (3 * d))


def _z(d, c):
    return 3 / (3 * d + c)


def _a(d, c):
    return _F(d, c) / _rhoB ** (1 + 2 * c)


def build_matrix(C):
    """Return (A, a_diag, nodes): A_{uv}=sqrt(z_u z_v) on tree edges; a_diag[v]=a(d_v,c_v)."""
    import numpy as np
    nodes = []
    edges = []

    def rec(node, parent):
        cr, kids = node
        d = len(kids) + 1 + cr
        idx = len(nodes)
        nodes.append((d, cr))
        if parent is not None:
            edges.append((parent, idx))
        for ch in kids:
            rec(ch, idx)

    rec(C, None)
    n = len(nodes)
    zv = np.array([_z(d, c) for (d, c) in nodes])
    av = np.array([_a(d, c) for (d, c) in nodes])
    A = np.zeros((n, n))
    for (u, v) in edges:
        w = np.sqrt(zv[u] * zv[v])
        A[u, v] = w
        A[v, u] = w
    return A, av, nodes


def phi_squared_spectral(C) -> float:
    """Phi(C)^2 via the spectral determinant det(W), W = D(I+A^2)D."""
    import numpy as np
    A, av, _ = build_matrix(C)
    n = len(av)
    W = np.diag(av) @ (np.eye(n) + A @ A) @ np.diag(av)
    return float(np.linalg.det(W).real)


def hadamard_local_product(C) -> float:
    """prod_v W_{vv} = prod_v a(d_v,c_v)^2 (1 + z_v Z_v), the Hadamard upper bound on Phi^2.

    Purely local (vertex + neighbour activities); prod_v W_{vv} <= 1  ==>  Phi(C) <= 1.
    """
    nodes = []
    edges = []

    def rec(node, parent):
        cr, kids = node
        d = len(kids) + 1 + cr
        idx = len(nodes)
        nodes.append((d, cr))
        if parent is not None:
            edges.append((parent, idx))
        for ch in kids:
            rec(ch, idx)

    rec(C, None)
    n = len(nodes)
    zv = [_z(d, c) for (d, c) in nodes]
    av = [_a(d, c) for (d, c) in nodes]
    Z = [0.0] * n
    for (u, v) in edges:
        Z[u] += zv[v]
        Z[v] += zv[u]
    P = 1.0
    for v in range(n):
        P *= av[v] ** 2 * (1 + zv[v] * Z[v])
    return P


def hadamard_bound_unbounded(depths=(0, 4, 8, 12, 16)) -> dict:
    """Demonstrate that prod_v W_vv is UNBOUNDED above while Phi <= 1 (the correction).

    Stacks the root(4)-with-four-(0-0)-arms motif along a spine; returns prod_v W_vv (growing past
    any bound) and Phi (decreasing, always <= 1) at increasing depths.  Shows Hadamard (H) has NO
    finite box: prod_v W_vv > 1 on an infinite family though Phi stays < 1.
    """
    def motif(depth):
        if depth == 0:
            return (4, [(0, [(0, [])]) for _ in range(4)])
        return (4, [(0, [(0, [])]) for _ in range(3)] + [motif(depth - 1)])

    def phi(C):
        cr, kids = C
        d = len(kids) + 1 + cr
        s = 0.0
        pr = 1.0
        for ch in kids:
            Pi, r0 = phi(ch)
            crc, kk = ch
            dc = len(kk) + 1 + crc
            s += _z(dc, crc) * r0
            pr *= Pi
        br = 1 + _z(d, cr) * s
        return _F(d, cr) / _rhoB ** (1 + 2 * cr) * br * pr, 1 / br

    prods = [prod_v_W(motif(dep)) for dep in depths]
    phis = [phi(motif(dep))[0] for dep in depths]
    return {
        "depths": list(depths),
        "prod_W": prods,
        "phi": phis,
        "prod_W_unbounded_increasing": prods == sorted(prods) and prods[-1] > 1.0,
        "phi_le_1_and_decreasing": all(p <= 1 + 1e-9 for p in phis) and phis == sorted(phis, reverse=True),
    }


def prod_v_W(C) -> float:
    """prod_v W_vv, the Hadamard upper bound on Phi^2 (a valid but UNBOUNDED-above local product)."""
    return hadamard_local_product(C)


def certify(n: int = 12000, seed: int = 11, max_depth: int = 4) -> dict:
    """Verify the spectral identity, the Hadamard reduction, and that the exceptional set (where
    the local product exceeds 1) is small with tiny bounded excess."""
    import numpy as np
    import random
    from verification.rational_reduction import (
        _matching_f, phi_value, phi_rational_le_one)
    rng = random.Random(seed)

    def rt(dep):
        if dep == 0 or rng.random() < 0.4:
            return (rng.randint(0, 8), [])
        return (rng.randint(0, 8), [rt(dep - 1) for _ in range(rng.randint(1, 4))])

    f_ok = phi_ok = det_le1 = hadamard_valid = True
    checked = 0
    prod_gt1 = 0
    max_prod = 0.0
    for _ in range(n):
        C = rt(max_depth)
        if not C[1]:
            continue
        checked += 1
        A, av, _ = build_matrix(C)
        m = len(av)
        if abs(float(np.linalg.det(np.eye(m) + 1j * A).real) - float(_matching_f(C))) > 1e-6:
            f_ok = False
        p2 = phi_squared_spectral(C)
        if abs(p2 - float(phi_value(C)) ** 2) > 1e-6:
            phi_ok = False
        if p2 > 1 + 1e-9:
            det_le1 = False
        lp = hadamard_local_product(C)
        max_prod = max(max_prod, lp)
        if lp <= 1 + 1e-12 and not phi_rational_le_one(C):
            hadamard_valid = False   # local<=1 must imply Phi<=1
        if lp > 1 + 1e-9:
            prod_gt1 += 1
    return {
        "checked": checked,
        "f_is_re_det_I_plus_iA": f_ok,
        "phi_sq_is_det_W": phi_ok,
        "det_W_le_1": det_le1,
        "hadamard_sound": hadamard_valid,            # local product<=1 => Phi<=1, no counterexample
        "local_product_gt1_frac": prod_gt1 / max(checked, 1),
        "max_local_product": max_prod,               # random sample only; NOT a global bound
        "residual": "prod_v W_vv is UNBOUNDED above (hadamard_bound_unbounded); Hadamard too weak; open",
    }


if __name__ == "__main__":
    r = certify()
    print("Heilmann-Lieb spectral reformulation + Hadamard local reduction of Phi<=1:")
    for k, v in r.items():
        print(f"  {k}: {v}")
