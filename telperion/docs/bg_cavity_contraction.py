"""Lead 1 foundation: is the matching cavity map a CONTRACTION (Heilmann-Lieb), and does the
finite-DEPTH truncation of the free energy converge GEOMETRICALLY to log rho*?

Cavity map on a directed edge:  x_{u->v} = sum_{c~u, c!=v} w_{uc}/(1+x_{c->u}),  w=1/(d_u d_c).
Jacobian magnitude  sum_c w_{uc}/(1+x_{c->u})^2 < (d_u-1)/d_u < 1  => contraction.

Test A: propagate a perturbation of the leaf message up an arm/spine of the caterpillar; measure decay.
Test B: compute the caterpillar free energy with messages truncated at depth d (set to 0 below depth d),
        vs the exact fixed point; error should be ~ rho_contract^d (geometric).  If so, Lead 1 gives
        F(T) <= log rho* + C rho^d -- a GEOMETRICALLY convergent bound (better than W9's slow moment hierarchy).
"""
import math
import numpy as np
from scipy.optimize import brentq

LOG_RHO = math.log(1.2276458)


def caterpillar_edges(spine_len, a, leg=2):
    e = []; nid = spine_len
    for i in range(spine_len - 1):
        e.append((i, i + 1))
    for i in range(spine_len):
        for _ in range(a):
            p = i
            for _ in range(leg):
                e.append((p, nid)); p = nid; nid += 1
    return nid, e


def cavity_fixed(n, edges, iters, init=0.0):
    """Run the cavity recursion for `iters` sweeps from init; return messages + degrees/adj/w."""
    d = [0] * n; adj = [[] for _ in range(n)]
    for a, b in edges:
        d[a] += 1; d[b] += 1; adj[a].append(b); adj[b].append(a)
    w = {}
    for a, b in edges:
        w[(a, b)] = w[(b, a)] = 1.0 / (d[a] * d[b])
    x = {(a, b): init for a, b in edges}
    x.update({(b, a): init for a, b in edges})
    for _ in range(iters):
        nx = {}
        for (u, v) in x:
            nx[(u, v)] = sum(w[(u, c)] / (1.0 + x[(c, u)]) for c in adj[u] if c != v)
        x = nx
    return d, adj, w, x


def bethe_density(n, edges, iters, init=0.0):
    d, adj, w, x = cavity_fixed(n, edges, iters, init)
    q = {k: 1.0 / (1.0 + x[k]) for k in x}
    vs = sum(math.log(1.0 + sum(w[(v, a)] * q[(a, v)] for a in adj[v])) for v in range(n))
    seen = set(); es = 0.0
    for a, b in edges:
        e = (min(a, b), max(a, b))
        if e in seen: continue
        seen.add(e)
        es += math.log(1.0 + w[(a, b)] * q[(a, b)] * q[(b, a)])
    return (vs - es) / n


# Test A: contraction rate along a long arm/spine
print("=== Test A: perturbation decay (contraction factor) ===")
n, e = caterpillar_edges(30, 7, 2)
d, adj, w, x0 = cavity_fixed(n, e, 400)          # converged
# perturb one leaf's message, re-propagate a few sweeps, measure how the change shrinks per hop
import copy
xp = dict(x0)
# find a leaf and its directed edge to arm-mid
deg = d
leaf = next(v for v in range(n) if deg[v] == 1)
am = adj[leaf][0]
xp[(leaf, am)] += 0.1
# one synchronous sweep: measure max change at distance-k edges (crude contraction proxy)
prev = 0.1
for hop in range(1, 8):
    nx = {}
    for (u, v) in xp:
        nx[(u, v)] = sum(w[(u, c)] / (1.0 + xp[(c, u)]) for c in adj[u] if c != v)
    diffs = [abs(nx[k] - x0[k]) for k in nx]
    mx = max(diffs)
    print(f"  sweep {hop}: max|deviation from fixed pt| = {mx:.3e}  ratio={mx/prev:.3f}")
    prev = mx if mx > 0 else prev
    xp = nx

# Test B: depth-truncated free energy convergence
print("\n=== Test B: free energy vs cavity ITERATIONS (depth) -> geometric convergence to log rho* ===")
n, e = caterpillar_edges(40, 7, 2)
Fstar = bethe_density(n, e, 500)
print(f"  converged F (a=7, spine 40) = {Fstar:.6f}   log rho* = {LOG_RHO:.6f}")
prev_err = None
for it in range(1, 12):
    Fit = bethe_density(n, e, it, init=0.0)
    err = abs(Fit - Fstar)
    ratio = (err / prev_err) if prev_err and prev_err > 0 else float('nan')
    print(f"  iters={it:2d}: F={Fit:.6f}  |F-F*|={err:.3e}  ratio={ratio:.3f}")
    prev_err = err
