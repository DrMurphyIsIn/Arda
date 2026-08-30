"""Probe (a): the moment-SDP proper.  max_mu  G=sum_k c_k m_k  over measures mu on [0,1],
subject to Hankel-PSD (moment + localizing matrices) and the tree walk-count cuts (S2).

Stages (to see which constraint closes the gap to log rho*):
  0. envelope only (no measure constraint)  -- trivially c-sum at u=1
  1. + Hankel-PSD (mu a measure on [0,1])   -- W3 'overshoot'
  2. + m_1 <= max_T m_1  (W2 linear cut)
  3. + m_2 >= phi(m_1) tangent at caterpillar (W4 lower cut)
Report max G at each stage vs log rho* and vs the caterpillar's own moments.
"""
import sys
import numpy as np
import cvxpy as cp
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')
import networkx as nx

LOG_RHO = 0.2050983

def envelope(K, grid=3000):
    u = np.linspace(1e-6, 1, grid); t = 0.5*np.log(1+u)
    Am = np.vstack([u**k for k in range(1, K+1)]).T
    return linprog(Am.mean(0), A_ub=-Am, b_ub=-t, bounds=[(-5, 5)]*K, method='highs').x

def caterpillar_legs(sp, a, L):
    e = []; nid = sp
    for i in range(sp-1): e.append((i, i+1))
    for i in range(sp):
        for _ in range(a):
            p = i
            for _ in range(L): e.append((p, nid)); p = nid; nid += 1
    return nid, e

def moms(n, e, K):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(e)
    A = nx.to_numpy_array(G, nodelist=range(n)); dg = A.sum(1)
    N = np.diag(1/np.sqrt(dg))@A@np.diag(1/np.sqrt(dg))
    return [np.trace(np.linalg.matrix_power(N, 2*k))/n for k in range(1, K+1)]

# max_T m_1 (W2): exhaustive small + path/double-broom limit -> ~ 0.5..0.625
def max_m1(nmax=14):
    best = 0
    for n in range(2, nmax+1):
        for T in nx.nonisomorphic_trees(n):
            idx = {v: i for i, v in enumerate(T.nodes())}; ed = [(idx[a], idx[b]) for a, b in T.edges()]
            best = max(best, moms(n, ed, 1)[0])
    return best

M1MAX = max_m1(13)

# caterpillar reference moments (a=7) up to order 6
CAT_N, CAT_E = caterpillar_legs(60, 7, 2)
CAT_M = moms(CAT_N, CAT_E, 6)

# phi(m_1) tangent at caterpillar a=7: use caterpillar family to get slope d m_2/d m_1
fam = [moms(*caterpillar_legs(60, a, 2), 2) for a in (6, 7, 8)]
m1_7, m2_7 = fam[1]
slope = (fam[2][1]-fam[0][1])/(fam[2][0]-fam[0][0])   # d m_2 / d m_1 along caterpillar

print(f"log rho*={LOG_RHO:.6f} | max_T m_1={M1MAX:.5f} | caterpillar a=7 m=({m1_7:.4f},{m2_7:.4f}) slope={slope:.3f}")
print(f"caterpillar moments m1..m6 = {[round(x,5) for x in CAT_M]}")

def solve(K, stage):
    c = envelope(K)
    m = cp.Variable(7)   # m[0..6], m[0]=1
    cons = [m[0] == 1]
    obj = cp.Maximize(sum(c[k-1]*m[k] for k in range(1, K+1)))
    if stage >= 1:
        M = cp.bmat([[m[i+j] for j in range(4)] for i in range(4)])          # moment matrix 4x4 (m0..m6)
        Lu = cp.bmat([[m[i+j+1] for j in range(3)] for i in range(3)])        # u>=0 localizing (m1..m5)
        L1 = cp.bmat([[m[i+j]-m[i+j+1] for j in range(3)] for i in range(3)]) # 1-u>=0 (m0..m5)
        cons += [M >> 0, Lu >> 0, L1 >> 0]
    if stage >= 2:
        cons += [m[1] <= M1MAX]
    if stage >= 3:
        # convex lower envelope of the caterpillar (m1,m2) boundary: many supporting tangents
        for a in range(4, 13):
            f0 = moms(*caterpillar_legs(60, a-1, 2), 2)
            f2 = moms(*caterpillar_legs(60, a+1, 2), 2)
            fa = moms(*caterpillar_legs(60, a, 2), 2)
            sl = (f2[1]-f0[1])/(f2[0]-f0[0])
            cons += [m[2] >= fa[1] + sl*(m[1]-fa[0])]
    prob = cp.Problem(obj, cons)
    prob.solve(solver=cp.SCS, eps=1e-8, max_iters=50000)
    return prob.value, m.value

for K in (2, 4, 6):
    print(f"\n--- envelope K={K}, c={np.round(envelope(K),4)} ---")
    for stage, name in [(1, 'Hankel only'), (2, '+m1 cut'), (3, '+m2>=phi tangent')]:
        val, mv = solve(K, stage)
        gap = (val - LOG_RHO) if val is not None else None
        m1v = mv[1] if mv is not None else float('nan')
        print(f"  stage {stage} ({name:18s}): max G={val:.6f}  gap={gap:+.6f}  (argmax m1={m1v:.4f})")
