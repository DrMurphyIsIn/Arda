"""Probe (b): K=4 discharging -- how far does the 1-hop plateau drop with the tighter envelope
and higher moments? Per-vertex objective g_K(v) = sum_{k=1}^K c_k (N^{2k})_{vv} (exact, on a large
realization so k-balls are complete). Compare K=2 vs K=4:
  - the caterpillar 3 vertex types (leaf/arm-mid/hub) -- can a 1-hop w make all <= log rho*?
  - the small-path binding pair {leaf, path-interior} that floored K=2 at 0.231.
"""
import sys
import numpy as np
sys.path.insert(0, 'telperion/src')
import networkx as nx
from scipy.optimize import linprog
LOG_RHO = 0.2050983

def env(K, grid=3000):
    u = np.linspace(1e-6, 1, grid); t = 0.5*np.log(1+u)
    Am = np.vstack([u**k for k in range(1, K+1)]).T
    return linprog(Am.mean(0), A_ub=-Am, b_ub=-t, bounds=[(-5, 5)]*K, method='highs').x

def Nmat(n, e):
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(e)
    A = nx.to_numpy_array(G, nodelist=range(n)); dg = A.sum(1)
    return np.diag(1/np.sqrt(dg))@A@np.diag(1/np.sqrt(dg)), dg

def gvert(N, K, c, v):
    """per-vertex g_K(v) = sum_k c_k (N^{2k})_vv."""
    val = 0.0; P = N.copy()
    for k in range(1, K+1):
        P2 = np.linalg.matrix_power(N, 2*k)
        val += c[k-1]*P2[v, v]
    return val

def caterpillar_legs(sp, a, L):
    e = []; nid = sp
    for i in range(sp-1): e.append((i, i+1))
    for i in range(sp):
        for _ in range(a):
            p = i
            for _ in range(L): e.append((p, nid)); p = nid; nid += 1
    return nid, e

# build a big a=7 caterpillar; identify a mid-spine hub, its arm-mid, its leaf
a = 7; SP = 41; n, e = caterpillar_legs(SP, a, 2)
N, dg = Nmat(n, e)
hub = SP//2
# neighbors of hub: spine hubs (deg a+2) + arm-mids (deg 2). pick an arm-mid child:
adj = {i: [] for i in range(n)}
for x, y in e: adj[x].append(y); adj[y].append(x)
armmid = [u for u in adj[hub] if abs(dg[u]-2) < .5][0]
leaf = [u for u in adj[armmid] if dg[u] == 1][0]

for K in (2, 4):
    c = env(K)
    gl = gvert(N, K, c, leaf); ga = gvert(N, K, c, armmid); gh = gvert(N, K, c, hub)
    print(f"\n=== K={K}  c={np.round(c,4)} ===")
    print(f"  caterpillar per-vertex g: leaf={gl:.5f} arm-mid={ga:.5f} hub(deg{int(dg[hub])})={gh:.5f}  (log rho*={LOG_RHO:.5f})")
    # 3-type tightness: solve w12,w29 s.t. all three == log rho* (over-determined 3 eq/2 unk)
    # leaf: gl - w12 ; arm: ga + w12 - w2h ; hub: gh + a*w2h   (w2h=w(2,hubdeg))
    import numpy as _np
    Amat = _np.array([[ -1, 0],[1,-1],[0, a]]); bvec = _np.array([LOG_RHO-gl, LOG_RHO-ga, LOG_RHO-gh])
    sol, res, *_ = _np.linalg.lstsq(Amat, bvec, rcond=None)
    resid = Amat@sol - bvec
    print(f"  3-type discharge lstsq w=(w12,w2hub)={_np.round(sol,5)} residual(each type - logrho after w)={_np.round(resid,6)}")
    print(f"    -> max |residual| = {_np.max(_np.abs(resid)):.2e}  ({'TIGHT (1-hop closes at caterpillar)' if _np.max(_np.abs(resid))<1e-4 else 'NOT tight -- 1-hop cannot pin all 3 types'})")
    # small-path binding pair floor: leaf-in-P and interior-in-P
    for (pn, pe, lbl) in [(4, [(0,1),(1,2),(2,3)], 'P4')]:
        Np, _ = Nmat(pn, pe)
        gpl = gvert(Np, K, c, 0)        # P4 leaf
        gpi = gvert(Np, K, c, 1)        # P4 interior (deg2, nbrs deg1&deg2)
        print(f"  {lbl}: g_leaf={gpl:.5f} g_interior={gpi:.5f}  pairwise floor (gl+gi)/2={(gpl+gpi)/2:.5f}")
