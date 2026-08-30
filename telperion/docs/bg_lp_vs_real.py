"""Precise check: flag-LP min m2 vs best REAL tree, at matched m1. Confirms (i) LP <= real tree
(relaxation validity) and (ii) how tight the LP is to the true achievable boundary. Also tests whether
mixed-arm / multi-hub caterpillars beat the uniform caterpillar (=> the true phi is below uniform-cat)."""
import sys, itertools
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')

def m12_exact(n, e):
    d = [0]*n; adj = [[] for _ in range(n)]
    for a, b in e: d[a] += 1; d[b] += 1; adj[a].append(b); adj[b].append(a)
    m1 = F(0); m2 = F(0)
    for v in range(n):
        dv = d[v]; S = sum(F(1, d[a]) for a in adj[v]); Q = sum(F(1, d[a]**2) for a in adj[v])
        m1 += S/dv; m2 += 2*S*S/(dv*dv) - Q/(dv*dv)
    return float(m1/n), float(m2/n)

def spine_tree(SP, arms, L):
    e = []; nid = SP
    for i in range(SP-1): e.append((i, i+1))
    for i in range(SP):
        for _ in range(arms[i]):
            p = i
            for _ in range(L): e.append((p, nid)); p = nid; nid += 1
    return nid, e

# enumerate MANY real trees, record (m1, m2, label)
real = []
for a in range(4, 14):
    for L in (2, 3):
        n, e = spine_tree(40, [a]*40, L); real.append((*m12_exact(n, e), f"uniform a={a} L={L}"))
for a1 in range(5, 12):
    for a2 in range(5, 12):
        for k in range(1, 4):   # every k-th vertex uses a2
            arms = [a2 if i % k == 0 else a1 for i in range(40)]
            n, e = spine_tree(40, arms, 2); real.append((*m12_exact(n, e), f"a1={a1}/a2={a2}/k={k}"))
for a in range(6, 20):
    for k in (2, 3, 4):
        arms = [a if i % k == 0 else 0 for i in range(42)]
        n, e = spine_tree(42, arms, 2); real.append((*m12_exact(n, e), f"hub a={a} every-{k}"))

# flag-LP (DMAX=9) min m2 at a given m1
DMAX = 9
types = []
for d in range(1, DMAX+1):
    for c in itertools.combinations_with_replacement(range(1, DMAX+1), d): types.append((d, c))
NT = len(types)
xv = np.array([sum(1.0/e for e in t[1])/t[0] for t in types])
m2c = np.array([2*(sum(1.0/e for e in t[1])/t[0])**2 - sum(1.0/e**2 for e in t[1])/t[0]**2 for t in types])
dvv = np.array([t[0] for t in types], float)
rows = [np.ones(NT), dvv.copy()]; rhs = [1.0, 2.0]
for d in range(1, DMAX+1):
    for e in range(d+1, DMAX+1):
        row = np.zeros(NT)
        for i, t in enumerate(types):
            if t[0] == d: row[i] += sum(1 for z in t[1] if z == e)
            if t[0] == e: row[i] -= sum(1 for z in t[1] if z == d)
        rows.append(row); rhs.append(0.0)
Ab = np.array(rows); bb = np.array(rhs)
def lp_min(M1):
    r = linprog(m2c, A_eq=np.vstack([Ab, xv]), b_eq=np.append(bb, M1), bounds=[(0, None)]*NT, method='highs')
    return r.fun if r.success else None

print(" m1_target | LP min m2 | best REAL tree m2 (label)            | uniform-cat m2 | LP<=real?")
for M1 in [0.516, 0.518, 0.520, 0.522, 0.524]:
    near = [(m2, lab, m1) for (m1, m2, lab) in real if abs(m1 - M1) < 0.0006]
    if not near:
        print(f"  {M1:.3f}   | (no real tree near this m1)"); continue
    bm2, blab, bm1 = min(near)
    unifs = [(m2, m1) for (m1, m2, lab) in real if 'uniform' in lab and abs(m1-M1) < 0.003]
    ucat = min(unifs)[0] if unifs else float('nan')
    lp = lp_min(M1)
    ok = "YES" if lp <= bm2 + 1e-9 else "*** NO (bug) ***"
    print(f"  {M1:.3f}   |  {lp:.5f}  | {bm2:.5f} ({blab}, m1={bm1:.4f}) | {ucat:.5f}    | {ok}  gap={bm2-lp:+.5f}")
