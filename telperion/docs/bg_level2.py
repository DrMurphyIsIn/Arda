"""Level-2 (pair / 2-ball) flag lift vs the 1-ball flag-LP.

1-ball LP (W8): min m2 s.t. m1=M over vertex-type dist pi, with norm + mean-degree-2 + 1-hop mass transport.
Level-2 adds a JOINT edge-type variable e(a,b) >= 0 (density of directed edges from a type-a vertex to a
type-b vertex) with:
    marginal:   sum_{b: deg(b)=k} e(a,b) = pi(a) * count_k(a)     (edges a->deg-k neighbours split by head type)
    symmetry:   e(a,b) = e(b,a)                                    (each undirected edge counted both ways)
This enforces 2-hop coherence the 1-ball relaxation lacks. If min m2 rises toward the true bounded-degree
tree min, the pair lift tightens the cut. Tractable at small DMAX.
"""
import sys, itertools
import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')

def build_types(DMAX):
    return [(d, c) for d in range(1, DMAX+1)
            for c in itertools.combinations_with_replacement(range(1, DMAX+1), d)]

def moms(d, c):
    S = sum(F(1, e) for e in c); Q = sum(F(1, e*e) for e in c); x = S/d
    return float(x), float(2*x*x - Q/(d*d))

def oneball_min(DMAX, M1):
    types = build_types(DMAX); NT = len(types)
    xv = np.array([moms(d, c)[0] for d, c in types])
    m2c = np.array([moms(d, c)[1] for d, c in types])
    dv = np.array([d for d, _ in types], float)
    rows = [np.ones(NT), dv.copy()]; rhs = [1.0, 2.0]
    for d in range(1, DMAX+1):
        for e in range(d+1, DMAX+1):
            row = np.zeros(NT)
            for i, (dd, c) in enumerate(types):
                if dd == d: row[i] += sum(1 for z in c if z == e)
                if dd == e: row[i] -= sum(1 for z in c if z == d)
            rows.append(row); rhs.append(0.0)
    r = linprog(m2c, A_eq=np.vstack([np.array(rows), xv]), b_eq=np.append(np.array(rhs), M1),
                bounds=[(0, None)]*NT, method='highs')
    return r.fun if r.success else None

def level2_min(DMAX, M1):
    types = build_types(DMAX); NT = len(types)
    deg = [d for d, _ in types]
    cnt = [{} for _ in types]
    for i, (d, c) in enumerate(types):
        for e in c: cnt[i][e] = cnt[i].get(e, 0) + 1
    xv = np.array([moms(d, c)[0] for d, c in types])
    m2c = np.array([moms(d, c)[1] for d, c in types])
    # joint edge vars: pairs (i,j) with deg(j) in cnt[i] AND deg(i) in cnt[j]
    pair_idx = {}
    for i in range(NT):
        for j in range(NT):
            if deg[j] in cnt[i] and deg[i] in cnt[j]:
                pair_idx[(i, j)] = NT + len(pair_idx)
    NE = len(pair_idx); NV = NT + NE
    A = []; b = []
    def row():
        return np.zeros(NV)
    # norm, mean degree, m1
    r = row();  r[:NT] = 1.0;               A.append(r); b.append(1.0)
    r = row();  r[:NT] = np.array(deg, float); A.append(r); b.append(2.0)
    r = row();  r[:NT] = xv;                A.append(r); b.append(M1)
    # marginal: for each type i and neighbour degree k: sum_j e(i,j) = pi(i)*cnt[i][k]
    for i in range(NT):
        for k, c_ik in cnt[i].items():
            r = row(); r[i] = -c_ik
            for j in range(NT):
                if deg[j] == k and (i, j) in pair_idx: r[pair_idx[(i, j)]] = 1.0
            A.append(r); b.append(0.0)
    # symmetry e(i,j)=e(j,i)  (i<j)
    for (i, j), p in pair_idx.items():
        if i < j and (j, i) in pair_idx:
            r = row(); r[p] = 1.0; r[pair_idx[(j, i)]] = -1.0; A.append(r); b.append(0.0)
    c_obj = np.concatenate([m2c, np.zeros(NE)])
    res = linprog(c_obj, A_eq=np.array(A), b_eq=np.array(b), bounds=[(0, None)]*NV, method='highs')
    return res.fun if res.success else None, NT, NE

# best real degree-<=DMAX tree at m1 (family search) as an upper bound on true min
def spine(SP, arms, L):
    e = []; nid = SP
    for i in range(SP-1): e.append((i, i+1))
    for i in range(SP):
        for _ in range(arms[i]):
            p = i
            for _ in range(L): e.append((p, nid)); p = nid; nid += 1
    return nid, e
def m12(n, e):
    d = [0]*n; adj = [[] for _ in range(n)]
    for a, b in e: d[a]+=1; d[b]+=1; adj[a].append(b); adj[b].append(a)
    m1=F(0); m2=F(0)
    for v in range(n):
        S=sum(F(1,d[k]) for k in adj[v]); Q=sum(F(1,d[k]**2) for k in adj[v])
        m1+=S/d[v]; m2+=2*S*S/(d[v]*d[v])-Q/(d[v]*d[v])
    return float(m1/n), float(m2/n)
def best_real(DMAX, M1):
    best = 9.9
    for a1 in range(1, DMAX-1):
        for a2 in range(1, DMAX-1):
            for k in range(1, 4):
                arms = [a2 if i % k == 0 else a1 for i in range(40)]
                if max(arms)+2 > DMAX: continue
                n, e = spine(40, arms, 2); m1, m2 = m12(n, e)
                if abs(m1-M1) < 0.002 and m2 < best: best = m2
    return best if best < 9 else None

for DMAX in (4, 5):
    print(f"\n=== DMAX={DMAX} ===")
    print("  m1  | 1-ball min | LEVEL-2 min | best real tree | (level2 - 1ball tightening)")
    for M1 in [0.52, 0.53, 0.54]:
        ob = oneball_min(DMAX, M1)
        l2, NT, NE = level2_min(DMAX, M1)
        br = best_real(DMAX, M1)
        brs = f"{br:.5f}" if br else "  --   "
        print(f" {M1:.2f} |  {ob:.5f}  |   {l2:.5f}  |    {brs}     | +{l2-ob:.5f}  (NT={NT},NE={NE})")
