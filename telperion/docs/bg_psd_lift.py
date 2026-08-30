"""PSD (Lasserre / reflection-positivity) lift of the flag relaxation.

The LINEAR pair lift is vacuous (joint edge always fillable given mass transport). The genuine tightening
is the SDP level: constrain the joint edge measure E=[e(a,b)] (density of edges between type-a and type-b
vertices) to be PSD as a matrix (reflection positivity of the 2-point function) -- NOT just entrywise >=0.

min_{pi>=0, E>=0, E=E^T, E PSD}  sum_a pi(a) (2x_a^2 - q_a)
  s.t.  sum pi = 1,  sum pi*deg = 2,  sum pi*x = M1,
        marginal: sum_{b: deg(b)=k} E[a,b] = pi(a)*count_k(a)   for each type a, neighbour degree k.
Compare min m2 to the 1-ball LP and the best real degree-<=DMAX tree.
"""
import sys, itertools
import numpy as np
import cvxpy as cp
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')

def build_types(DMAX):
    return [(d, c) for d in range(1, DMAX+1)
            for c in itertools.combinations_with_replacement(range(1, DMAX+1), d)]
def moms(d, c):
    S = sum(F(1, e) for e in c); Q = sum(F(1, e*e) for e in c); x = S/d
    return float(x), float(2*x*x - Q/(d*d))

def oneball(DMAX, M1):
    types = build_types(DMAX); NT = len(types)
    xv = np.array([moms(d, c)[0] for d, c in types]); m2c = np.array([moms(d, c)[1] for d, c in types])
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
    return r.fun

def psd_lift(DMAX, M1):
    types = build_types(DMAX); NT = len(types)
    deg = [d for d, _ in types]
    cnt = [{} for _ in types]
    for i, (d, c) in enumerate(types):
        for e in c: cnt[i][e] = cnt[i].get(e, 0) + 1
    xv = np.array([moms(d, c)[0] for d, c in types]); m2c = np.array([moms(d, c)[1] for d, c in types])
    pi = cp.Variable(NT, nonneg=True)
    E = cp.Variable((NT, NT), symmetric=True)
    cons = [E >> 0, E >= 0, cp.sum(pi) == 1, pi @ np.array(deg, float) == 2, pi @ xv == M1]
    for i in range(NT):
        for k in range(1, DMAX+1):
            c_ik = cnt[i].get(k, 0)
            cols = [j for j in range(NT) if deg[j] == k]
            cons.append(cp.sum(E[i, cols]) == c_ik * pi[i])
    prob = cp.Problem(cp.Minimize(m2c @ pi), cons)
    prob.solve(solver=cp.SCS, eps=1e-7, max_iters=40000)
    return prob.value

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
            for k in range(1, 5):
                arms = [a2 if i % k == 0 else a1 for i in range(40)]
                if max(arms)+2 > DMAX: continue
                n, e = spine(40, arms, 2); m1, m2 = m12(n, e)
                if abs(m1-M1) < 0.0025 and m2 < best: best = m2
    return best if best < 9 else None

for DMAX in (4, 5):
    print(f"\n=== DMAX={DMAX} ===  (1-ball vs PSD-lift vs best real tree)")
    for M1 in [0.52, 0.53]:
        ob = oneball(DMAX, M1); ps = psd_lift(DMAX, M1); br = best_real(DMAX, M1)
        brs = f"{br:.5f}" if br else "  --  "
        print(f"  m1={M1:.2f}: 1-ball={ob:.5f}  PSD-lift={ps:.5f}  best-real={brs}   PSD tightening=+{ps-ob:.5f}")
