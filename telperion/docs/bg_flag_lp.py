"""Degree-distribution flag-LP for the m_2 cut.

Vertex type t = (d; multiset {e_1..e_d} of neighbour degrees). Empirical type distribution pi(t).
Both moments are LINEAR in pi:
    m_1 = sum_t pi(t) x(t),   x(t) = (sum_i 1/e_i)/d
    m_2 = sum_t pi(t) (2 x(t)^2 - q(t)),  q(t) = (sum_i 1/e_i^2)/d^2   [per-vertex local, exact]
Realizability constraints a REAL TREE must satisfy (the piece W6/W7 lacked):
    (norm) sum pi = 1
    (tree) sum pi(t) d(t) = 2                     [handshake / mean degree 2, bulk]
    (mass transport / unimodularity) for all deg pairs d<e:
        sum_t pi(t) [ cnt_e(t)*1{deg=d} - cnt_d(t)*1{deg=e} ] = 0
        (number of (d,e) edges counted from each endpoint is equal)
Objective: MIN m_2 s.t. m_1 = M1 (scan near 0.52). If min == caterpillar boundary, the cut is proved
(and the LP multipliers are the certificate). Compare to the loose W6 discharging floor.
"""
import sys, itertools
import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')

DMAX = 7   # a=5 caterpillar: hub deg 7, arm-mid 2, leaf 1 -> fits

# enumerate types
types = []   # (d, tuple(sorted neighbor degs))
for d in range(1, DMAX+1):
    for combo in itertools.combinations_with_replacement(range(1, DMAX+1), d):
        types.append((d, combo))
NT = len(types)

def x_of(t):
    d, ne = t; return sum(1.0/e for e in ne)/d
def q_of(t):
    d, ne = t; return sum(1.0/e**2 for e in ne)/d**2
def cnt(t, deg):
    return sum(1 for e in t[1] if e == deg)

xv = np.array([x_of(t) for t in types])
m2c = np.array([2*x_of(t)**2 - q_of(t) for t in types])
dv = np.array([t[0] for t in types], float)

# equality constraints
rows = []; rhs = []
rows.append(np.ones(NT)); rhs.append(1.0)          # normalization
rows.append(dv.copy()); rhs.append(2.0)            # mean degree 2 (tree handshake)
# mass transport for each pair d<e
for d in range(1, DMAX+1):
    for e in range(d+1, DMAX+1):
        row = np.zeros(NT)
        for i, t in enumerate(types):
            if t[0] == d: row[i] += cnt(t, e)
            if t[0] == e: row[i] -= cnt(t, d)
        rows.append(row); rhs.append(0.0)
A_eq_base = np.array(rows); b_eq_base = np.array(rhs)

# caterpillar a=5 reference (exact): m1=0.5234, m2=0.3218
def caterpillar_legs(sp, a, L):
    e=[];nid=sp
    for i in range(sp-1):e.append((i,i+1))
    for i in range(sp):
        for _ in range(a):
            p=i
            for _ in range(L):e.append((p,nid));p=nid;nid+=1
    return nid,e
def m12_exact(n,e):
    d=[0]*n;adj=[[] for _ in range(n)]
    for a,b in e:d[a]+=1;d[b]+=1;adj[a].append(b);adj[b].append(a)
    m1=F(0);m2=F(0)
    for v in range(n):
        dvv=d[v];S=sum(F(1,d[a]) for a in adj[v]);Q=sum(F(1,d[a]**2) for a in adj[v])
        m1+=S/dvv;m2+=2*S*S/(dvv*dvv)-Q/(dvv*dvv)
    return float(m1/n),float(m2/n)
cm1,cm2 = m12_exact(*caterpillar_legs(50,5,2))
print(f"types={NT} (DMAX={DMAX}). caterpillar a=5: m1={cm1:.5f} m2={cm2:.5f}")
print("\n  M1  | min m2 (flag-LP w/ mass-transport) | caterpillar m2 | W6-loose-floor 0.231")
for M1 in [0.50, 0.51, 0.5234, 0.53, 0.54]:
    A_eq = np.vstack([A_eq_base, xv]); b_eq = np.append(b_eq_base, M1)
    res = linprog(m2c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)]*NT, method='highs')
    if res.success:
        tag = " <-- caterpillar m1" if abs(M1-cm1) < 1e-3 else ""
        print(f"  {M1:.4f} |   min m2 = {res.fun:.5f}                  |   {cm2 if abs(M1-cm1)<1e-3 else '-':>7}       {tag}")
    else:
        print(f"  {M1:.4f} |   INFEASIBLE ({res.message[:40]})")


print("\n=== extract LP dual = the certificate, verify per-type inequality ===")
M1 = cm1
A_eq = np.vstack([A_eq_base, xv]); b_eq = np.append(b_eq_base, M1)
res = linprog(m2c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)]*NT, method='highs')
y = res.eqlin.marginals              # dual for each equality row
# rows: [0]=norm, [1]=mean-deg, [2..]=mass-transport pairs (d<e), [last]=m1
y_norm = y[0]; y_deg = y[1]; y_m1 = y[-1]
pair_list = [(d, e) for d in range(1, DMAX+1) for e in range(d+1, DMAX+1)]
y_pair = {pair_list[k]: y[2+k] for k in range(len(pair_list))}
def wfun(d, e):  # antisymmetric discharging potential from mass-transport duals
    if d == e: return 0.0
    return y_pair[(d, e)] if d < e else -y_pair[(e, d)]
# certificate: for every type t,  m2c(t) >= y_norm + y_deg*d + y_m1*x(t) + sum_{a} w(d, e_a)
worst = 9e9
for t in types:
    d, ne = t
    bound = y_norm + y_deg*d + y_m1*x_of(t) + sum(wfun(d, e) for e in ne)
    slack = m2c[types.index(t)] - bound
    worst = min(worst, slack)
lp_val = res.fun
cert_val = y_norm + 2*y_deg + M1*y_m1
print(f"LP min m2 = {lp_val:.6f}  dual b.y = {cert_val:.6f}  (should match)")
print(f"certificate per-type inequality worst slack = {worst:.2e}  ({'VALID (>=0)' if worst > -1e-6 else 'VIOLATED'})")
print(f"=> proven lower bound  m2 >= {cert_val:.5f}  at m1={M1:.5f};  caterpillar m2={cm2:.5f}  gap={cm2-cert_val:+.5f}")
print(f"   antisymmetric discharging potential w(d,e) from mass-transport duals, e.g. w(1,2)={wfun(1,2):.5f} w(2,7)={wfun(2,7):.5f} w(2,3)={wfun(2,3):.5f}")
