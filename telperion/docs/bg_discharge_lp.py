"""Corrected K=2 discharging LP over BULK-realizable profiles.

min B  s.t.  for every realizable local profile (D; multiset {y_1..y_D}, y_i>=1):
    g(D;{y}) - sum_i w(D,y_i) <= B,     w(x,y) = -w(y,x)  antisymmetric.
Exclude 'all-leaf' neighborhoods (D,{1,1,...,1}) = star-centers, realizable only in the finite
star K_{1,D} (a surface/finite object), never in the bulk of a large tree.
If min B == log rho*, the 1-neighbourhood K=2 discharging certificate closes the density bound.
"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog
LOG_RHO = 0.2050983
C1, C2 = 0.5, -0.15343
DMAX = 8

pairs = [(x, y) for x in range(1, DMAX+1) for y in range(x+1, DMAX+1)]
pidx = {p: i for i, p in enumerate(pairs)}
NP = len(pairs); B_IDX = NP

def g_profile(D, ys):
    S = sum(1.0/y for y in ys); Q = sum(1.0/y**2 for y in ys)
    return C1*S/D + C2*(2*S*S/D/D - Q/D/D)

def wsign(D, y):  # coefficient of the pair-variable in w(D,y)
    if D == y: return 0.0, None
    p = (min(D, y), max(D, y)); s = 1.0 if D < y else -1.0
    return s, pidx[p]

def constraint_row(D, ys):
    # encode  g - sum w(D,y) <= B   as   (-sum w) - B <= -g
    row = np.zeros(NP+1)
    for y in ys:
        s, i = wsign(D, y)
        if i is not None: row[i] += -s
    row[B_IDX] = -1.0
    return row, -g_profile(D, ys)

def realizable(D, ys):
    # exclude all-ones neighborhoods (star-center K_{1,D}); everything else is bulk-realizable
    return not all(y == 1 for y in ys)

def worst_profile(D, wvals):
    best = -9.0; bestys = None
    for combo in itertools.combinations_with_replacement(range(1, DMAX+1), D):
        ys = list(combo)
        if not realizable(D, ys): continue
        val = g_profile(D, ys)
        for y in ys:
            s, i = wsign(D, y)
            if i is not None: val -= s*wvals[i]
        if val > best: best = val; bestys = ys
    return best, bestys

# seed: uniform non-leaf neighborhoods
A = []; b = []
def add(D, ys):
    row, rhs = constraint_row(D, ys); A.append(row); b.append(rhs)
for D in range(1, DMAX+1):
    for y in range(2, DMAX+1):
        add(D, [y]*D)
# also caterpillar profiles (a in 5..8): spine (a+2,{a+2,a+2, 2*a}), arm-mid (2,{a+2,1}), leaf (1,{2})
for a in range(3, DMAX-1):
    add(a+2, [a+2, a+2] + [2]*a)
    add(2, [a+2, 1])
    add(1, [2])

c = np.zeros(NP+1); c[B_IDX] = 1.0
bounds = [(-3, 3)]*NP + [(-1, 1)]
lastB = None
for it in range(80):
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method='highs')
    if not res.success:
        print("LP failed:", res.message); break
    wv = res.x[:NP]; B = res.x[B_IDX]
    worst = -9.0; wc = None
    for D in range(1, DMAX+1):
        v, ys = worst_profile(D, wv)
        if v > worst: worst = v; wc = (D, ys)
    viol = worst - B
    if it % 8 == 0 or viol <= 1e-7:
        print(f"iter {it:2d}: B={B:.6f} worst={worst:.6f} viol={viol:.2e} (logrho*={LOG_RHO:.6f}) worstprof={wc}")
    if viol <= 1e-7:
        print(f"\nCONVERGED min per-vertex bound B={B:.6f}  vs log rho*={LOG_RHO:.6f}")
        gap = B - LOG_RHO
        print(f"  gap B - log rho* = {gap:+.6f}  => K=2 local certificate {'CLOSES' if abs(gap)<1e-4 else 'does NOT close (needs higher K / 2-nbhd)'}")
        break
    add(*wc)
