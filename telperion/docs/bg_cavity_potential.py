"""Cavity-potential bound: does a discharge potential P(x) on cavity messages prove F(T) <= log rho*?

Per-vertex free energy (edges split 1/2 to each end):  pv(v) = log A_v - (1/2) sum_a log B_{va},
  A_v = 1 + sum_a q_a/(d*d_a),  q_a = 1/(1+x_a),  x_a = incoming message from neighbour a (degree d_a),
  x_{v->a} = sum_{c != a} q_c/(d*d_c)  (outgoing),  B_{va} = 1 + q_a q_{v->a}/(d*d_a).
Discharge telescopes on trees:  sum_v sum_a [P(x_a) - P(x_{v->a})] = 0.
Certificate: exists P and bound B with   pv(v) - sum_a [P(x_a) - P(x_{v->a})] <= B   for every local config
(degree d, neighbours (d_a, x_a)).  If min B == log rho*, the cavity potential proves the density bound
(tight at the caterpillar) -- the exact route, in message space, NOT moments.

Config space: degrees 1..DMAX, messages on a grid; P piecewise-linear on the grid (linear interpolation ->
constraints linear in P's grid values).  Cutting-plane over configs.
"""
import sys, itertools, math
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')
LOG_RHO = math.log(1.2276458)

DMAX = 4
GRID = np.linspace(0.0, 1.0, 11)      # message grid for P (piecewise linear)
NG = len(GRID)

def interp_row(x):
    """row over grid s.t. row.P = P(x) by linear interpolation; x clamped to [0,1]."""
    x = min(max(x, 0.0), 1.0)
    j = min(int(x*(NG-1)), NG-2)
    t = (x - GRID[j])/(GRID[j+1]-GRID[j])
    r = np.zeros(NG); r[j] = 1-t; r[j+1] = t
    return r

# per-vertex config = (d, tuple of (d_a, x_a)).  message-grid values for neighbours' x_a
MSG = [0.0, 0.1, 0.2, 1.0/3, 0.4, 0.5]   # candidate incoming message values (coarse)

def pv_and_disc(d, nbrs):
    """nbrs = list of (d_a, x_a). Returns (pv, discharge_row over P-grid)."""
    q = [1.0/(1.0+x) for (_, x) in nbrs]
    A = 1.0 + sum(q[i]/(d*nbrs[i][0]) for i in range(d))
    disc = np.zeros(NG)
    pv = math.log(A)
    for i in range(d):
        d_a, x_a = nbrs[i]
        x_out = sum(q[c]/(d*nbrs[c][0]) for c in range(d) if c != i)
        q_out = 1.0/(1.0+x_out)
        B = 1.0 + q[i]*q_out/(d*d_a)
        pv -= 0.5*math.log(B)
        disc += interp_row(x_a) - interp_row(x_out)     # +P(x_a) - P(x_out)
    return pv, disc

# enumerate configs: degree d, multiset of (d_a in 1..DMAX, x_a in MSG)
def configs():
    nb_types = [(da, xa) for da in range(1, DMAX+1) for xa in MSG]
    for d in range(1, DMAX+1):
        for combo in itertools.combinations_with_replacement(nb_types, d):
            yield d, list(combo)

CONF = list(configs())
print(f"DMAX={DMAX}, grid={NG}, {len(CONF)} configs")

# LP: variables [P_0..P_{NG-1}, B, beta]; per-config  pv - disc.P - beta*d <= B
# density bound (handshake sum d = 2n-2):  F(T) <= B + beta*(2 - 2/n) -> B + 2 beta (bulk).  Minimize B+2beta.
NV = NG + 2
BI, BETA = NG, NG+1
A_ub = []; b_ub = []
for d, nbrs in CONF:
    pv, disc = pv_and_disc(d, nbrs)
    row = np.zeros(NV); row[:NG] = -disc; row[BI] = -1.0; row[BETA] = -d   # -disc.P - B - beta*d <= -pv
    A_ub.append(row); b_ub.append(-pv)
A_eq = np.zeros((1, NV)); A_eq[0, 0] = 1.0     # gauge P(0)=0
c = np.zeros(NV); c[BI] = 1.0; c[BETA] = 2.0    # minimize B + 2 beta (bulk density bound)
res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), A_eq=A_eq, b_eq=[0.0],
              bounds=[(-10, 10)]*NG + [(-2, 2), (-2, 2)], method='highs')
if res.success:
    dens = res.x[BI] + 2*res.x[BETA]
    print(f"density bound B+2beta = {dens:.6f}   log rho* = {LOG_RHO:.6f}   gap = {dens-LOG_RHO:+.6f}")
    print(f"  (B={res.x[BI]:.5f}, beta={res.x[BETA]:.5f})")
    print("=> cavity potential (with handshake)", "CLOSES to log rho*" if abs(dens-LOG_RHO) < 2e-3 else "plateaus ABOVE log rho*")
    print(f"   P grid = {np.round(res.x[:NG], 4)}")
else:
    print("LP failed:", res.message)
