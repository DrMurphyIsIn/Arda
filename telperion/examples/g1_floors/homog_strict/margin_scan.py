from fractions import Fraction as F

W = F(64,621); GAMMA = W**2 * F(5,3)**11; T = W * F(5,3)**11

# The cert P for each region is (T-GS)-shaped after clearing denominators.
# From bridges: 
#  A: P_A(mu) = T - (7/6+mu/2)^11              [k=1 form, no glemma]   deg 11 in the neg part -> the cert poly given is deg<=11
#  B/C1: P = T*(1+mu/3)^11 - (7/6+mu/2)^11 * GAMMA        (glemma^1)
#  C2: P = T*(1+mu/3)^22 - ((10+6mu)/9)^11 * GAMMA^2
#  C3: P = T*(1+mu/3)^33 - (1+mu)^11 * GAMMA^3
# But note certA's polynomial as stated equals T - (7/6+mu/2)^11 (the bridgeA heq).

def P_A(mu):  return T - (F(7,6)+mu/2)**11
def P_B(mu):  return T*(1+mu/3)**11 - (F(7,6)+mu/2)**11 * GAMMA
def P_C2(mu): return T*(1+mu/3)**22 - ((10+6*mu)/9)**11 * GAMMA**2
def P_C3(mu): return T*(1+mu/3)**33 - (1+mu)**11 * GAMMA**3

regions = [
    ("A  [0,37/120]",    P_A,  F(0),      F(37,120)),
    ("B  [37/120,1/3]",  P_B,  F(37,120), F(1,3)),
    ("C1 [1/3,1/2]",     P_B,  F(1,3),    F(1,2)),
    ("C2 [1/3,1/2]",     P_C2, F(1,3),    F(1,2)),
    ("C3 [1/3,1/2]",     P_C3, F(1,3),    F(1,2)),
]
for name, P, lo, hi in regions:
    # endpoints + min over grid
    plo = P(lo); phi = P(hi)
    mn = None; mnmu=None
    N=600
    for i in range(N+1):
        mu = lo + (hi-lo)*F(i,N)
        v = P(mu)
        if mn is None or v<mn: mn=v; mnmu=mu
    print(f"{name}: P(lo)={float(plo):.6e}  P(hi)={float(phi):.6e}  min={float(mn):.6e} at mu={float(mnmu):.5f}")
