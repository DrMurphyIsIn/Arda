"""Exact infinite-caterpillar cavity fixed point + free-energy density F(a), maximised over arm-count a.

Cell = 1 hub (deg a+2) + a arm-mids (deg 2) + a leaves (deg 1); weights w=1/(d_u d_v).
Messages (fixed point): x_leaf->AM=0; x_AM->H=1/2; X:=x_H->H and x_H->AM solve the hub cavity;
x_AM->L closes the arm.  Density F(a) = per-cell Bethe free energy / (2a+1).  Confirm max_a F(a)=log rho*.
"""
import math
from scipy.optimize import brentq, minimize_scalar

LOG_RHO = math.log(1.2276458)


def fixed_point(a):
    wHH = 1.0/(a+2)**2
    wHA = 1.0/(2*(a+2))
    wAL = 0.5
    xAMH = wAL/(1.0+0.0)          # arm-mid -> hub  = 1/2
    # X = x_H->H  solves  X = wHH/(1+X) + (a * wHA)/(1+xAMH)
    c = a*wHA/(1.0+xAMH)
    X = brentq(lambda X: wHH/(1.0+X) + c - X, 0.0, 2.0)
    xHAM = 2*wHH/(1.0+X) + (a-1)*wHA/(1.0+xAMH)   # hub -> arm-mid (excludes 1 arm-mid)
    xAML = wHA/(1.0+xHAM)                          # arm-mid -> leaf
    return dict(wHH=wHH, wHA=wHA, wAL=wAL, X=X, xAMH=xAMH, xHAM=xHAM, xAML=xAML)


def density(a):
    p = fixed_point(a)
    q = lambda x: 1.0/(1.0+x)
    qHH = q(p['X']); qAMH = q(p['xAMH']); qHAM = q(p['xHAM']); qAML = q(p['xAML']); qLAM = 1.0
    A_H = 1.0 + 2*p['wHH']*qHH + a*p['wHA']*qAMH
    A_AM = 1.0 + p['wHA']*qHAM + p['wAL']*qLAM
    A_L = 1.0 + p['wAL']*qAML
    B_HH = 1.0 + p['wHH']*qHH*qHH
    B_HA = 1.0 + p['wHA']*qHAM*qAMH
    B_AL = 1.0 + p['wAL']*qAML*qLAM
    vsum = math.log(A_H) + a*math.log(A_AM) + a*math.log(A_L)
    esum = math.log(B_HH) + a*math.log(B_HA) + a*math.log(B_AL)
    return (vsum - esum)/(2*a+1)


print(" a  |   F(a)     | vs log rho*")
for a in (5, 6, 7, 8, 9, 10):
    print(f" {a:2d} | {density(a):.6f} | {density(a)-LOG_RHO:+.6f}")

res = minimize_scalar(lambda a: -density(a), bounds=(4, 12), method='bounded')
astar = res.x
print(f"\ncontinuous max: a* = {astar:.4f}   F(a*) = {density(astar):.6f}   log rho* = {LOG_RHO:.6f}")
print(f"  => cavity infinite-caterpillar density maximised at a*~{astar:.2f}, equals log rho* to {abs(density(astar)-LOG_RHO):.2e}")
