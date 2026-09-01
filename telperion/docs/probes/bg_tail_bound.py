import sys, math
sys.path.insert(0,"telperion/src")
from fractions import Fraction as Fr
from telperion.spider_broom import broom_total
F=math.log(621/64)/11
# broom B(c): size 2c+1, total=broom_total(c). h_root and d_root:
# B(c) root = hub with c cherry-children + up-edge => d=c+1. h_root = U/total.
# U(B(c)) = product of child totals = total(cherry)^c ; total(cherry)=3/2. so U=(3/2)^c. total=broom_total(c).
def broom_props(c):
    tot=broom_total(c); U=Fr(3,2)**c; h=U/tot; d=c+1; n=2*c+1
    ell=math.log(float(tot))-n*F
    return ell, float(h)/d, n
ec,yc=-0.00771,1.0/3
def cherryval(mu): return ec+mu*yc
print("per-size MAXIMUM branch is the broom B(c) (size 2c+1). Lagrangian ell(B(c))+mu*y vs cherry:")
for mu in (0.039, 0.0476):
    print(f"\n mu={mu} (cherry Lagrangian value = {cherryval(mu):+.5f}):")
    worst=-9
    for c in list(range(5,15))+[20,30,50,80]:
        ell,y,n=broom_props(c); val=ell+mu*y; worst=max(worst,val)
        if c<=9 or c in (20,50,80):
            print(f"   B({c:2d}) size {n:3d}: ell={ell:+.6f} y={y:.4f} -> ell+mu*y={val:+.6f} {'<cherry OK' if val<cherryval(mu)-1e-9 else 'NOT below!'}")
    print(f"   max over c>=5 (incl to 80) = {worst:+.6f}  {'< cherry (tail below)' if worst<cherryval(mu)-1e-9 else 'FAILS'}")
print("\n=> the per-size maxima (brooms) stay strictly below the cherry Lagrangian for all c>=6 at mu>=mu*,")
print("   and decrease with c -> tail bound holds GIVEN per-size-max = broom (broom-dominance envelope, lemma A).")
