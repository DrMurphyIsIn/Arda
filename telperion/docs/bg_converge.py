"""Does flag-LP min m2 at FIXED m1=0.520 converge as degree cap DMAX grows (=> exact boundary),
or keep dropping (=> relaxation loosening)? Compare to best real tree at m1=0.520."""
import sys, itertools
import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')
def lp_min(DMAX, M1):
    types=[]
    for d in range(1,DMAX+1):
        for c in itertools.combinations_with_replacement(range(1,DMAX+1),d): types.append((d,c))
    NT=len(types)
    xv=np.array([sum(1.0/e for e in t[1])/t[0] for t in types])
    m2c=np.array([2*(sum(1.0/e for e in t[1])/t[0])**2-sum(1.0/e**2 for e in t[1])/t[0]**2 for t in types])
    dvv=np.array([t[0] for t in types],float)
    rows=[np.ones(NT),dvv.copy()];rhs=[1.0,2.0]
    for d in range(1,DMAX+1):
        for e in range(d+1,DMAX+1):
            row=np.zeros(NT)
            for i,t in enumerate(types):
                if t[0]==d:row[i]+=sum(1 for z in t[1] if z==e)
                if t[0]==e:row[i]-=sum(1 for z in t[1] if z==d)
            rows.append(row);rhs.append(0.0)
    r=linprog(m2c,A_eq=np.vstack([np.array(rows),xv]),b_eq=np.append(np.array(rhs),M1),bounds=[(0,None)]*NT,method='highs')
    return NT, (r.fun if r.success else None)
M1=0.5200
print(f"convergence of flag-LP min m2 at fixed m1={M1}:")
for D in (8,9,10,11):
    NT,v=lp_min(D,M1)
    print(f"  DMAX={D:2d} ({NT:6d} types): min m2 = {v:.5f}")
