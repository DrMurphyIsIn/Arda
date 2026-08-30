"""Is the k=1 (single-root) reflection-positivity moment matrix M[j,k]=E_v[cnt_v(j)cnt_v(k)] a BITING
constraint on the type distribution pi, or vacuous (auto-PSD for any pi)?
M[j,k] = sum_t pi(t) cnt_t(j) cnt_t(k) = covariance of features phi_j(v)=cnt_v(j) -> always PSD.
Confirm: adding M>>0 to the flag-LP does not change min m2 (constraint is vacuous)."""
import sys, itertools
import numpy as np, cvxpy as cp
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0,'telperion/src')
DMAX=5; M1=0.52
types=[(d,c) for d in range(1,DMAX+1) for c in itertools.combinations_with_replacement(range(1,DMAX+1),d)]
NT=len(types); deg=[d for d,_ in types]
cnt=np.zeros((NT,DMAX+1))
for i,(d,c) in enumerate(types):
    for e in c: cnt[i,e]+=1
def mm(d,c):
    S=sum(F(1,e) for e in c);Q=sum(F(1,e*e) for e in c);x=S/d;return float(x),float(2*x*x-Q/(d*d))
xv=np.array([mm(d,c)[0] for d,c in types]);m2c=np.array([mm(d,c)[1] for d,c in types])
# 1-ball LP min
rows=[np.ones(NT),np.array(deg,float)];rhs=[1.0,2.0]
for d in range(1,DMAX+1):
    for e in range(d+1,DMAX+1):
        row=np.zeros(NT)
        for i,(dd,c) in enumerate(types):
            if dd==d:row[i]+=sum(1 for z in c if z==e)
            if dd==e:row[i]-=sum(1 for z in c if z==d)
        rows.append(row);rhs.append(0.0)
ob=linprog(m2c,A_eq=np.vstack([np.array(rows),xv]),b_eq=np.append(np.array(rhs),M1),bounds=[(0,None)]*NT,method='highs').fun
# add k=1 moment matrix PSD: M[j,k]=sum_i pi[i] cnt[i,j] cnt[i,k], j,k in 1..DMAX
pi=cp.Variable(NT,nonneg=True)
cons=[cp.sum(pi)==1, pi@np.array(deg,float)==2, pi@xv==M1]
for d in range(1,DMAX+1):
    for e in range(d+1,DMAX+1):
        cons.append(pi@np.array([cnt[i,d] for i in range(NT)])==pi@np.array([cnt[i,e] for i in range(NT)])*0 + sum(cnt[i,d]*0 for i in range(NT))) if False else None
# mass transport
for d in range(1,DMAX+1):
    for e in range(d+1,DMAX+1):
        cons.append(cp.sum(cp.multiply(pi,np.array([cnt[i,e] if deg[i]==d else 0 for i in range(NT)])))
                    ==cp.sum(cp.multiply(pi,np.array([cnt[i,d] if deg[i]==e else 0 for i in range(NT)]))))
M=cp.vstack([cp.hstack([cp.sum(cp.multiply(pi,cnt[:,j]*cnt[:,k])) for k in range(1,DMAX+1)]) for j in range(1,DMAX+1)])
cons.append(M>>0)
val=cp.Problem(cp.Minimize(m2c@pi),cons).solve(solver=cp.CLARABEL)
print(f"1-ball LP min m2         = {ob:.5f}")
print(f"+ k=1 moment matrix PSD  = {val:.5f}   tightening = +{val-ob:.5f}")
print("=> k=1 moment matrix is", "VACUOUS (auto-PSD, no tightening)" if abs(val-ob)<1e-4 else "BITING")
