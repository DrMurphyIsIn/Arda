"""Robustness of the flag-LP m_2 cut as the degree cap DMAX grows.
For each DMAX, min m_2 at the matching caterpillar's m_1 (hub degree = DMAX, a=DMAX-2),
extract+verify the dual certificate, report gap to the caterpillar. If min m_2 stays ~ caterpillar
(does not drop as more high-degree types are admitted), the cut is robust."""
import sys, itertools
import numpy as np
from fractions import Fraction as F
from scipy.optimize import linprog
sys.path.insert(0, 'telperion/src')

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

def run(DMAX, a):
    types=[]
    for d in range(1,DMAX+1):
        for combo in itertools.combinations_with_replacement(range(1,DMAX+1),d):
            types.append((d,combo))
    NT=len(types)
    x_of=lambda t:sum(1.0/e for e in t[1])/t[0]
    q_of=lambda t:sum(1.0/e**2 for e in t[1])/t[0]**2
    xv=np.array([x_of(t) for t in types])
    m2c=np.array([2*x_of(t)**2-q_of(t) for t in types])
    dv=np.array([t[0] for t in types],float)
    rows=[np.ones(NT),dv.copy()];rhs=[1.0,2.0]
    for d in range(1,DMAX+1):
        for e in range(d+1,DMAX+1):
            row=np.zeros(NT)
            for i,t in enumerate(types):
                if t[0]==d:row[i]+=sum(1 for z in t[1] if z==e)
                if t[0]==e:row[i]-=sum(1 for z in t[1] if z==d)
            rows.append(row);rhs.append(0.0)
    cm1,cm2=m12_exact(*caterpillar_legs(50,a,2))
    A_eq=np.vstack([np.array(rows),xv]);b_eq=np.append(np.array(rhs),cm1)
    res=linprog(m2c,A_eq=A_eq,b_eq=b_eq,bounds=[(0,None)]*NT,method='highs')
    return NT,cm1,cm2,res.fun

print(" DMAX | types | caterpillar(m1,m2)   | flag-LP min m2 | gap(cat-LP)")
for DMAX,a in [(7,5),(8,6),(9,7),(10,7)]:
    NT,cm1,cm2,lp=run(DMAX,a)
    print(f"  {DMAX:2d}  | {NT:6d}| ({cm1:.5f},{cm2:.5f}) |   {lp:.5f}      |  {cm2-lp:+.5f}")
