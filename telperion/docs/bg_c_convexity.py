"""Probe (c): can degree-sequence convexity prove m_2 >= phi(m_1) near the extremum band?
Derived crude bound (Cauchy-Schwarz + Jensen):  m_2 >= 2 m_1^2 - m_1.  Test tightness vs caterpillar.
Also fit best m_2 >= a*m_1^2+b*m_1+c and check the gap to the caterpillar boundary near m_1~0.52."""
import sys; sys.path.insert(0,'telperion/src')
from fractions import Fraction as F
import numpy as np, networkx as nx
def dm(n,e):
    d=[0]*n;adj=[[] for _ in range(n)]
    for a,b in e:d[a]+=1;d[b]+=1;adj[a].append(b);adj[b].append(a)
    return d,adj
def m12(n,e):
    d,adj=dm(n,e);m1=F(0);m2=F(0)
    for v in range(n):
        dv=d[v];S=sum(F(1,d[a]) for a in adj[v]);Q=sum(F(1,d[a]**2) for a in adj[v])
        m1+=S/dv;m2+=2*S*S/(dv*dv)-Q/(dv*dv)
    return float(m1/n),float(m2/n)
def cat(sp,a,L):
    e=[];nid=sp
    for i in range(sp-1):e.append((i,i+1))
    for i in range(sp):
        for _ in range(a):
            p=i
            for _ in range(L):e.append((p,nid));p=nid;nid+=1
    return nid,e
# crude bound test over all trees
viol=0;tot=0;minslack=9
for n in range(2,14):
    for T in nx.nonisomorphic_trees(n):
        idx={v:i for i,v in enumerate(T.nodes())};e=[(idx[a],idx[b]) for a,b in T.edges()]
        m1,m2=m12(n,e);slack=m2-(2*m1*m1-m1)
        tot+=1
        if slack<-1e-12:viol+=1
        minslack=min(minslack,slack)
print(f"crude bound m_2 >= 2 m_1^2 - m_1: violations={viol}/{tot}, min slack={minslack:.5f}")
# caterpillar boundary values near m1~0.52 and the crude-bound value there
print("\ncaterpillar boundary vs crude bound vs true m_2:")
for a in [5,7,9]:
    n,e=cat(40,a,2);m1,m2=m12(n,e)
    print(f"  a={a}: m1={m1:.4f} true m2={m2:.4f}  crude 2m1^2-m1={2*m1*m1-m1:.4f}  (crude is {'USELESS' if 2*m1*m1-m1 < m2-0.1 else 'ok'})")
# how much of m_2 is 'variance' (2 avg x^2 - 2 m1^2) that the crude bound throws away?
print("\nvariance content: m_2 = 2*avg(x^2) - avg(Q/d^2); caterpillar avg(x^2) vs m1^2:")
for a in [7]:
    n,e=cat(40,a,2);d,adj=dm(n,e)
    xs=[float(sum(F(1,d[k]) for k in adj[v])/d[v]) for v in range(n)]
    ax2=np.mean(np.array(xs)**2);m1=np.mean(xs)
    print(f"  a={a}: avg(x^2)={ax2:.4f}  m1^2={m1*m1:.4f}  variance avg(x^2)-m1^2={ax2-m1*m1:.4f} (LOST by Jensen)")
