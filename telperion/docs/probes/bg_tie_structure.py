import sys, math
sys.path.insert(0,"telperion/src")
import numpy as np
from scipy.optimize import linprog
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
F=math.log(621/64)/11; EXEMPT=15
def minmax_phi(n,e):  # LP min over tau of max_v phi_v
    Aarg,Barg,deg=bethe_terms(n,e)
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    E=[(min(a,b),max(a,b)) for a,b in e]; idx={ee:i for i,ee in enumerate(E)}
    Be={ee:math.log(float(Barg.get((ee[0],ee[1]),Barg.get((ee[1],ee[0]))))) for ee in E}
    adj=_adj(n,e); NV=len(E)+1; tv=NV-1; Aub=[];bub=[]
    for i in range(len(E)):
        r=np.zeros(NV);r[i]=1;Aub.append(r.copy());bub.append(1.0)
        r=np.zeros(NV);r[i]=-1;Aub.append(r.copy());bub.append(0.0)
    for v in range(n):
        if deg[v]>=EXEMPT: continue
        r=np.zeros(NV);const=A[v]
        for u in adj[v]:
            ee=(min(u,v),max(u,v));i=idx[ee];be=Be[ee]
            if v==ee[0]: r[i]+=-be
            else: const+=-be; r[i]+=be
        r[tv]-=1;Aub.append(r);bub.append(-const)
    c=np.zeros(NV);c[tv]=1
    res=linprog(c,A_ub=np.array(Aub),b_ub=np.array(bub),bounds=[(None,None)]*NV,method="highs")
    logpi=sum(A[v] for v in range(n))  # = sum phi_v (invariant of tau)
    return res.x[tv], logpi/ (sum(1 for v in range(n)))  # (minmax phi, mean phi = logpi/n)
print(f"F* = {F:.6f}   [minmax = LP-tight max phi over tau ; mean = logpi/n = actual F(T)]")
for k in (5,10,20,40,80):
    mm,mean=minmax_phi(*spider_edges(k,5))
    print(f"  S({k},5): minmax phi = {mm:.6f} (F*-{F-mm:+.2e})   mean phi=F(T) = {mean:.6f} (F*-{F-mean:+.2e})")
print("\nKEY: minmax->F* (LP-tight, no margin-leaving rational tau at the extremal); mean=F(T)<F* strictly")
print("=> the tie is the EXTREMAL FAMILY (min-max=F* only via transcendental tau), not isolated configs.")
