import math, sys
sys.path.insert(0,"telperion/src")
import numpy as np
from scipy.optimize import linprog
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
from telperion.transfer_caterpillar import caterpillar_edges
F=math.log(621/64)/11; EXEMPT=15
def pertree_minmaxphi(n,e):
    # variables: tau_e per edge (min-index oriented) + t ; min t s.t. phi_v<=t, 0<=tau<=1
    Aarg,Barg,deg=bethe_terms(n,e); 
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    E=[(min(a,b),max(a,b)) for a,b in e]; idx={ee:i for i,ee in enumerate(E)}
    Be={ee:math.log(float(Barg.get((ee[0],ee[1]),Barg.get((ee[1],ee[0]))))) for ee in E}
    adj=_adj(n,e); NV=len(E)+1; tv=NV-1
    Aub=[];bub=[]
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
    return res.x[tv]
POOL=[("S(%d,%d)"%(k,c),spider_edges(k,c)) for k in (2,3,4,5,6,8) for c in (3,4,5,6,7,8)]
POOL+=[("cat"+str(p),caterpillar_edges(p)) for p in ([6]*10,[6,8,4]*3,[7,5,3]*3,[4,6,8]*3,[3,5,7]*3,[8,4,6,5]*2,[9]*6,[5,9,3]*3)]
print(f"F* = {F:.6f}")
print("PER-TREE field-adaptive tau (the plan's 'always works' claim) -- min max-phi:")
worst=-9
for nm,(n,e) in POOL:
    mp=pertree_minmaxphi(n,e); worst=max(worst,mp-F)
    flag="OK <=F*" if mp<=F+1e-7 else f"INFEASIBLE +{mp-F:.6f}"
    print(f"  {nm:16s} {mp:.6f}  {flag}")
print(f"\nworst per-tree gap over F* = {worst:+.6e}")
print("=> "+("PER-TREE FEASIBILITY CONFIRMED: every tree has a field-adaptive tau with phi<=F*."
       if worst<=1e-7 else "PER-TREE INFEASIBLE on some tree: the wall is feasibility itself, not universality."))
