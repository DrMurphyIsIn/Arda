"""Phase 0 GO/NO-GO: does a UNIVERSAL field-dependent LOCAL discharge tau exist?
Per-tree LP always keeps max_v phi_v <= F*. Question: is the required tau on each edge a
CONSISTENT function of that edge's LOCAL data (degrees + the two cavity fields), or globally coupled?
Method: for each edge compute the FEASIBLE tau-interval [xmin,xmax] (freedom s.t. every phi_v<=F*).
Two edges with near-identical local data whose intervals are DISJOINT => no local rule => GLOBAL
coupling => NO-GO. All close pairs overlap => a universal local field-tau exists => GO. exact-ish (float LP).
"""
import math, sys, itertools
sys.path.insert(0, "telperion/src")
import numpy as np
from scipy.optimize import linprog
from telperion.bg_bulk_discharge import bethe_terms, _adj
from telperion.spider_broom import spider_edges
from telperion.transfer_caterpillar import caterpillar_edges
F = math.log(621/64)/11
EXEMPT = 15

def edge_intervals(n, edges):
    """Return list of (local_data, [xmin,xmax]) per edge; local_data=(dv,du,h_vu,h_uv) with dv<=du."""
    Aarg,Barg,deg = bethe_terms(n,edges)
    # cavity fields h[(u,v)] recomputed via bethe_terms internals: get from Barg? need h. recompute:
    from telperion.bg_bulk_discharge import cavity_fields
    h,_ = cavity_fields(n,edges)
    E = [(min(a,b),max(a,b)) for (a,b) in edges]
    idx = {e:i for i,e in enumerate(E)}
    A = {v: math.log(float(Aarg[v])) for v in range(n)}
    Be = {}
    for (a,b) in E:
        Be[(a,b)] = math.log(float(Barg.get((a,b), Barg.get((b,a)))))
    adj=_adj(n,edges)
    # constraint: phi_v <= F for non-exempt v. phi_v = A_v - sum over edges.
    # var x_e in [0,1]. phi_a = A_a - sum_{e:a=min} x_e Be - sum_{e:a=max} (1-x_e) Be
    m=len(E)
    Aub=[]; bub=[]
    for v in range(n):
        if deg[v]>=EXEMPT: continue
        row=[0.0]*m; const=A[v]
        for u in adj[v]:
            e=(min(u,v),max(u,v)); i=idx[e]; be=Be[e]
            if v==e[0]:  # v is min -> share x
                row[i]+= -be   # -x_e*be  => coefficient on x_e is -be
            else:        # v is max -> share (1-x) => -(1-x)be = -be + x be
                const += -be; row[i]+= be
        # phi_v = const + row.x  <= F  => row.x <= F-const
        Aub.append(row); bub.append(F-const)
    Aub=np.array(Aub); bub=np.array(bub)
    out=[]
    for e in E:
        i=idx[e]; a,b=e
        c=np.zeros(m); c[i]=1.0
        rmin=linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0,1)]*m, method="highs")
        rmax=linprog(-c, A_ub=Aub, b_ub=bub, bounds=[(0,1)]*m, method="highs")
        if not (rmin.success and rmax.success): 
            out.append((None,None)); continue
        xmin=rmin.x[i]; xmax=rmax.x[i]
        da,db=deg[a],deg[b]; hvu=float(h[(a,b)]); huv=float(h[(b,a)])
        # local_data oriented so 'x' share belongs to endpoint a (min index) with degree da
        ld=(da,db,round(hvu,4),round(huv,4))
        out.append((ld,(xmin,xmax)))
    return out

POOL = ([("S(%d,%d)"%(k,c),spider_edges(k,c)) for k in (2,3,4,5) for c in (3,4,5,6)]
        + [("cat%s"%str(p),caterpillar_edges(p)) for p in ([5]*8,[7]*8,[4]*10,[6]*8,[3]*12,[5,7,5,7,5,7])])

allint=[]
maxt=-9
for name,(rec) in [(nm,ed) for nm,ed in POOL]:
    n,e = rec
    ivs = edge_intervals(n,e)
    for ld,iv in ivs:
        if ld is None: continue
        allint.append((ld,iv,name))

print(f"F* = {F:.6f};  collected {len(allint)} edge feasible-intervals across {len(POOL)} trees")
# Test: close local data => overlapping intervals?
def close(a,b):
    return (a[0]==b[0] and a[1]==b[1] and abs(a[2]-b[2])<0.02 and abs(a[3]-b[3])<0.02)
def overlap(i,j):
    return not (i[1] < j[0]-1e-9 or j[1] < i[0]-1e-9)
bad=[]; pairs=0
for (i,(ld1,iv1,n1)),(j,(ld2,iv2,n2)) in itertools.combinations(enumerate(allint),2):
    if close(ld1,ld2):
        pairs+=1
        if not overlap(iv1,iv2):
            bad.append((ld1,iv1,n1,ld2,iv2,n2))
print(f"close-local-data pairs: {pairs};  DISJOINT (global-coupling) pairs: {len(bad)}")
if bad:
    print("*** NO-GO evidence: same local data, disjoint feasible tau (global coupling):")
    for ld1,iv1,n1,ld2,iv2,n2 in bad[:8]:
        print(f"   {ld1} {n1} tau in [{iv1[0]:.3f},{iv1[1]:.3f}]  vs  {n2} tau in [{iv2[0]:.3f},{iv2[1]:.3f}]")
else:
    print("=> GO evidence: every near-identical-local-data edge pair has OVERLAPPING feasible tau.")
    print("   A universal local field-dependent tau is consistent with all constraints.")
# also report backbone (hub-hub) intervals width
bb=[(ld,iv,nm) for ld,iv,nm in allint if ld[0]>=3 and ld[1]>=3]
print(f"backbone (both deg>=3) edges: {len(bb)}; sample feasible widths:",
      [f"{iv[1]-iv[0]:.2f}" for _,iv,_ in bb[:8]])
