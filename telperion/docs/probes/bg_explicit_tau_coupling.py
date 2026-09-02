import sys, math
sys.path.insert(0,"telperion/src")
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
F=math.log(621/64)/11
n,e=spider_edges(40,5)
Aarg,Barg,deg=bethe_terms(n,e); h,_=cavity_fields(n,e); adj=_adj(n,e)
A={v:math.log(float(Aarg[v])) for v in range(n)}
def Bof(u,v): return math.log(float(Barg.get((min(u,v),max(u,v))) or Barg.get((max(u,v),min(u,v)))))
# explicit rational tau: for each edge, the LOWER-degree endpoint takes the bigger share
# (leaf gets 46/99 of leaf-edge; armmid takes 1 of armmid-center; center takes 1 of center-hub).
# rule: share of endpoint = f(its degree vs neighbor). Implement the "greedy give to lower degree" with k/99.
def share_of(v,u):   # v's share of edge (v,u)
    dv,du=deg[v],deg[u]
    if dv==1: return 46/99         # leaf takes 46/99 (armmid takes 53/99)
    if du==1: return 53/99         # armmid's share of leaf edge
    if dv<du: return 1.0           # lower-degree endpoint takes whole edge
    if dv>du: return 0.0
    return 0.5
mx=-9; argmx=None
for v in range(n):
    if deg[v]>=15: continue
    s=0.
    for u in adj[v]: s+=share_of(v,u)*Bof(v,u)
    phi=A[v]-s
    if phi>mx: mx=phi; argmx=(v,deg[v])
print(f"explicit rational tau on S(40,5): max phi_v = {mx:.6f} at vertex deg {argmx[1]}  (F*={F:.6f})")
print(f"   -> {'<=F* : a MARGIN-LEAVING RATIONAL tau EXISTS (contradicts min-max=F*!?)' if mx<=F+1e-9 else 'ABOVE F* by %.6f (the coupling bites: some vertex forced over)'%(mx-F)}")
# check edge-share consistency: every edge's two shares sum to 1
bad=0
for a,b in e:
    if share_of(a,b)+share_of(b,a)!=1.0 and abs(share_of(a,b)+share_of(b,a)-1.0)>1e-9: bad+=1
print(f"   edge-share consistency (sum to 1): {'OK all edges' if bad==0 else '%d edges violate'%bad}")
