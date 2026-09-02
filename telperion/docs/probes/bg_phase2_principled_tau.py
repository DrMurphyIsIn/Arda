import math, sys
sys.path.insert(0,"telperion/src")
from fractions import Fraction as Fr
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
from telperion.transfer_caterpillar import caterpillar_edges
F=math.log(621/64)/11; EXEMPT=15
def build(n,e):
    Aarg,Barg,deg=bethe_terms(n,e); h,_=cavity_fields(n,e); adj=_adj(n,e)
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    # p_{v,u} = (h_{u->v}/(d_u d_v)) / Aarg[v]   (fractional field contribution, in (0,1))
    p={}
    for v in range(n):
        for u in adj[v]:
            p[(v,u)]=float(h[(u,v)])/(deg[u]*deg[v])/float(Aarg[v])
    B={}
    for a,b in e:
        ee=(min(a,b),max(a,b)); B[ee]=math.log(float(Barg.get((a,b),Barg.get((b,a)))))
    return A,B,deg,adj,p,n
def maxphi(tree,tau):  # tau(v,u,ctx)->share for v
    A,B,deg,adj,p,n=tree; best=-9
    for v in range(n):
        if deg[v]>=EXEMPT: continue
        s=0.
        for u in adj[v]:
            ee=(min(u,v),max(u,v))
            s+=tau(v,u,tree)*B[ee]
        best=max(best,A[v]-s)
    return best
# candidate tau rules (v's share of edge (v,u)); must satisfy tau(v,u)+tau(u,v)=1
def t_marg(v,u,tr):   # marginal-occupation split
    _,_,_,_,p,_=tr; pv,pu=p[(v,u)],p[(u,v)]; return pv/(pv+pu)
def t_deg(v,u,tr):    # degree split (baseline, known +0.0033)
    _,_,deg,_,_,_=tr; return deg[u]/(deg[u]+deg[v])
def t_degv(v,u,tr):
    _,_,deg,_,_,_=tr; return deg[v]/(deg[u]+deg[v])
def t_margsq(v,u,tr):
    _,_,_,_,p,_=tr; pv,pu=p[(v,u)],p[(u,v)]; return pv*pv/(pv*pv+pu*pu)
def t_half(v,u,tr): return 0.5
POOL=[("S(%d,%d)"%(k,c),spider_edges(k,c)) for k in (2,3,4,5,6,8) for c in (3,4,5,6,7,8)]
POOL+=[("cat"+str(p),caterpillar_edges(p)) for p in ([6]*10,[6,8,4]*3,[7,5,3]*3,[4,6,8]*3,[9]*6,[5,9,3]*3,[8,4,6,5]*2,[3,5,7]*3)]
trees=[(nm,build(n,e)) for nm,(n,e) in POOL]
print(f"F* = {F:.6f}\n")
for name,tau in [("half",t_half),("deg u/(u+v)",t_deg),("deg v/(u+v)",t_degv),
                 ("MARGINAL p/(p+p)",t_marg),("marginal^2",t_margsq)]:
    gaps=[(nm,maxphi(tr,tau)-F) for nm,tr in trees]
    worst=max(g for _,g in gaps); wn=[nm for nm,g in gaps if g==worst][0]
    ok=sum(1 for _,g in gaps if g<=1e-9)
    print(f"{name:20s}  worst max-phi-F* = {worst:+.6f} @ {wn:16s}  ({ok}/{len(gaps)} <= F*)")
print("\n(marginal split is the principled Bethe-dual candidate; goal: worst <= 0)")
