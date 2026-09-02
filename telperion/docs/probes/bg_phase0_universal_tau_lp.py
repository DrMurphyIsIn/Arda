import math, sys, collections
sys.path.insert(0,"telperion/src")
import numpy as np
from scipy.optimize import linprog
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
from telperion.transfer_caterpillar import caterpillar_edges
F=math.log(621/64)/11; EXEMPT=15
# tau_{a,b} (a<b) = c[key] . feat, feat=[1,h_ab,h_ba,A_a,A_b], key=(deg[a],deg[b]). tau_{b,a}=1-tau_{a,b}.
# phi_v linear in coeffs. Minimize t s.t. phi_v<=t, 0<=tau_e<=1. LP over all coeffs + t.
NF=5
def feat(hab,hba,Aa,Ab): return [1.0,hab,hba,Aa,Ab]
TRAIN=[("S(%d,%d)"%(k,c),spider_edges(k,c)) for k in (2,3,4,5,7) for c in (3,4,5,6,7,8)]+[("cat",caterpillar_edges(p)) for p in ([5]*8,[7]*8,[4]*10,[6]*8,[3]*12,[8]*6,[4,6,8]*3,[5,7]*5,[3,5,7]*3)]
HELD =[("S(6,5)",spider_edges(6,5)),("S(6,7)",spider_edges(6,7)),("S(3,4)",spider_edges(3,4)),
       ("S(6,8)",spider_edges(6,8)),("cat[6]x10",caterpillar_edges([6]*10)),("cat[6,8,4]x3",caterpillar_edges([6,8,4]*3)),("cat[7,5,3]x3",caterpillar_edges([7,5,3]*3))]
keys={}
def kidx(k):
    if k not in keys: keys[k]=len(keys)
    return keys[k]
# first pass: register keys
data=[]
for nm,(n,e) in TRAIN:
    Aarg,Barg,deg=bethe_terms(n,e); h,_=cavity_fields(n,e)
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    Be={}
    for a,b in e:
        ee=(min(a,b),max(a,b)); Be[ee]=math.log(float(Barg.get((a,b),Barg.get((b,a)))))
    adj=_adj(n,e)
    for a,b in [(min(x,y),max(x,y)) for x,y in e]:
        kidx((deg[a],deg[b]))
    data.append((n,e,A,Be,deg,h,adj))
NK=len(keys); NV=NK*NF+1  # coeffs + t (t is last var)
tvar=NV-1
def coefcol(k): return keys[k]*NF
# build LP
Aub=[]; bub=[]
for (n,e,A,Be,deg,h,adj) in data:
    E=[(min(a,b),max(a,b)) for a,b in e]
    # tau_e as linear form in vars
    tauform={}
    for (a,b) in E:
        k=(deg[a],deg[b]); base=coefcol(k)
        f=feat(float(h[(a,b)]),float(h[(b,a)]),A[a],A[b])
        row=np.zeros(NV)
        for i in range(NF): row[base+i]=f[i]
        tauform[(a,b)]=row  # tau_{a,b} = row.x
        # 0<=tau<=1
        Aub.append(row.copy()); bub.append(1.0)
        Aub.append(-row.copy()); bub.append(0.0)
    for v in range(n):
        if deg[v]>=EXEMPT: continue
        row=np.zeros(NV); const=A[v]
        for u in adj[v]:
            ee=(min(u,v),max(u,v)); be=Be[ee]; tf=tauform[ee]
            if v==ee[0]:  # v is a: -tau*be
                row += -be*tf
            else:         # v is b: -(1-tau)*be = -be + tau*be
                const += -be; row += be*tf
        # phi_v = const + row.x <= t  => row.x - t <= -const
        row[tvar]-=1.0
        Aub.append(row); bub.append(-const)
Aub=np.array(Aub); bub=np.array(bub)
c=np.zeros(NV); c[tvar]=1.0
r=linprog(c,A_ub=Aub,b_ub=bub,bounds=[(None,None)]*NV,method="highs")
print(f"F* = {F:.6f}")
print(f"JOINT LP over {NK} degree-pair affine-tau rules: min max-phi (TRAIN) = {r.x[tvar]:.6f}  "
      f"{'<= F* : a concrete local tau achieves it' if r.x[tvar]<=F+1e-9 else 'ABOVE F* +%.6f'%(r.x[tvar]-F)}")
# apply to held-out
sol=r.x
def apply_maxphi(n,e):
    Aarg,Barg,deg=bethe_terms(n,e); h,_=cavity_fields(n,e)
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    Be={}
    for a,b in e:
        ee=(min(a,b),max(a,b)); Be[ee]=math.log(float(Barg.get((a,b),Barg.get((b,a)))))
    adj=_adj(n,e); best=-9
    for v in range(n):
        if deg[v]>=EXEMPT: continue
        s=0.
        for u in adj[v]:
            ee=(min(u,v),max(u,v))
            k=(deg[ee[0]],deg[ee[1]])
            if k not in keys: 
                t=0.5
            else:
                base=keys[k]*NF; f=feat(float(h[(ee[0],ee[1])]),float(h[(ee[1],ee[0])]),A[ee[0]],A[ee[1]])
                t=sum(sol[base+i]*f[i] for i in range(NF)); t=min(1.,max(0.,t))
            if v!=ee[0]: t=1-t
            s+=t*Be[ee]
        best=max(best,A[v]-s)
    return best
print("OUT-OF-SAMPLE (held-out trees):")
allok=r.x[tvar]<=F+1e-9
for nm,(n,e) in HELD:
    mp=apply_maxphi(n,e); flag="<=F*" if mp<=F+1e-9 else f"ABOVE +{mp-F:.6f}"
    if mp>F+1e-9: allok=False
    print(f"  {nm:16s} max phi = {mp:.6f}  {flag}")
print("\nVERDICT:", "GO (SUFFICIENCY) -- a concrete per-degree affine LOCAL tau achieves max phi<=F* jointly, in+out of sample."
      if allok else "local affine tau insufficient; margin above = the residual to close (Phase 2 richer form / genuine coupling).")
