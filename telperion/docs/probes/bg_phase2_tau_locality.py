import math, sys, warnings
warnings.filterwarnings("ignore")
sys.path.insert(0,"telperion/src")
import numpy as np, cvxpy as cp
from sklearn.ensemble import GradientBoostingRegressor
from telperion.bg_bulk_discharge import bethe_terms, _adj, cavity_fields
from telperion.spider_broom import spider_edges
from telperion.transfer_caterpillar import caterpillar_edges
F=math.log(621/64)/11; EXEMPT=15
def build(n,e):
    Aarg,Barg,deg=bethe_terms(n,e); h,_=cavity_fields(n,e); adj=_adj(n,e)
    A={v:math.log(float(Aarg[v])) for v in range(n)}
    E=[(min(a,b),max(a,b)) for a,b in e]; idx={ee:i for i,ee in enumerate(E)}
    B={ee:math.log(float(Barg.get((ee[0],ee[1]),Barg.get((ee[1],ee[0]))))) for ee in E}
    return dict(n=n,A=A,B=B,deg=deg,adj=adj,E=E,idx=idx,h=h)
def canon_tau(tr):  # min sum (tau-0.5)^2 s.t. phi_v<=F*, 0<=tau<=1
    E=tr["E"]; m=len(E); tau=cp.Variable(m)
    cons=[tau>=0,tau<=1]
    for v in range(tr["n"]):
        if tr["deg"][v]>=EXEMPT: continue
        expr=tr["A"][v]
        for u in tr["adj"][v]:
            ee=(min(u,v),max(u,v)); i=tr["idx"][ee]; be=tr["B"][ee]
            expr=expr-(tau[i] if v==ee[0] else (1-tau[i]))*be
        cons.append(expr<=F)
    prob=cp.Problem(cp.Minimize(cp.sum_squares(tau-0.5)),cons)
    prob.solve(solver=cp.OSQP,eps_abs=1e-8,eps_rel=1e-8,max_iter=40000)
    if tau.value is None: return None
    return np.clip(tau.value,0,1)
def feats(tr,ee):
    a,b=ee; deg=tr["deg"]; h=tr["h"]; A=tr["A"]; adj=tr["adj"]
    def other(x,y):  # aggregate of x's OTHER incident fields (exclude y)
        vals=[float(h[(w,x)]) for w in adj[x] if w!=y]
        return (max(vals) if vals else 0.0, sum(vals), len(vals))
    oa=other(a,b); ob=other(b,a)
    return [deg[a],deg[b],float(h[(b,a)]),float(h[(a,b)]),A[a],A[b],
            oa[0],oa[1],oa[2],ob[0],ob[1],ob[2]]
POOL=[("S(%d,%d)"%(k,c),spider_edges(k,c)) for k in (2,3,4,5,6,7,8) for c in (3,4,5,6,7,8)]
POOL+=[("cat"+str(p),caterpillar_edges(p)) for p in
       ([6]*10,[6,8,4]*3,[7,5,3]*3,[4,6,8]*3,[9]*6,[5,9,3]*3,[8,4,6,5]*2,[3,5,7]*3,[5]*12,[7]*8,[4,8]*5)]
trees=[(nm,build(n,e)) for nm,(n,e) in POOL]
X=[];Y=[];tid=[]
for ti,(nm,tr) in enumerate(trees):
    tv=canon_tau(tr)
    if tv is None: print("infeasible canon",nm); continue
    for i,ee in enumerate(tr["E"]):
        X.append(feats(tr,ee)); Y.append(float(tv[i])); tid.append(ti)
X=np.array(X);Y=np.array(Y);tid=np.array(tid)
# split by TREE: even index train, odd test
ntr=len(trees); train_t=set(range(0,ntr,2)); test_t=set(range(1,ntr,2))
mtr=np.array([t in train_t for t in tid]); mte=~mtr
gb=GradientBoostingRegressor(n_estimators=400,max_depth=4,learning_rate=0.05)
gb.fit(X[mtr],Y[mtr])
r2=gb.score(X[mte],Y[mte])
print(f"F* = {F:.6f}")
print(f"canonical-tau locality: out-of-sample R^2 (predict tau from local features) = {r2:.4f}")
# apply learned tau, measure out-of-sample max phi on TEST trees
def apply_maxphi(tr):
    best=-9
    tau={}
    for ee in tr["E"]:
        tau[ee]=float(np.clip(gb.predict([feats(tr,ee)])[0],0,1))
    for v in range(tr["n"]):
        if tr["deg"][v]>=EXEMPT: continue
        s=0.
        for u in tr["adj"][v]:
            ee=(min(u,v),max(u,v))
            t=tau[ee] if v==ee[0] else 1-tau[ee]
            s+=t*tr["B"][ee]
        best=max(best,tr["A"][v]-s)
    return best
print("\nApply learned tau to HELD-OUT trees (out-of-sample joint feasibility):")
worst=-9
for ti in sorted(test_t):
    nm,tr=trees[ti]; mp=apply_maxphi(tr); worst=max(worst,mp-F)
    fl="<=F*" if mp<=F+1e-9 else f"ABOVE +{mp-F:.5f}"
    print(f"  {nm:22s} {mp:.6f} {fl}")
print(f"\nworst out-of-sample gap = {worst:+.6f}")
print("=> "+("LOCAL RULE GENERALIZES: a local tau reproduces feasibility out-of-sample (GO to certify)."
       if worst<=1e-6 else "flexible local learner still misses -> tau not a bounded-radius local function (global coupling signal)."))
