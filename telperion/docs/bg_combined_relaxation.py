"""Combined relaxation: exact cavity free energy + Stieltjes-realizable messages + FULL mass-transport
(discharge potential P(d,x) on half-edge STATES, not just P(x) as in W15).  Telescopes on trees.
Compare P(x) [W15] vs P(d,x) [full mass transport] at DMAX=5."""
import itertools, math
import numpy as np
from scipy.optimize import linprog
LOG_RHO=math.log(1.2276458); DMAX=5; QUANT=0.02
def realizable(depth=10):
    allowed={1:{0.0}}
    for d in range(2,DMAX+1): allowed[d]={(d-1)/(d*1.0)}
    for _ in range(depth):
        nxt={1:{0.0}}
        for d in range(2,DMAX+1):
            ch=[1.0/(d*dc*(1.0+xc)) for dc in range(1,DMAX+1) for xc in allowed[dc]]
            lo,hi=min(ch),max(ch)
            nxt[d]={round((d-1)*lo/QUANT)*QUANT,round((d-1)*hi/QUANT)*QUANT,round((d-1)*(lo+hi)/2/QUANT)*QUANT}
        allowed=nxt
    return {d:sorted(v) for d,v in allowed.items()}
MSG=realizable()
# states for P: (d, x) with d in 1..DMAX, x in MSG[d]  (sender degree + message)
states=[(d,x) for d in range(1,DMAX+1) for x in MSG[d]]
sidx={s:i for i,s in enumerate(states)}; NS=len(states)
# message grid for interpolating outgoing messages onto states-of-a-given-degree
def Prow_state(d,x,mode):
    """row over state-vars for P(d,x); mode 'msg'=P depends on x only, 'state'=P on (d,x). Interp over MSG[d]."""
    r=np.zeros(NS)
    grid=MSG[d]; x=min(max(x,grid[0]),grid[-1])
    j=min(max(np.searchsorted(grid,x)-1,0),len(grid)-2)
    t=(x-grid[j])/(grid[j+1]-grid[j]) if grid[j+1]>grid[j] else 0.0
    if mode=='state':
        r[sidx[(d,grid[j])]]+=1-t; r[sidx[(d,grid[j+1])]]+=t
    else:  # msg: collapse degree -> use degree-1 rep as canonical (P(x) only): sum a shared var; approximate by d=1..put on min-degree
        # emulate P(x): tie all (d,x') with same x'; use a separate small grid
        pass
    return r
def solve(mode):
    if mode=='msg':
        allx=sorted(set(x for d in MSG for x in MSG[d])); NP=len(allx); pidx={x:i for i,x in enumerate(allx)}
        def prow(d,x):
            r=np.zeros(NP); x=min(max(x,allx[0]),allx[-1]); j=min(max(np.searchsorted(allx,x)-1,0),NP-2)
            t=(x-allx[j])/(allx[j+1]-allx[j]) if allx[j+1]>allx[j] else 0.0
            r[j]+=1-t; r[j+1]+=t; return r
        NV=NP+2; gauge=pidx[0.0]
    else:
        NP=NS; prow=lambda d,x: Prow_state(d,x,'state'); NV=NS+2; gauge=sidx[(1,0.0)]
    BI,BETA=NP,NP+1; A=[]; b=[]; nc=0
    nbt=[(da,xa) for da in range(1,DMAX+1) for xa in MSG[da]]
    for d in range(1,DMAX+1):
        for combo in itertools.combinations_with_replacement(nbt,d):
            nb=list(combo)
            if all(da==1 for (da,_) in nb): continue
            q=[1.0/(1.0+x) for (_,x) in nb]; Av=1.0+sum(q[i]/(d*nb[i][0]) for i in range(d))
            pv=math.log(Av); disc=np.zeros(NP)
            for i in range(d):
                da,xa=nb[i]; xo=sum(q[c]/(d*nb[c][0]) for c in range(d) if c!=i)
                Bv=1.0+q[i]*(1.0/(1.0+xo))/(d*da); pv-=0.5*math.log(Bv)
                disc+= prow(da,xa) - prow(d,xo)   # +P(sender=da,xa) - P(sender=d,xo)
            row=np.zeros(NV); row[:NP]=-disc; row[BI]=-1.0; row[BETA]=-d; A.append(row); b.append(-pv); nc+=1
    Aeq=np.zeros((1,NV)); Aeq[0,gauge]=1.0; c=np.zeros(NV); c[BI]=1.0; c[BETA]=2.0
    r=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=Aeq,b_eq=[0.0],bounds=[(-30,30)]*NP+[(-5,5),(-5,5)],method='highs')
    dens=r.x[BI]+2*r.x[BETA] if r.success else None
    print(f"  P({'x only, W15' if mode=='msg' else 'd,x  full mass-transport'}): {nc} configs -> bound={dens:.6f}  gap={dens-LOG_RHO:+.6f}")
    return dens
print(f"DMAX={DMAX}, log rho*={LOG_RHO:.6f}")
solve('msg')
solve('state')
