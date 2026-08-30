import itertools, math
import numpy as np
from scipy.optimize import linprog
LOG_RHO=math.log(1.2276458); DMAX=5; QUANT=0.02
# realizable message set per degree (contraction-converged)
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
REAL=realizable()
FREE={d:[0.0,0.15,0.3,0.45,0.6] for d in range(1,DMAX+1)}
FREE[1]=[0.0]
def solve(MSG,label):
    allvals=sorted(set(v for d in MSG for v in MSG[d])); NG=len(allvals)
    def ir(x):
        x=min(max(x,allvals[0]),allvals[-1]); j=min(max(np.searchsorted(allvals,x)-1,0),NG-2)
        t=(x-allvals[j])/(allvals[j+1]-allvals[j]) if allvals[j+1]>allvals[j] else 0.0
        r=np.zeros(NG); r[j]=1-t; r[j+1]=t; return r
    NV=NG+2; BI,BETA=NG,NG+1; A=[]; b=[]; nc=0
    nbt=[(da,xa) for da in range(1,DMAX+1) for xa in MSG[da]]
    for d in range(1,DMAX+1):
        for combo in itertools.combinations_with_replacement(nbt,d):
            nb=list(combo)
            if all(da==1 for (da,_) in nb): continue
            q=[1.0/(1.0+x) for (_,x) in nb]; Av=1.0+sum(q[i]/(d*nb[i][0]) for i in range(d))
            pv=math.log(Av); disc=np.zeros(NG)
            for i in range(d):
                da,xa=nb[i]; xo=sum(q[c]/(d*nb[c][0]) for c in range(d) if c!=i)
                Bv=1.0+q[i]*(1.0/(1.0+xo))/(d*da); pv-=0.5*math.log(Bv); disc+=ir(xa)-ir(xo)
            row=np.zeros(NV); row[:NG]=-disc; row[BI]=-1.0; row[BETA]=-d; A.append(row); b.append(-pv); nc+=1
    Aeq=np.zeros((1,NV)); Aeq[0,allvals.index(0.0)]=1.0; c=np.zeros(NV); c[BI]=1.0; c[BETA]=2.0
    r=linprog(c,A_ub=np.array(A),b_ub=np.array(b),A_eq=Aeq,b_eq=[0.0],bounds=[(-20,20)]*NG+[(-5,5),(-5,5)],method='highs')
    dens=r.x[BI]+2*r.x[BETA] if r.success else None
    print(f"  {label}: {nc} configs -> density bound = {dens:.6f}  gap={dens-LOG_RHO:+.6f}")
    return dens
print(f"DMAX={DMAX}, log rho*={LOG_RHO:.6f}")
print("realizable msgs:", {d:[round(x,3) for x in REAL[d]] for d in REAL})
solve(FREE,"FREE messages   ")
solve(REAL,"REALIZABLE (Stieltjes)")
