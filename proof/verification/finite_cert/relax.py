"""Size-priced relaxation test: B(n,k) = min_{t,lam} [log t+1/t-1 + (k-1) What(mu,lam) + Whatna(mu,lam) + lam*(n-1)],
What(mu,lam) = max_{s<=S} max_frontier (bell - lam*s + mu*y) (true frontiers, cap k-1)."""
import sys, math, pickle
import numpy as np
from rootb import PHI
S=int(sys.argv[1]); Nmax=int(sys.argv[2])
H=60; grid=np.linspace(0.5/H,0.5,H); lams=np.linspace(-0.004,0.03,69)
worst={}
for k in range(2,min(Nmax,24)):
    FA,FN=pickle.load(open(f"fr_{S}_{k-1}.pkl","rb"))
    Wa=np.full((len(lams),H),-np.inf); Wn=np.full((len(lams),H),-np.inf)
    for s in range(1,S+1):
        l,y=FA[s]; v=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0)
        Wa=np.maximum(Wa,v[None,:]-lams[:,None]*s)
        if s in FN:
            l,y=FN[s]; v=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0); Wn=np.maximum(Wn,v[None,:]-lams[:,None]*s)
    t=1/(k*grid)
    base=np.log(t)+1/t-1+(k-1)*Wa+Wn    # (lam,H)
    for n in range(k+1,Nmax+1):
        b=np.min(base+lams[:,None]*(n-1))
        m=PHI[n]-b
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
bad=sorted((n,round(m,5),k) for n,(m,k) in worst.items() if m<=0)
print("failures:",bad[:40],"count",len(bad),"of",len(worst))
