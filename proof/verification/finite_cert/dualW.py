"""Test: per-size envelope replaced by its size-dual  W_s(mu) <= min_lam [What(mu,lam) + lam*s]  for s > S1,
exact W_s for s <= S1; root keeps the exact size knapsack."""
import sys, math, pickle
import numpy as np
from rootb import PHI
from rootbell2 import knapH
S=int(sys.argv[1]); Nmax=int(sys.argv[2]); S1=int(sys.argv[3])
H=60; grid=np.linspace(0.5/H,0.5,H); lams=np.linspace(-0.004,0.05,109)
worst={}
for k in range(2,min(Nmax,24)):
    FA,FN=pickle.load(open(f"fr_{S}_{k-1}.pkl","rb"))
    WA=np.full((S+1,H),-1e30); WN=np.full((S+1,H),-1e30)
    for s in range(1,S+1):
        l,y=FA[s]; WA[s]=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0)
        if s in FN: l,y=FN[s]; WN[s]=np.max(l[:,None]+grid[None,:]*y[:,None],axis=0)
    sz=np.arange(S+1)
    Wh=np.max(WA[1:,None,:]-lams[None,:,None]*sz[1:,None,None],axis=0)   # (lam,H)
    Whn=np.max(WN[1:,None,:]-lams[None,:,None]*sz[1:,None,None],axis=0)
    DA=np.min(Wh[None,:,:]+lams[None,:,None]*sz[:,None,None],axis=1)   # (S+1,H)
    DN=np.min(Whn[None,:,:]+lams[None,:,None]*sz[:,None,None],axis=1)
    Wa=WA.copy(); Wn=WN.copy(); Wa[S1+1:]=DA[S1+1:]; Wn[S1+1:]=DN[S1+1:]
    Bn=knapH(Wa,Wn,k,Nmax-1); t=1/(k*grid); best=np.min(np.log(t)+1/t-1+Bn,axis=1)
    for n in range(k+1,Nmax+1):
        m=PHI[n]-best[n-1]
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
bad=sorted((n,round(m,5),k) for n,(m,k) in worst.items() if m<=0)
print("S1",S1,"failures:",bad[:30],"count",len(bad))
