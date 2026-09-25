"""Witness-closure of grid points for the Bellman certificate, and certificate-size estimate."""
import sys, math, pickle
import numpy as np
from rootb import PHI
from rootbell2 import knapH
F=math.log(621/64)/11; NEG=-1e30
S=490; H=100; Nmax=491
grid=np.linspace(0.5/H,0.5,H)
thr={2:28,3:70,4:104,5:298}
CAPS=[1,2,3,4,5,6,7,8,12,16,22]
def bellman_w(S,C,grid):
    Hh=len(grid); mu=np.asarray(grid)
    Wa=np.full((S+1,Hh),NEG); Wn=np.full((S+1,Hh),NEG); Wa[1]=-F+mu
    K=[None]+[np.full((S+1,Hh),NEG) for _ in range(C)]; Kx=[None]+[np.full((S+1,Hh),NEG) for _ in range(C)]
    wit={}   # (s,c) -> argmin h per g  (array len H) for all/na
    m_=mu[:,None]; nu=mu[None,:]; disc=1-4*m_*nu
    u=np.where(disc>=0,(1+np.sqrt(np.maximum(disc,0)))/(2*nu),np.nan)
    for s in range(2,S+1):
        N=s-1
        K[1][N]=Wa[N]; Kx[1][N]=Wa[N] if N!=2 else NEG
        for c in range(2,C+1):
            if N<c: break
            m=np.arange(1,N-c+2); prev=K[c-1][N-m]; prevx=Kx[c-1][N-m]; w=Wa[m]
            K[c][N]=np.max(prev+w,axis=0)
            Kx[c][N]=np.max(np.maximum(prevx+w,np.where((m==2)[:,None],NEG,prev+w)),axis=0)
        va=np.full(Hh,-np.inf); vn=np.full(Hh,-np.inf)
        for c in range(1,min(C,N)+1):
            d=c+1; valid=(disc>=0)&(u>2*m_)
            const=np.where(valid,np.log(u/d)+m_/u-F-nu*(u-d),np.inf)
            tot=np.where(K[c][N][None,:]>NEG/2,const+K[c][N][None,:],np.inf)
            h=np.argmin(tot,axis=1); vc=tot[np.arange(Hh),h]; wit[(s,c,0)]=h
            if c==1: vcn=vc if N>=3 else np.full(Hh,-np.inf); hn=h
            else:
                totn=np.where(Kx[c][N][None,:]>NEG/2,const+Kx[c][N][None,:],np.inf); hn=np.argmin(totn,axis=1); vcn=totn[np.arange(Hh),hn]
            wit[(s,c,1)]=hn
            va=np.maximum(va,vc); vn=np.maximum(vn,vcn)
        Wa[s]=np.where(np.isfinite(va),va,NEG); Wn[s]=np.where(np.isfinite(vn),vn,NEG)
    return Wa,Wn,wit
tabs={C:bellman_w(S,C,grid) for C in CAPS}
unc=bellman_w(90,89,grid)
need={}   # cap -> set of g
rootchecks=0
for k in range(2,Nmax):
    Nk=min(Nmax,90) if k>=24 else min(Nmax,thr.get(k,491))
    if Nk<k+1: continue
    C=89 if k>=24 else min(c for c in CAPS if c>=k-1)
    Wa,Wn,_=unc if k>=24 else tabs[C]
    Bn=knapH(Wa[:Nk],Wn[:Nk],k,Nk-1); t=1/(k*grid); val=np.log(t)+1/t-1+Bn
    gs=set(int(x) for x in np.argmin(val[k:],axis=1))
    need.setdefault(C,set()).update(gs)
    rootchecks+=len(gs)*k*Nk*Nk//2*2
# closure
tot_entries=0; tot_bell=0; tot_knap=0
for C,gs in need.items():
    Wa,Wn,wit=unc if C==89 else tabs[C]
    Sc=Wa.shape[0]-1
    todo=set(gs); done=set()
    while todo:
        g=todo.pop(); done.add(g)
        for (s,c,f),h in wit.items():
            hh=int(h[g])
            if hh not in done: todo.add(hh)
    G=len(done)
    tot_entries+=2*Sc*G; tot_bell+=2*Sc*min(C,Sc)*G
    tot_knap+=2*G*sum(min(C,N)*N for N in range(1,Sc))//1
    print(f"cap {C}: root grid pts {len(gs)}, closure {G} of {H}")
print(f"entries {tot_entries:.3g}, bellman witness checks {tot_bell:.3g}, inner knapsack checks {tot_knap:.3g}, root knapsack checks {rootchecks:.3g}")
