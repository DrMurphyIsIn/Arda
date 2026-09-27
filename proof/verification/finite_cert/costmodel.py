"""Tightness + exact check-count model of the Bellman envelope certificate for n <= Nmax.
usage: python3 costmodel.py Nmax H CAPS(comma) [grid=uniform|mixed]"""
import sys, math, pickle
import numpy as np
from rootb import PHI
from rootbell2 import knapH
from closure import bellman_w
Nmax=int(sys.argv[1]); H=int(sys.argv[2]); CAPS=[int(x) for x in sys.argv[3].split(",")]
kind=sys.argv[4] if len(sys.argv)>4 else "uniform"
if kind=="uniform": grid=np.linspace(0.5/H,0.5,H)
else:  # mixed: uniform base + extra density on [0.02,0.12]
    grid=np.unique(np.concatenate([np.linspace(0.5/H,0.5,H),np.linspace(0.02,0.12,H//2)]))
H=len(grid)
thr={2:28,3:70,4:104,5:298}
S=Nmax
tabs={C:bellman_w(S,C,grid) for C in CAPS}; unc=bellman_w(90,89,grid)
worst={}; need={}; rootchecks=0; SNEED={}
for k in range(2,Nmax):
    Nk=min(Nmax,90) if k>=24 else min(Nmax,thr.get(k,10**9))
    if Nk<k+1: continue
    C=89 if k>=24 else min(c for c in CAPS if c>=k-1)
    Wa,Wn,_=unc if k>=24 else tabs[C]
    Bn=knapH(Wa[:Nk],Wn[:Nk],k,Nk-1); t=1/(k*grid); val=np.log(t)+1/t-1+Bn; best=np.min(val,axis=1)
    # greedy set of root grid points covering all n for this k
    ns=list(range(max(7,k+1),Nk+1)); left=set(ns); gs=[]
    while left:
        g=max(range(H),key=lambda g: sum(val[n-1,g]<PHI[n] for n in left))
        cov={n for n in left if val[n-1,g]<PHI[n]}
        if not cov: break
        gs.append(g); left-=cov
    for n in range(k+1,Nk+1):
        m=PHI[n]-best[n-1]
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
    need.setdefault(C,set()).update(gs); SNEED[C]=max(SNEED.get(C,0),Nk-k)
    rootchecks+=len(gs)*3*k*sum(min(N,Nk) for N in range(1,Nk))
bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0 and n>=7)
tot_bell=0; tot_knap=0; clos={}
for C,gs in need.items():
    Wa,Wn,wit=unc if C==89 else tabs[C]
    Sc=min(Wa.shape[0]-1,SNEED[C])
    todo=set(gs); done=set()
    while todo:
        g=todo.pop(); done.add(g)
        for (s,c,f),h in wit.items():
            hh=int(h[g])
            if hh not in done: todo.add(hh)
    G=len(done); clos[C]=G
    tot_bell+=2*Sc*min(C,Sc)*G
    tot_knap+=2*G*sum(sum(N-c+1 for c in range(2,min(C,N)+1))+1 for N in range(1,Sc))
print(f"Nmax={Nmax} H={H} {kind} caps={CAPS}: failures(n>=7)={len(bad)} {bad[:6]}  closure={clos}")
print(f"   checks: bellman-witness {tot_bell:.3g}, inner knapsack {tot_knap:.3g}, root {rootchecks:.3g}, TOTAL {tot_bell+tot_knap+rootchecks:.3g}")
