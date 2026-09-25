"""Shared helpers: exact best-spider values PHI[n] = log M(n) - (n-1)F*, per-size envelopes from frontiers, and the
root knapsack (k parts, at least one non-atom).  First run computes M(n), n <= 520, exactly and caches it."""
import sys, math, pickle
import numpy as np
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..'))
import bg_spider_reduction as B
F=B.F
import os
_cache=os.path.join(os.path.dirname(os.path.abspath(__file__)),"spider_cache_520.pkl")
try:
    sp=pickle.load(open(_cache,"rb"))
except Exception:
    sp=B.spider_max(520); pickle.dump(sp,open(_cache,"wb"))
PHI={n:math.log(v[0])-(n-1)*F for n,v in sp.items()}
def env(FR,S,mu):
    W=np.full(S+1,-np.inf)
    for s,(l,y) in FR.items():
        if s<=S: W[s]=np.max(l+mu*y)
    return W
def knap(Wa,Wn,k,N):
    """best sum over compositions of N into k parts (sizes>=1), >=1 part from Wn. returns array over N"""
    S=len(Wa)-1
    NEG=-1e18
    A=np.full(N+1,NEG); A[0]=0.0   # all-parts
    Bn=np.full(N+1,NEG)            # with a na part
    for i in range(k):
        A2=np.full(N+1,NEG); B2=np.full(N+1,NEG)
        for s in range(1,min(S,N)+1):
            if Wa[s]>-np.inf:
                A2[s:]=np.maximum(A2[s:],A[:N+1-s]+Wa[s]); B2[s:]=np.maximum(B2[s:],Bn[:N+1-s]+Wa[s])
            if Wn[s]>-np.inf:
                B2[s:]=np.maximum(B2[s:],A[:N+1-s]+Wn[s])
        A,Bn=A2,B2
    return Bn
def bound(FA,FN,k,Nmax,ts):
    S=max(FA); best=np.full(Nmax+1,np.inf)
    for t in ts:
        mu=1/(k*t)
        Wa=env(FA,S,mu); Wn=env(FN,S,mu)
        v=math.log(t)+1/t-1+knap(Wa,Wn,k,Nmax)
        best=np.minimum(best,v)
    return best
if __name__=="__main__":
    fa,fn=pickle.load(open(sys.argv[1],"rb")); Nmax=int(sys.argv[2])
    ts=np.linspace(1.02,3,100)
    worst={}
    for k in range(1,min(Nmax,60)):
        b=bound(fa,fn,k,Nmax-1,ts)
        for n in range(max(4,k+1),Nmax+1):
            m=PHI[n]-b[n-1]
            if n not in worst or m<worst[n][0]: worst[n]=(m,k)
    bad=[(n,worst[n]) for n in worst if worst[n][0]<=0]
    print("failures (n,margin,k):",[(n,round(m,5),k) for n,(m,k) in sorted(bad)][:40], "count",len(bad))
