"""Root: replace the exact k-part knapsack by a part-count Lagrangian: sum of k parts <= phi_kappa(N) + k*kappa,
phi_kappa(N) = max over ANY number of parts (>=1 non-atom) of sum (W_m - kappa)."""
import sys, math, pickle
import numpy as np
from rootb import PHI
from bellman import bellman
NEG=-1e30
S=490; H=100; Nmax=491
grid=np.linspace(0.5/H,0.5,H); thr={2:28,3:70,4:104,5:298}
CAPS=[1,2,3,4,5,6,7,8,12,16,22]
tabs={C:bellman(S,C,grid) for C in CAPS}
kappas=np.linspace(-0.3,0.3,121)
worst={}
for k in range(2,24):
    Nk=min(Nmax,thr.get(k,491)); C=min(c for c in CAPS if c>=k-1); Wa,Wn=tabs[C]
    t=1/(k*grid); base=np.log(t)+1/t-1
    best=np.full(Nk,np.inf)
    for kap in kappas:
        A=np.full((Nk,H),NEG); A[0]=0; Bn=np.full((Nk,H),NEG)
        for N in range(1,Nk):
            m=np.arange(1,N+1)
            A[N]=np.max(A[N-m]+Wa[m]-kap,axis=0)
            Bn[N]=np.max(np.maximum(Bn[N-m]+Wa[m]-kap,A[N-m]+Wn[m]-kap),axis=0)
        val=base[None,:]+Bn+k*kap
        best=np.minimum(best,np.min(val,axis=1))
    for n in range(k+1,Nk+1):
        mm=PHI[n]-best[n-1]
        if n not in worst or mm<worst[n][0]: worst[n]=(mm,k)
bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0)
print("count-relaxed root: failures",bad[:30],"count",len(bad))
