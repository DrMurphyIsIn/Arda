import sys, math, pickle, numpy as np
from rootb import PHI
from rootbell2 import knapH
from bellman import bellman
S=int(sys.argv[1]); Nmax=int(sys.argv[2]); Hd=int(sys.argv[3]); Hs=int(sys.argv[4])
grid=np.unique(np.concatenate([np.linspace(0.02,0.15,Hd),np.linspace(0.15,0.5,Hs),np.linspace(0.002,0.02,4)]))
H=len(grid)
thr={2:28,3:70,4:104,5:298}
CAPS=[1,2,3,4,5,6,7,8,12,16,22]
tabs={C:bellman(S,C,grid) for C in CAPS}; unc=bellman(90,89,grid)
worst={}; rootg={}
for k in range(2,Nmax):
    Nk=min(Nmax,90) if k>=24 else min(Nmax,thr.get(k,491))
    if Nk<k+1: continue
    Wa,Wn=unc if k>=24 else tabs[min(c for c in CAPS if c>=k-1)]
    Bn=knapH(Wa[:Nk],Wn[:Nk],k,Nk-1); t=1/(k*grid); val=np.log(t)+1/t-1+Bn; best=np.min(val,axis=1)
    for n in range(k+1,Nk+1):
        m=PHI[n]-best[n-1]
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0)
print("H",H,"failures",bad[:20],"count",len(bad))
