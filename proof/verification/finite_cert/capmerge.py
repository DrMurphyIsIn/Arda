import sys, math, pickle
import numpy as np
from rootb import PHI
from rootbell2 import knapH
from bellman import bellman
S=490; H=100; Nmax=491
grid=np.linspace(0.5/H,0.5,H)
thr={2:28,3:70,4:104,5:298}
KSET=[int(x) for x in sys.argv[1].split(",")]   # caps available (children per vertex)
tabs={C:bellman(S,C,grid) for C in KSET}
unc=bellman(90,89,grid)
worst={}
for k in range(2,Nmax):
    Nk=min(Nmax,90) if k>=24 else min(Nmax,thr.get(k,491))
    if Nk<k+1: continue
    if k>=24: Wa,Wn=unc
    else:
        C=min(c for c in KSET if c>=k-1); Wa,Wn=tabs[C]
    Bn=knapH(Wa[:Nk],Wn[:Nk],k,Nk-1); t=1/(k*grid); best=np.min(np.log(t)+1/t-1+Bn,axis=1)
    for n in range(k+1,Nk+1):
        m=PHI[n]-best[n-1]
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0)
print("caps",KSET,"failures:",bad[:20],"count",len(bad))
