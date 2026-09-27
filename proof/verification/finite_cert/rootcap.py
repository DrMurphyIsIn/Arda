import sys, math, pickle
import numpy as np
from rootb import bound, PHI
S=int(sys.argv[1]); Nmax=int(sys.argv[2]); tmax=float(sys.argv[3]) if len(sys.argv)>3 else 4
ts=np.linspace(1.01,tmax,150)
worst={}
unc=pickle.load(open(f"fr_{S}_0.pkl","rb"))
for k in range(2,Nmax):
    fa,fn = pickle.load(open(f"fr_{S}_{k-1}.pkl","rb")) if k<=23 else unc
    b=bound(fa,fn,k,Nmax-1,ts)
    for n in range(k+1,Nmax+1):
        m=PHI[n]-b[n-1]
        if n not in worst or m<worst[n][0]: worst[n]=(m,k)
bad=sorted((n,round(m,6),k) for n,(m,k) in worst.items() if m<=0)
print("failures:",bad[:60],"count",len(bad))
print("min margin over n>=10:",min((worst[n][0],n,worst[n][1]) for n in worst if n>=10))
pickle.dump(worst,open(f"worst_{S}_{Nmax}.pkl","wb"))
