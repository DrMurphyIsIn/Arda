import wf
from wf import *
A=np.log(2)/2
for tf in (15,30,60):
    wf.TFAC=tf
    r=[lam(2.0,N,GAM['zeta'],[]) for N in (6,10,14)]
    print(tf, r, flush=True)
