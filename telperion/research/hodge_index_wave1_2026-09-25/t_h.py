import wf
from wf import *
def cw(x):
    c={}
    for n in range(2,int(np.floor(x-1e-12))+1):
        pk=primepow(n)
        if pk: p,k=pk; c[n]=np.log(p)*{2:(-1)**k,3:2*(-1)**k,5:(-1)**k}[p]
    return c
for we in [3,1]:
    wf.WEXP=we
    for x in [5.03,5.06,5.1]:
        for N in [14,20,26]:
            try:
                v=[WF(x,N,par,20,[0,1],True,T=(200 if we==3 else 800),dt=0.02).lmin(cw(x)) for par in [0,1]]
                print('wexp=%d x=%.2f N=%d witness lmin even/odd = %.4e %.4e'%(we,x,N,*v),flush=True)
            except np.linalg.LinAlgError as e: print('ill-cond',we,x,N)
