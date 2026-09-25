import wf
from wf import *
wf.WEXP=1
def cz(x,a2):
    c={}
    for n in range(2,int(np.floor(x-1e-12))+1):
        pk=primepow(n)
        if pk: p,k=pk; c[n]=np.log(p)*(a2**k if p==2 else 1.0)
    return c
for a2 in [1.0,0.99,-1.0]:
    v=[WF(3.0,20,par,1,[0],True,T=800,dt=0.02).lmin(cz(3.0,a2)) for par in [0,1]]
    print('zeta data x=3 alpha2=%.2f lmin=%.4e %.4e'%(a2,*v),flush=True)
def cu(x,t2,t3):
    c={}
    for n in range(2,int(np.floor(x-1e-12))+1):
        pk=primepow(n)
        if pk: p,k=pk; c[n]=np.log(p)*2*np.cos(k*(t2 if p==2 else t3))
    return c
for x in [4.12,4.18,4.22,4.3]:
    Ws=[WF(x,20,par,20,[0,1],True,T=800,dt=0.02) for par in [0,1]]
    best=min((min(W.lmin(cu(x,t2,t3)) for W in Ws),t2,t3) for t2 in np.linspace(0,np.pi,13) for t3 in np.linspace(0,np.pi,13))
    print('ZK unitary-all-p x=%.2f worst=%.4e theta2=%.2f theta3=%.2f'%(x,*best),flush=True)
