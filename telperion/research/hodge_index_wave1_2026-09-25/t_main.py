from wf import *
import itertools
nm=80
C={'ZK':logderiv_coeffs(a_ZK(nm),nm),'E':logderiv_coeffs(a_E(nm),nm),'D':logderiv_coeffs(a_D(nm),nm),
   'zeta':[0,0]+[np.log(primepow(n)[0]) if primepow(n) else 0 for n in range(2,nm+1)]}
SPEC={'ZK':(20,[0,1],True),'E':(20,[0,1],True),'D':(5,[1],False),'zeta':(1,[0],True)}
def lm(kind,x,N=12,c=None):
    q,mus,pole=SPEC[kind]; out=[]
    for par in [0,1]:
        W=WF(x,N,par,q,mus,pole,T=200,dt=0.02)
        cc = c if c is not None else {n:C[kind][n] for n in W.P}
        out.append(W.lmin(cc))
    return out
print('--- controls (smooth basis N=12; value = Rayleigh-Ritz upper bound on lambda_min)')
for kind,xs in [('zeta',[2,3,6]),('ZK',[6,20,22]),('E',[6,12,18,19.5,20.5,22,25]),('D',[20,28,31,34,38,45])]:
    for x in xs: print(kind,x,['%.4e'%v for v in lm(kind,x)],flush=True)
print('--- exhaustive pure-local search, ZK data (strict: alpha_2,alpha_5 in {1,-1,0}; p=3 theta grid or inert)')
def cvec(x,a2,t3,a5):
    c={}
    for n in range(2,int(np.floor(x-1e-12))+1):
        pk=primepow(n)
        if not pk: continue
        p,k=pk
        if p==2: c[n]=np.log(2)*a2**k
        elif p==5: c[n]=np.log(5)*a5**k
        elif p==3: c[n]=np.log(3)*(2*np.cos(k*t3) if t3 is not None else (1+(-1)**k))
        else: raise
    return c
for x in [4.9,5.03,5.06,5.1,5.5,6.0]:
    for N in [10,14]:
        Ws=[WF(x,N,par,20,[0,1],True,T=200,dt=0.02) for par in [0,1]]
        best=(9,None)
        for a2 in [1,-1,0]:
            for a5 in [1,-1,0]:
                for t3 in list(np.linspace(0,np.pi,25))+[None]:
                    v=min(W.lmin(cvec(x,a2,t3,a5)) for W in Ws)
                    if v<best[0]: best=(v,(a2,t3,a5))
        zk=min(W.lmin({n:C['ZK'][n] for n in W.P}) for W in Ws)
        print('x=%.2f N=%d worst=%.4e at (a2,theta3,a5)=%s ; zetaK=%.4e'%(x,N,best[0],best[1],zk),flush=True)
