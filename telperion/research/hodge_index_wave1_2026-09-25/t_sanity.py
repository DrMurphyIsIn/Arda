from wf import *
import time
nm=60
cE=logderiv_coeffs(a_E(nm),nm); cK=logderiv_coeffs(a_ZK(nm),nm); cD=logderiv_coeffs(a_D(nm),nm)
for n in range(2,13):
    pk=primepow(n); lamK = (np.log(pk[0])*(1+chi20(n)) if pk else 0)
    print(n, 'cK=%.4f (Lambda(1+chi)=%.4f) cE=%.4f cD=%.4f'%(cK[n],lamK,cE[n],cD[n]))
print('max|cK - Lambda(1+chi)|', max(abs(cK[n]-((np.log(primepow(n)[0])*(1+chi20(n))) if primepow(n) else 0)) for n in range(2,nm+1)))
# convergence of arch in T, dt
for T,dt in [(300,0.04),(600,0.02),(1200,0.02)]:
    W=WF(20,10,0,20,[0,1],True,T=T,dt=dt); print('ZK x=20 N=10 even T=%g dt=%g lmin=%.5e'%(T,dt,W.lmin({n:cK[n] for n in W.P})))
