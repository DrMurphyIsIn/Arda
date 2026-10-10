from wf import *
nm=60
cK=logderiv_coeffs(a_ZK(nm),nm)
for N in [8,12]:
  for T,dt in [(100,0.02),(200,0.02),(200,0.01),(400,0.02)]:
    W=WF(20,N,0,20,[0,1],True,T=T,dt=dt); print('ZK x=20 N=%d even T=%g dt=%g lmin=%.6e'%(N,T,dt,W.lmin({n:cK[n] for n in W.P})),flush=True)
