import numpy as np, mpmath as mp, weilwin as W
# 1. constant identity
for a,z in ((0,0.25),(1,0.75)):
    e=0.5 if a==0 else -0.5
    v=mp.quad(lambda u: mp.e**(-2*u)/u - mp.e**(e*u)/mp.sinh(u),[0,1,mp.inf])
    print('const',a,v,mp.digamma(z))
# 2. Crux3 band test: freqs 763/9, 259/3 on A=9pi/14
A=9*np.pi/14
fr=np.array([763/9,259/3])
orig=W.basis
def b(A_,N,p): 
    G=np.array([[W.corr(A,fr,np.array([0.0]),0)[i,j,0] for j in range(2)] for i in range(2)])
    return fr,G
W.basis=b
for kind in ('zeta','D'):
    Q,G,_=W.form_matrix(kind,A,2,0,M=400)
    c=np.array([-3.,2.])
    ev=np.linalg.eigvals(np.linalg.solve(G,Q))
    print(kind,'Rayleigh(-3,2)=',c@Q@c/(c@G@c),'eigs',sorted(ev.real))
W.basis=orig
