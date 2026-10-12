import os
for k in ["OMP_NUM_THREADS","OPENBLAS_NUM_THREADS","MKL_NUM_THREADS","VECLIB_MAXIMUM_THREADS"]: os.environ[k]="1"
import numpy as np, mpmath as mp
N=120
x,w=np.polynomial.legendre.leggauss(N); x=(x+1)/2; w=w/2
K=2*np.cos(2*np.pi*np.outer(x,x))
sw=np.sqrt(w); A=sw[:,None]*K*sw[None,:]
lam,U=np.linalg.eigh(A)
E=U/sw[:,None]          # columns e_n(x_j), normalised: sum w e^2 = 1
print("top |lam|:",sorted(abs(lam))[::-1][:5])
def Ce(wv):  # (C e_n)(wv) = int 2cos(2 pi wv y) e_n(y) dy  = lam phi_n(wv)
    return (2*np.cos(2*np.pi*np.outer(wv,x))*w[None,:])@E
def sincInt(c): return float(mp.quad(lambda s: mp.sinc(c*s),[0,1]))
def deltaK(t): t=abs(t); return 2*np.exp(t/2)*(sincInt(2*np.pi*(np.exp(t)+1))+sincInt(2*np.pi*(np.exp(t)-1)))
for t in [0.0,0.3,1.0,2.0]:
    a=Ce(x); b=Ce(np.exp(t)*x)
    terms=np.exp(t/2)*np.sum(w[:,None]*a*b,axis=0)   # lam_n^2 e^{t/2} int phi(v)phi(e^t v)
    # also via xi/eta representation: lam*<xi, theta(-t) eta>, xi=phi(|v|)/sqrt2 on [-1,1], eta=lam phi(|w|)/sqrt2
    print(t, terms.sum(), deltaK(t))
