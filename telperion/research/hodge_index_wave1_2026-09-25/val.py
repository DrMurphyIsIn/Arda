from amp import *
import time
for kind in ['zeta','ZK','E']:
    rh = load_zeros(kind)
    for (x,frac,m,g0) in [(np.e**2,0.7,6,20.0),(np.e**1.5,0.6,6,15.0),(8.0,0.5,8,30.)]:
        te = Test(x,frac,m,g0)
        ks=[1,2,3]
        t0=time.time(); P = prime_side(kind, te, ks); Z,_ = zero_side(te, rh, ks)
        for k in ks:
            print(kind, round(x,3), k, 'prime-side %.10e'%P[k]['s'].real, 'imag %.1e'%P[k]['s'].imag, 'zero-side %.10e'%Z[k].real, 'rel %.1e'%(abs(P[k]['s']-Z[k])/abs(Z[k])), '%.1fs'%(time.time()-t0))
