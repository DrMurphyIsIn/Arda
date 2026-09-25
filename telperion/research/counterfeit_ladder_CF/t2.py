import mpmath as mp, time
from cf_core import *
mp.mp.dps = 30
N=80
cE = logderiv_coeffs(lattice_aE, N); cK = cK_list(N)
A = mp.log(28)/2
q = A/mp.pi
for M in (9,):
    t=time.time()
    W = dirichlet_window(q, M)
    Ms = matrices(W, cE, cK)
    gram = Ms['gram']
    # generalized eigen: QE v = lam gram v; gram = A I
    QEn = Ms['QE']/A; QKn = Ms['QK']/A
    ev, V = mp.eigsy(QEn)
    i0 = min(range(M), key=lambda i: ev[i])
    v = [V[r,i0] for r in range(M)]
    mx = max(v, key=abs); v=[x/mx for x in v]
    nv = sum(x*x for x in v)
    print("M",M,"lam_min(E)/A-normalized", ev[i0], "time", time.time()-t)
    print("v =", [mp.nstr(x,4) for x in v])
    print("Q_E(v)/(A|c|^2) =", quadval(Ms['QE'],v)/(A*nv), " Q_K(v)/(A|c|^2) =", quadval(Ms['QK'],v)/(A*nv))
    print("Q_E(v)/|c|^2 =", quadval(Ms['QE'],v)/(nv), " Q_K/|c|^2 =", quadval(Ms['QK'],v)/nv)
    print("Q_E(v), Q_K(v) raw:", quadval(Ms['QE'],v), quadval(Ms['QK'],v))
    evK,_ = mp.eigsy(QKn); print("lam_min(K) on span", min(evK))
    print("parts at v: pole", quadval(Ms['pole'],v), "arch", quadval(Ms['arch'],v), "pE", quadval(Ms['pE'],v), "pK", quadval(Ms['pK'],v))
