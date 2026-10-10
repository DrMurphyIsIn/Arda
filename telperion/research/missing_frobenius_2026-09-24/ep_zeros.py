import mpmath as mp, sys
from ep_core import *
mp.mp.dps = 15
T = float(sys.argv[1]) if len(sys.argv)>1 else 60
dt = 0.05
prevE = prevK = None; nE = nK = 0; t = 0.2
lastrep = 0
while t < T:
    s = mp.mpc(0.5, t)
    zk, g = parts(s)
    ph = gam(s)
    vE = mp.re(ph*(zk+g)); vK = mp.re(ph*zk)
    if prevE is not None:
        if vE*prevE < 0: nE += 1
        if vK*prevK < 0: nK += 1
    prevE, prevK = vE, vK
    if t - lastrep >= 5:
        exp = theta(t)/mp.pi + 1
        print("t=%6.1f  Nline_E=%3d Nline_ZK=%3d  theta/pi+1=%.2f  imag-check=%.1e" % (t, nE, nK, float(exp), float(abs(mp.im(ph*(zk+g)))/(abs(ph*(zk+g))+1e-30))), flush=True)
        lastrep = t
    t += dt
