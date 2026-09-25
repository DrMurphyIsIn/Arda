"""Weil form on window [-A,A] (x = e^{2A}) for the degree-2 pair
   ZK = zeta*L(chi_-20)  (Dedekind zeta of Q(sqrt-5), Euler product)  and
   E  = Epstein zeta of x^2+5y^2 = ZK + L(chi_-4)L(chi_5)  (a_n >= 0, pole, same FE, NO Euler product).
Arch = sum of two Gamma_R families (beta0 = 1/2, c0=-log pi) + (beta0 = 3/2, c0 = log(20/pi)); pole as zeta.
Reuses the Crux3 FWindow closed forms (copied, not modified)."""
import mpmath as mp, numpy as np, sys
import weilfreq
from weilfreq import FWindow
from weilmodes import von_mangoldt
from ep_core import coeffs, logderiv_weights, chi_m20
mp.mp.dps = 20
weilfreq.mp.mp.dps = 20

class Fam(FWindow):
    def __init__(self, A, beta0, c0, w=None, pole=False):
        import weilmodes
        self._b0, self._c0 = mp.mpf(beta0), mp.mpf(c0)
        orig = weilfreq.consts, weilfreq.weights
        weilfreq.consts = lambda kind: (self._b0, self._c0)
        weilfreq.weights = lambda kind, nmax: (w if w is not None else [mp.mpf(0)] * (nmax + 1))
        FWindow.__init__(self, A, 'zeta' if pole else 'other')
        weilfreq.consts, weilfreq.weights = orig

def form(A, kind, M):
    x = mp.exp(2 * A); nmax = int(mp.floor(x))
    if kind == 'ZK':
        lam = von_mangoldt(nmax)
        w = [lam[n] * (1 + chi_m20(n)) if n >= 1 else 0 for n in range(nmax + 1)]
    elif kind == 'E':
        aE, _, _ = coeffs(nmax)
        w = logderiv_weights(aE, nmax)
    f1 = Fam(A, 0.5, -mp.log(mp.pi), w=w, pole=True)          # carries prime side + pole
    f2 = Fam(A, 1.5, mp.log(20 / mp.pi), w=None, pole=False)  # second gamma family, no primes
    ks = [mp.pi * m / A for m in range(-M, M + 1)]
    M1, G, C, P, R = f1.matrices(ks)
    M2, _, _, _, _ = f2.matrices(ks)
    n = len(ks)
    Mn = np.array([[complex(M1[i, j] + M2[i, j]) for j in range(n)] for i in range(n)])
    Gn = np.array([[complex(G[i, j]) for j in range(n)] for i in range(n)])
    Mn = (Mn + Mn.conj().T) / 2; Gn = (Gn + Gn.conj().T) / 2
    Lc = np.linalg.cholesky(Gn); Li = np.linalg.inv(Lc)
    ev, W = np.linalg.eigh(Li @ Mn @ Li.conj().T); V = Li.conj().T @ W
    return ev[0], V[:, 0], ks

if __name__ == "__main__":
    xs = [float(v) for v in sys.argv[1:]] or [2, 4, 8, 12, 16, 20, 25, 30]
    for x in xs:
        A = mp.log(x) / 2
        M = int(mp.ceil(24 * A / mp.pi)) + 2
        eK, _, _ = form(A, 'ZK', M)
        eE, v, ks = form(A, 'E', M)
        kdom = float(abs(ks[int(np.argmax(abs(v)))]))
        print("x=%6.2f A=%.3f M=%d  lam_min ZK=%+.5f   lam_min E=%+.5f  (E eigvec peak |k|=%.2f)" % (x, float(A), M, eK, eE, kdom), flush=True)
