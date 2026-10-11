"""CC section 3 'delta route' (no prolates): D o Q = -2 Id + K^delta_I (Thm 3.6), kernel
kappa(x) = (Q_+ delta)(e^{|x|}) = (-d^2/dx^2 + 1/4) delta(e^x) at |x| (x != 0), with the closed form (49)
delta(rho) = 2 rho^{1/2} [Si(2pi(1+rho))/(2pi(1+rho)) + Si(2pi(rho-1))/(2pi(rho-1))].
Weil positivity on the one-condition class follows (Prop 3.5 + Cor 2.3) on a g-interval of length a as
soon as lambda_max(K^delta_I) <= 2.  2026-10-11.  Numerical (mpmath derivatives), NOT certified.
conjecture1_proved = False."""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"
import math
import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq
mp.mp.dps = 30


def delta_e(x):
    rho = mp.e ** x
    a = 2 * mp.pi * (1 + rho)
    b = 2 * mp.pi * (rho - 1)
    tb = mp.si(b) / b if b != 0 else mp.mpf(1)
    return 2 * mp.sqrt(rho) * (mp.si(a) / a + tb)


def kappa(x):
    x = mp.mpf(abs(x))
    return float(-mp.diff(delta_e, x, 2) + delta_e(x) / 4)


xs = np.linspace(1e-6, math.log(2), 1500)
ks = np.array([kappa(v) for v in xs])
print("delta(1) =", float(delta_e(0)), " CC (50): 2(Si(4pi)/4pi + 1) =", float(2 * (mp.si(4 * mp.pi) / (4 * mp.pi) + 1)))
print("d/dx delta(e^x) at 0+ =", float(mp.diff(delta_e, mp.mpf('1e-12'))), " (CC: 1, so the jump gives -2 delta_0)")
print(f"kappa range on (0, log 2]: [{ks.min():.3f}, {ks.max():.3f}]  (CC Fig 8: about [-15, 15])")


def lmax(a, N=500):
    xg, wg = leggauss(N)
    t, w = a / 2 * xg, a / 2 * wg
    K = np.interp(np.abs(t[:, None] - t[None, :]), xs, ks)
    s = np.sqrt(w)
    return np.linalg.eigvalsh(s[:, None] * K * s[None, :])[::-1][:2]


for a in [0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, math.log(2)]:
    print(f"|I| = {a:.4f} (L = {a / 2:.4f}): top eigenvalues of K^delta_I = {lmax(a)}  (need <= 2)")
ad = brentq(lambda a: lmax(a)[0] - 2, 0.05, math.log(2)) if lmax(math.log(2))[0] > 2 else float('nan')
print(f"delta-route window: lambda_max(K^delta) = 2 at |I| = {ad:.5f}, our L = {ad / 2:.5f}")
cum = 2 * np.concatenate([[0], np.cumsum(np.abs(ks[1:]) * np.diff(xs))])
aS = xs[np.searchsorted(cum, 2.0)]
print(f"Schur/L1 version (2 int_0^a |kappa| <= 2): |I| <= {aS:.5f}, L <= {aS / 2:.5f}  (CC Cor 3.8 uses the f-support form: s = 0.0975)")
