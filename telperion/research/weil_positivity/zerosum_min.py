import os, sys
sys.path.insert(0, os.path.expanduser("~/arda-e9-audit/telperion/research/weil_positivity"))
import cc_followup as cf, weil_form as wf, mpmath as mp, numpy as np
mp.mp.dps = 40
a = mp.log(2) / 2; K = 40
S = cf.legendre_gram(a, K)
Bs, idx = cf.sector(S["G"], 0)
ev, Q, order = cf.eig_sym(Bs)
c = np.zeros(K)
for r, j in enumerate(idx):
    c[j] = float(Q[r, order[0]])
af = float(a)
x, w = np.polynomial.legendre.leggauss(400)
xs = af * x; ws = af * w
import gram_experiments as ge
f = c @ (ge.legendre_norm_eval(K, x) / np.sqrt(af))
print("||f||^2 =", (f * f * ws).sum())
Z = np.array([float(g) for g in wf.load_zeros()])
from scipy.special import spherical_jn
F = np.zeros(len(Z))
amp = np.zeros(len(Z), complex)
for jj in range(K):
    if c[jj] != 0:
        amp += c[jj] * np.sqrt((2*jj+1)/(2*af)) * 2*af * (1j)**jj * spherical_jn(jj, af*Z)
F = np.abs(amp)**2
tot = 2 * F.sum()
# tail: |F(t)|^2 ~ C/t^2 (f does not vanish at the endpoints); fit C on the last 5000 zeros, integrate density
C = np.median(F[-5000:] * Z[-5000:] ** 2)
T = Z[-1]
tail = 2 * C * (np.log(T / (2 * np.pi)) + 1) / (2 * np.pi * T)
print("lambda_min (Gram)       =", mp.nstr(ev[0], 10))
print("zero sum, 20000 zeros   =", tot)
print("tail estimate (C/t^2)   =", tail, " C =", C)
print("zero sum + tail         =", tot + tail)
