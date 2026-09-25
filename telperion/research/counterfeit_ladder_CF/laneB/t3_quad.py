"""Independent check: time-domain Weil form by quadrature (Weil's arch formula, no closed forms)
   vs the closed-form sector matrix, on the N=12 lowest eigenvector (even and odd)."""
import numpy as np, mpmath as mp
from bcore import *
mp.mp.dps = 20
x = 24; A = mp.log(x)/2; Af = float(A)
for kind in ('ZK', 'E'):
    fm = Form(A, kind)
    for par in (0, 1):
        kap = sector_basis(A, 12, par, 'neumann')
        Mr, Gr = real_sector(fm, kap, par)
        e, V = gmin(Mr, Gr, vec=True); v = V[:, 0]
        trig = mp.cos if par == 0 else mp.sin
        f = lambda u: sum(v[i] * trig(kap[i] * u) for i in range(len(kap))) if abs(u) <= A else mp.mpf(0)
        def g(y):
            y = abs(y)
            if y >= 2 * A: return mp.mpf(0)
            return mp.quad(lambda s: f(s) * f(s - y), mp.linspace(y - A, A, 6))
        g0 = g(0)
        # arch: sum_fam c0 g(0) + int_0^inf [g(0) e^{-2u}/u - W(u) g(u)] du
        gg = {}
        arch = 0
        for b0, c0 in families(kind):
            W = lambda u: 2 * mp.exp(-b0 * u) / (1 - mp.exp(-2 * u))
            I1 = mp.quad(lambda u: g0 * mp.exp(-2 * u) / u - W(u) * g(u), mp.linspace(0, 2 * A, 9))
            I2 = g0 * mp.e1(4 * A)  # int_{2A}^inf e^{-2u}/u = E1(4A)
            arch += c0 * g0 + I1 + I2
        Fp = mp.quad(lambda u: f(u) * mp.exp(-u / 2), [-A, 0, A]); Fm = mp.quad(lambda u: f(u) * mp.exp(u / 2), [-A, 0, A])
        pole = 2 * Fp * Fm
        comb = sum(c * 2 * g(y) for (_, c, y) in fm.pr)
        Qq = pole + arch - comb
        Qm = v @ Mr @ v
        print(kind, 'par', par, 'quad Q=%.12f  matrix Q=%.12f  diff=%.2e  |f|^2 quad=%.10f matrix=%.10f' % (
            float(Qq), Qm, float(Qq) - Qm, float(g0), v @ Gr @ v), flush=True)
