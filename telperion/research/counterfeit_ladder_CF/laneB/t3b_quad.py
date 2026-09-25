"""Independent time-domain check (dps 40, closed-form autocorrelation, no FWindow closed forms)."""
import numpy as np, mpmath as mp
from bcore import *
x = 24; A0 = mp.log(x)/2
for kind in ('ZK', 'E'):
    fm = Form(A0, kind)
    for par in (0, 1):
        kap = sector_basis(A0, 12, par, 'neumann')
        Mr, Gr = real_sector(fm, kap, par)
        e, V = gmin(Mr, Gr, vec=True); v = V[:, 0]
        mp.mp.dps = 40
        A = mp.log(x)/2
        K = [mp.mpf(k) for k in kap]; K = [mp.pi*m/A for m in range(12)] if par == 0 else [mp.pi*(m+mp.mpf(1)/2)/A for m in range(12)]
        a = [mp.mpf(float(c)) for c in v]
        def Ic(al, th, lo, hi):
            if al == 0: return (hi-lo)*mp.cos(th)
            return (mp.sin(al*hi+th) - mp.sin(al*lo+th))/al
        def Is(al, th, lo, hi):  # int sin(al u + th)
            if al == 0: return (hi-lo)*mp.sin(th)
            return -(mp.cos(al*hi+th) - mp.cos(al*lo+th))/al
        def g(y):
            y = abs(y)
            if y >= 2*A: return mp.mpf(0)
            lo, hi = y - A, A; s = 0
            for i in range(12):
                for j in range(12):
                    ki, kj = K[i], K[j]
                    if par == 0:   # cos(ki u) cos(kj (u-y))
                        val = (Ic(ki+kj, -kj*y, lo, hi) + Ic(ki-kj, kj*y, lo, hi))/2
                    else:          # sin(ki u) sin(kj (u-y)) = [cos((ki-kj)u + kj y) - cos((ki+kj)u - kj y)]/2
                        val = (Ic(ki-kj, kj*y, lo, hi) - Ic(ki+kj, -kj*y, lo, hi))/2
                    s += a[i]*a[j]*val
            return s
        g0 = g(0)
        arch = 0
        for b0, c0 in families(kind):
            W = lambda u: 2*mp.exp(-b0*u)/(-mp.expm1(-2*u))
            pts = [0, mp.mpf('1e-6'), mp.mpf('1e-3'), mp.mpf('0.05')] + list(mp.linspace(0.2, 2*A, 12))
            I1 = mp.quad(lambda u: g0*mp.exp(-2*u)/u - W(u)*g(u), pts)
            arch += c0*g0 + I1 + g0*mp.e1(4*A)
        trig = mp.cos if par == 0 else mp.sin
        f = lambda u: sum(a[i]*trig(K[i]*u) for i in range(12))
        Fp = mp.quad(lambda u: f(u)*mp.exp(-u/2), [-A, 0, A]); Fm = mp.quad(lambda u: f(u)*mp.exp(u/2), [-A, 0, A])
        pole = 2*Fp*Fm
        comb = sum(c*2*g(mp.log(n)) for (n, c, y) in fm.pr)
        Qq = pole + arch - comb
        print(kind, 'par', par, 'time-domain Q=%.12f  matrix Q=%.12f  diff=%.2e  ||f||^2 %.12f vs %.12f' % (float(Qq), v@Mr@v, float(Qq)-v@Mr@v, float(g0), v@Gr@v), flush=True)
        mp.mp.dps = 30
