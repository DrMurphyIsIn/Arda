"""Pole-free near-radical probe: w = (Phi'/4 - Phi''') 1_W  (w^ = -i z (z^2+1/4) Xi(z) up to tails, so it
vanishes at every zero AND at z = +-i/2).  Exact pole-free correction w' = w - t z, z = Phi' 1_{W'},
x' = q - 0.5 (z has no overlap at shift log q), t = A(w)/A(z).  Zero-side values scaled by e^{2 pi q}."""
import json
import numpy as np, sympy as sp
from scipy.optimize import brentq
import probe_fast as pf

U, N = sp.symbols('u n', positive=True)
f = (4 * sp.pi**2 * N**4 * sp.exp(sp.Rational(9, 2) * U) - 6 * sp.pi * N**2 * sp.exp(sp.Rational(5, 2) * U))
E = -sp.pi * N**2 * sp.exp(2 * U)
# Phi_n = f * exp(E); write derivatives as (poly) * exp(E) and scale exp(E + shift)
d1 = sp.simplify(sp.diff(f * sp.exp(E), U) / sp.exp(E))
d3 = sp.simplify(sp.diff(f * sp.exp(E), U, 3) / sp.exp(E))
F1 = sp.lambdify((U, N), d1, 'numpy'); F3 = sp.lambdify((U, N), d3, 'numpy')

def deriv_s(u, which, shift, M=8):
    u = np.asarray(u, float); sgn = np.sign(u); v = np.abs(u); s = np.zeros_like(v)
    for n in range(1, M + 1):
        with np.errstate(under='ignore', over='ignore'):
            ex = np.exp(-np.pi * n * n * np.exp(2 * v) + shift)
        if which == 'w':
            s = s + (F1(v, n) / 4 - F3(v, n)) * ex
        else:
            s = s + F1(v, n) * ex
    return sgn * s          # both odd functions

Z = pf.ZEROS
def tailhat(which, L, shift):
    a = L / 2; v, wts = pf.tail_nodes(a); d = deriv_s(v, which, shift)
    return 2 * (np.sin(np.outer(Z, v)) @ (wts * d))        # |tau^| = 2|S| (imaginary unit dropped)

def A_of(which, L, shift):
    # A(g) = int_W g e^{u/2} = (full integral) - tail;  full integral of odd g times e^{u/2} = int g sinh(u/2)
    # full: for w: ghat(-i/2)-type value = 0 exactly (vanishes at +-i/2); for z=Phi': int Phi' sinh(u/2) = -(1/2) int Phi cosh(u/2) = -(1/2)Xi(i/2) = -1/4
    a = L / 2; v, wts = pf.tail_nodes(a)
    tail = 2 * np.sum(wts * deriv_s(v, which, shift) * np.sinh(v / 2))
    full = 0.0 if which == 'w' else -0.25 * np.exp(shift)
    return full - tail

def QS_pf(q, x):
    sh = np.pi * q
    L = np.log(x); Lp = np.log(q - 0.5)
    tw = tailhat('w', L, sh); tz = tailhat('z', Lp, 0.0)          # z unscaled
    Aw = A_of('w', L, sh); Az = A_of('z', Lp, 0.0)
    t = Aw / Az                                                    # scaled by e^{pi q}
    # Q(w') = sum |tw - t tz|^2 over zeros (+-gamma): tails sign conventions consistent (both odd, same formula)
    Qw = np.sum(2 * (tw - t * tz) ** 2)
    lo, hi = np.log(q) - L / 2, L / 2
    xv, wv = pf.gl(lo, hi, 400)
    h = float(np.sum(wv * deriv_s(xv, 'w', sh) * deriv_s(xv - np.log(q), 'w', sh)))
    return Qw + 2 * np.log(q) / np.sqrt(q) * h, Qw, h

out = {}
for q in [11, 13, 23, 47, 97, 199]:
    g = lambda dx: QS_pf(q, q + dx)[0]
    grid = [0.01, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.6, 0.8, 1.0, 1.5, 2.0]
    vals = [(dx, g(dx)) for dx in grid]
    root = None
    for (a_, fa), (b_, fb) in zip(vals[:-1], vals[1:]):
        if fa > 0 and fb < 0:
            root = brentq(g, a_, b_, xtol=1e-4); break
    out[q] = root
    print(q, 'pole-free probe onset dx =', root, ' h sign at dx=0.5:', np.sign(QS_pf(q, q + 0.5)[2]), flush=True)
json.dump(out, open('probe_polefree_onsets.json', 'w'))
