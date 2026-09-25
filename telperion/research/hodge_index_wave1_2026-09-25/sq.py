"""squareroot angle: E = sqrt(zK*LG) * cosh(u), u = (1/2) log(zK/LG).
   -E'/E = avg(-zK'/zK, -LG'/LG) + d/ds[-log cosh u].  Decompose Q_E = Q_avg + R."""
import sys; sys.path.insert(0, '/private/tmp/claude-0/-Users-peterwmurphy/ef083c48-579d-4bec-a689-c30fdccec2a1/scratchpad/cf/B')
import numpy as np, mpmath as mp
from bcore import *

def lp_list(nmax):
    return mangoldt(nmax)

def w_LG(nmax):
    lp = mangoldt(nmax)
    return [mp.log(lp[n]) * (chi_m4(n) + leg5(n)) if lp[n] else mp.mpf(0) for n in range(nmax + 1)]

def dconv(a, b, nmax):
    c = [mp.mpf(0)] * (nmax + 1)
    for m in range(1, nmax + 1):
        if a[m] == 0: continue
        for k in range(1, nmax // m + 1):
            c[m * k] += a[m] * b[k]
    return c

def cross_weights(nmax, order):
    """coefficients (times log n) of -d/ds log cosh u, truncated to u^{2..order}. order=None: exact."""
    wZ = weights_mp('ZK', nmax); wL = w_LG(nmax)
    b = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        b[n] = (wZ[n] - wL[n]) / (2 * mp.log(n))  # u = sum b(n) n^{-s}
    # log cosh u = sum_k T_k u^{2k}, T = 1/2, -1/12, 1/45, -17/2520, 31/14175
    T = [mp.mpf(1)/2, -mp.mpf(1)/12, mp.mpf(1)/45, -mp.mpf(17)/2520, mp.mpf(31)/14175, -mp.mpf(691)/467775]
    acc = [mp.mpf(0)] * (nmax + 1)
    u2 = dconv(b, b, nmax); p = u2[:]
    k = 1
    while k <= len(T) and 2**(2*k) <= nmax and (order is None or 2*k <= order):
        for n in range(nmax + 1): acc[n] += T[k-1] * p[n]
        p = dconv(p, u2, nmax); k += 1
    return [acc[n] * mp.log(n) if n >= 2 else mp.mpf(0) for n in range(nmax + 1)]

def form_with(A, w, famkind='ZK'):
    fm = Form(A, 'zeta' if famkind == 'zeta' else 'ZK')
    fm.pr = [(n, float(w[n] / mp.sqrt(n)), float(mp.log(n))) for n in range(2, fm.nmax + 1) if abs(w[n]) > 1e-30]
    return fm

def sector_parts(fm, A, N, par):
    Mr, Gr, P = real_sector(fm, sector_basis(A, N, par, 'neumann'), par, parts=True)
    return Gr, P

if __name__ == '__main__':
    # consistency: c_E == avg + cross(exact)
    nm = 60
    cE = weights_mp('E', nm); wZ = weights_mp('ZK', nm); wL = w_LG(nm); cr = cross_weights(nm, None)
    err = max(abs(cE[n] - (wZ[n] + wL[n]) / 2 - cr[n]) for n in range(2, nm + 1))
    print('identity check max err', mp.nstr(err, 5))
    for n in range(2, 41):
        if abs(cE[n]) > 1e-20 or abs(cr[n]) > 1e-20:
            print(n, 'cE=%+.4f avg=%+.4f cross=%+.4f' % (cE[n], (wZ[n]+wL[n])/2, cr[n]))
