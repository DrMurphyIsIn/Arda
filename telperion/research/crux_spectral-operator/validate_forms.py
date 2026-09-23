"""Validation of the window Weil forms (wpw.py) in both parity sectors.

(1) Displacement identity.  Translation invariance of W_F makes multiplication by z^2 symmetric
    on transforms whose space-side function satisfies the boundary condition l^T c = 0, so the
    commutator C = Omega Q - Q Omega must equal l g^T - g l^T.  We measure
        res = max |C - (l g^T - g l^T)| / max |C|,   g = -C l / (l^T l).
    A wrong sign in any sum-frequency term, pole term or prime term breaks this identity.
(2) Brute force.  A few entries Q[p, q] recomputed from the definitions: the cross-correlation
    g(y) = int f1(s) f2(s + y) ds by quadrature, then pole + arch - primes applied to it.
(3) Agreement of the even sector with the idea's weilwin.py (if present).
"""
import sys
import json
import mpmath as mp
import wpw


def displacement_residual(Q, L, N, sector):
    l = wpw.boundary_functional(L, N, sector)
    om2 = wpw.omega2(L, N, sector)
    M = len(l)
    C = mp.matrix(M, M)
    for i in range(M):
        for j in range(M):
            C[i, j] = (om2[i] - om2[j]) * Q[i, j]
    ll = sum(t * t for t in l)
    g = [-sum(C[i, j] * l[j] for j in range(M)) / ll for i in range(M)]
    cmax = max(abs(C[i, j]) for i in range(M) for j in range(M))
    rmax = max(abs(C[i, j] - (l[i] * g[j] - g[i] * l[j])) for i in range(M) for j in range(M))
    return rmax / cmax, cmax


def basis(L, k, sector):
    om = 2 * mp.pi / L
    if sector == 'even':
        if k == 0:
            return lambda t: 1 / mp.sqrt(L)
        return lambda t: mp.sqrt(2 / L) * mp.cos(k * om * t)
    return lambda t: mp.sqrt(2 / L) * mp.sin(k * om * t)


def brute_entry(x, kind, sector, j, k):
    x = mp.mpf(x)
    L = mp.log(x)
    f1, f2 = basis(L, j, sector), basis(L, k, sector)
    h = L / 2

    def ge(y):  # even part of the cross-correlation, y >= 0
        if y >= L:
            return mp.mpf(0)
        gp = mp.quad(lambda s: f1(s) * f2(s + y), [-h, h - y])
        gm = mp.quad(lambda s: f1(s) * f2(s - y), [-h + y, h])
        return (gp + gm) / 2
    g0 = ge(mp.mpf(0))
    if kind == 'zeta':
        W = lambda u: mp.exp(u / 2) / mp.sinh(u)
        c0 = -mp.log(mp.pi)
        lam = wpw.von_mangoldt(int(x))
    else:
        W = lambda u: mp.exp(-u / 2) / mp.sinh(u)
        c0 = mp.log(mp.mpf(5) / mp.pi)
        lam = wpw.lambda_dh(int(x))
    # arch = c0 g(0) + int_0^inf [g(0) e^{-2u}/u - g_e(u) W(u)] du
    fix = mp.quad(lambda u: mp.exp(-2 * u) / u - W(u), [0, h, L])
    rest = mp.quad(lambda u: (g0 - ge(u)) * W(u), [0, h, L])
    arch = c0 * g0 + g0 * (fix + mp.e1(2 * L)) + rest
    pole = mp.mpf(0)
    if kind == 'zeta':
        A1 = mp.quad(lambda s: f1(s) * mp.exp(-s / 2), [-h, h])
        B1 = mp.quad(lambda s: f1(s) * mp.exp(s / 2), [-h, h])
        A2 = mp.quad(lambda s: f2(s) * mp.exp(-s / 2), [-h, h])
        B2 = mp.quad(lambda s: f2(s) * mp.exp(s / 2), [-h, h])
        pole = A1 * B2 + B1 * A2
    prime = mp.mpf(0)
    for n in range(2, int(x) + 1):
        if lam[n] != 0:
            prime += 2 * lam[n] / mp.sqrt(n) * ge(mp.log(n))
    return pole + arch - prime


def main():
    out = {'displacement': [], 'brute': [], 'weilwin_agreement': None}
    mp.mp.dps = 40
    for kind in ('zeta', 'dh'):
        for sector in ('even', 'odd'):
            for x in (9, 20, 40):
                N = 12
                Q, L = wpw.build(x, N, kind, sector)
                res, cmax = displacement_residual(Q, L, N, sector)
                row = dict(kind=kind, sector=sector, x=x, N=N, dps=mp.mp.dps,
                           residual=mp.nstr(res, 3), cmax=mp.nstr(cmax, 4))
                out['displacement'].append(row)
                print('displacement', row, flush=True)
    mp.mp.dps = 25
    for kind in ('zeta', 'dh'):
        for sector in ('even', 'odd'):
            x = 9
            N = 4
            Q, L = wpw.build(x, N, kind, sector)
            idx = list(range(0, N + 1)) if sector == 'even' else list(range(1, N + 1))
            for (p, q) in [(0, 0), (0, 2), (1, 3), (3, 3)]:
                j, k = idx[p], idx[q]
                b = brute_entry(x, kind, sector, j, k)
                row = dict(kind=kind, sector=sector, x=x, basis=(j, k), closed=mp.nstr(Q[p, q], 15),
                           brute=mp.nstr(b, 15), diff=mp.nstr(abs(Q[p, q] - b), 3))
                out['brute'].append(row)
                print('brute', row, flush=True)
    # agreement with the idea's even-sector code
    try:
        sys.path.insert(0, '/private/tmp/claude-0/crux-spectral-operator')
        import weilwin
        mp.mp.dps = 40
        for kind in ('zeta', 'dh'):
            Q1, L = wpw.build(13, 20, kind, 'even')
            Q2, _ = weilwin.build(13, 20, kind)
            d = max(abs(Q1[i, j] - Q2[i, j]) for i in range(21) for j in range(21))
            out.setdefault('weilwin', []).append(dict(kind=kind, x=13, N=20, maxdiff=mp.nstr(d, 3)))
            print('weilwin agreement', kind, mp.nstr(d, 3), flush=True)
    except Exception as e:  # the idea's scratch code may be absent in other checkouts
        print('weilwin comparison skipped:', e)
    json.dump(out, open('validate_forms.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
