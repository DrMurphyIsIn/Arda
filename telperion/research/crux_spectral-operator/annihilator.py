"""Annihilator lemma, numerically: the truncated Polya kernel is a near-null vector of the window form.

zeta:  Phi(u) = sum_n (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) exp(-pi n^2 e^{2u}),  Phi^ = Xi.
DH:    Phi_D(u) = 2 e^{3u/2} sum_n c(n) n exp(-pi n^2 e^{2u}/5),                  Phi_D^ = Xi_D.
Both are even.  Phi_x = Phi restricted to [-L/2, L/2].  Its transform is Xi minus the transform
of the tail, which is O(x^{9/4} e^{-pi x}) (zeta) or O(x^{3/4} e^{-pi x/5}) (DH); since Xi
vanishes at every zero, the explicit formula gives QW_x(Phi_x) = O(poly(x) e^{-2 pi x}) resp.
O(poly(x) e^{-2 pi x/5}) with no hypothesis on the zeros.  Hence lambda_1(x) <= QW_x(Phi_x)/|Phi_x|^2.

We compute the Rayleigh quotient of the Galerkin projection P_N Phi_x (an upper bound for the
Galerkin lambda_1, hence for the true lambda_1), and compare with lambda_1 and with the scale.

usage: python3 annihilator.py
"""
import json
import mpmath as mp
import wpw


def phi_zeta(u):
    y = mp.exp(2 * u)
    s = mp.mpf(0)
    n = 1
    while True:
        t = (2 * mp.pi ** 2 * n ** 4 * mp.exp(9 * u / 2) - 3 * mp.pi * n ** 2 * mp.exp(5 * u / 2)) * mp.exp(-mp.pi * n * n * y)
        s += t
        if abs(t) < mp.mpf(10) ** (-mp.mp.dps - 5) and n > 2:
            break
        n += 1
    return s


def phi_dh(u):
    y = mp.exp(2 * u)
    s = mp.mpf(0)
    n = 1
    while True:
        t = wpw.c_dh(n) * n * mp.exp(-mp.pi * n * n * y / 5)
        s += t
        if n > 6 and mp.exp(-mp.pi * n * n * y / 5) * n < mp.mpf(10) ** (-mp.mp.dps - 5):
            break
        n += 1
    return 2 * mp.exp(3 * u / 2) * s


def coeffs(phi, L, N):
    """Even-basis coefficients of Phi restricted to the window (Phi even: integrate over [0, L/2])."""
    om = 2 * mp.pi / L
    h = L / 2
    pts = [0, h / 4, h / 2, 3 * h / 4, h]
    c = [2 * mp.quad(phi, pts) / mp.sqrt(L)]
    for k in range(1, N + 1):
        c.append(2 * mp.sqrt(2 / L) * mp.quad(lambda u: phi(u) * mp.cos(k * om * u), pts))
    return c


def run(kind, x, N, dps):
    mp.mp.dps = dps
    phi = phi_zeta if kind == 'zeta' else phi_dh
    even_err = abs(phi(mp.mpf('0.3')) - phi(mp.mpf('-0.3'))) / abs(phi(mp.mpf('0.3')))
    Q, L = wpw.build(x, N, kind, 'even')
    c = coeffs(phi, L, N)
    num = mp.fsum(c[i] * mp.fsum(Q[i, j] * c[j] for j in range(N + 1)) for i in range(N + 1))
    den = mp.fsum(t * t for t in c)
    full = 2 * mp.quad(lambda u: phi(u) ** 2, [0, L / 4, L / 2])
    E = sorted(mp.eigsy(Q, eigvals_only=True))
    scale = mp.exp(-2 * mp.pi * mp.mpf(x)) if kind == 'zeta' else mp.exp(-2 * mp.pi * mp.mpf(x) / 5)
    row = dict(kind=kind, x=x, N=N, dps=dps, evenness_rel_err=mp.nstr(even_err, 3),
               rayleigh_PN_Phi_x=mp.nstr(num / den, 6), lambda1=mp.nstr(E[0], 6),
               scale_e_minus_2pix=mp.nstr(scale, 4), rayleigh_over_scale=mp.nstr(num / den / scale, 4),
               norm_captured=mp.nstr(den / full, 20))
    print(json.dumps(row), flush=True)
    return row


if __name__ == '__main__':
    rows = []
    for (kind, x, N, dps) in [('zeta', 9, 30, 80), ('zeta', 13, 40, 100), ('zeta', 20, 50, 120),
                              ('dh', 20, 40, 100), ('dh', 25, 50, 110), ('dh', 30, 60, 120),
                              ('dh', 40, 60, 120)]:
        rows.append(run(kind, x, N, dps))
    json.dump(rows, open('annihilator.json', 'w'), indent=1)
