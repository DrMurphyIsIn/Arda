"""Cross-check of Galerkin horizon certificates by an INDEPENDENT evaluation (builder stage).

conjecture1_proved = False.

The Galerkin matrices (semilocal.build_form, on the validated wpw builder) are assembled from the
archimedean + pole + S-prime terms.  Here we take the bottom eigenvector c of such a matrix, form the
test g_c = sum_k c_k psi_k (odd sector: psi_k = sqrt(2/L) sin(k w t), w = 2 pi/L) and re-evaluate
its S-local value through the OTHER side of the explicit formula:

    Q_S(g_c) = sum_rho |g_c^(gamma_rho)|^2  +  2 sum_{missing n <= x} Lambda(n) n^{-1/2} h_{g_c}(log n),

zero sum over the first 2000 zeros (all verified on the critical line, so this is an evaluation, not
an assumption) plus a density tail, deficit by quadrature.  Agreement of the two numbers checks the
negative eigenvalue itself, not just the code that produced it.

Pole-free cases: the eigenvector of the restricted form (polefree.py) is used; for it A(g) = 0 and
the pole terms vanish on both sides, so the same zero-side formula applies.
"""
import json
import os
import sys
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import semilocal as sl  # noqa: E402

ZEROS = np.array(json.load(open(os.path.join(HERE, '..', 'zeros2000.json'))), dtype=float)


def vm(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return (np.log(p), p) if m == 1 else (0.0, p)
    return (0.0, None)


def odd_transform(c, L, t):
    """g^(t) = int g(u) e^{itu} du = 2i int_0^{L/2} g(u) sin(tu) du for g = sum c_k sqrt(2/L) sin(k w u)."""
    w = 2 * np.pi / L
    b = L / 2
    t = np.asarray(t, dtype=float)
    acc = np.zeros_like(t)
    for k, ck in enumerate(c, start=1):
        a = k * w
        # int_0^b sin(a u) sin(t u) du = [sin((a-t)u)/(2(a-t)) - sin((a+t)u)/(2(a+t))]_0^b
        d1 = a - t
        s1 = np.where(np.abs(d1) < 1e-12, b / 2, np.sin(d1 * b) / (2 * np.where(np.abs(d1) < 1e-12, 1, d1)))
        s2 = np.sin((a + t) * b) / (2 * (a + t))
        acc += ck * np.sqrt(2 / L) * (s1 - s2)
    return 2 * acc          # modulus of the purely imaginary value


def even_transform(c, L, t):
    """g^(t) = 2 int_0^{L/2} g(u) cos(tu) du for g = c_0 L^{-1/2} + sum_k c_k sqrt(2/L) cos(k w u)."""
    w = 2 * np.pi / L
    b = L / 2
    t = np.asarray(t, dtype=float)
    acc = c[0] / np.sqrt(L) * np.sin(t * b) / t
    for k in range(1, len(c)):
        a = k * w
        d1 = a - t
        s1 = np.where(np.abs(d1) < 1e-12, b / 2, np.sin(d1 * b) / (2 * np.where(np.abs(d1) < 1e-12, 1, d1)))
        s2 = np.sin((a + t) * b) / (2 * (a + t))
        acc = acc + c[k] * np.sqrt(2 / L) * (s1 + s2)
    return 2 * acc


def g_eval(c, L, u, sector='odd'):
    w = 2 * np.pi / L
    u = np.asarray(u, dtype=float)
    out = np.zeros_like(u)
    if sector == 'odd':
        for k, ck in enumerate(c, start=1):
            out += ck * np.sqrt(2 / L) * np.sin(k * w * u)
    else:
        out += c[0] / np.sqrt(L)
        for k in range(1, len(c)):
            out += c[k] * np.sqrt(2 / L) * np.cos(k * w * u)
    return np.where(np.abs(u) <= L / 2, out, 0.0)


def overlap(c, L, a, n=4000, sector='odd'):
    lo, hi = a - L / 2, L / 2
    if lo >= hi:
        return 0.0
    x, wt = np.polynomial.legendre.leggauss(n)
    v = 0.5 * (hi - lo) * x + 0.5 * (hi + lo)
    wt = 0.5 * (hi - lo) * wt
    return float(np.sum(wt * g_eval(c, L, v, sector) * g_eval(c, L, v - a, sector)))


def zero_side(c, L, S_primes, x, sector='odd'):
    T = ZEROS[-1]
    w = 2 * np.pi / L
    if sector == 'odd':
        G = odd_transform(c, L, ZEROS)
        # tail beyond T: |g^(t)| ~ |g'(L/2)| 2 |cos(tL/2)|/t^2 (the sine basis vanishes at the edge)
        B = abs(sum(ck * np.sqrt(2 / L) * k * w * (-1) ** k for k, ck in enumerate(c, start=1)))
        dens = lambda t: 0.5 * (2 * B) ** 2 / t ** 4
    else:
        G = even_transform(c, L, ZEROS)
        # tail beyond T: |g^(t)| ~ 2 |g(L/2)| |sin(tL/2)|/t
        gb = abs(c[0] / np.sqrt(L) + sum(c[k] * np.sqrt(2 / L) * (-1) ** k for k in range(1, len(c))))
        dens = lambda t: 0.5 * (2 * gb) ** 2 / t ** 2
    zs = 2 * np.sum(G ** 2)
    tail = 2 * float(mp.quad(lambda t: (mp.log(t / (2 * mp.pi)) / (2 * mp.pi)) * dens(t), [T, mp.inf]))
    deficit = 0.0
    for n in range(2, int(np.floor(x)) + 1):
        lam, p = vm(n)
        if lam > 0 and p not in S_primes:
            deficit += 2 * lam / np.sqrt(n) * overlap(c, L, np.log(n), sector=sector)
    return zs, tail, deficit


def pole_vector(x, N, sector):
    """A(g) for g = sum c_k basis_k is <v, c> (same formula as polefree.py, inlined because that
    script runs a scan at import time)."""
    L = mp.log(mp.mpf(x))
    om = 2 * mp.pi / L
    idx = list(range(0, N + 1)) if sector == 'even' else list(range(1, N + 1))
    a = {k: (1 / mp.sqrt(L) if k == 0 else mp.sqrt(2 / L)) for k in idx}
    if sector == 'even':
        return [a[j] * (-1) ** j * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4) for j in idx]
    return [a[j] * (-1) ** j * (j * om) * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4) for j in idx]


def case(x, P, polefree=False, N=28, dps=50, sector='odd'):
    Q, L = sl.build_form(x, N, sector, ('slocal', P), dps=dps)
    if polefree:
        v = pole_vector(x, N, sector)
        nv = mp.sqrt(sum(t * t for t in v))
        u = [t / nv for t in v]
        Pm = mp.eye(Q.rows)
        for i in range(Q.rows):
            for j in range(Q.rows):
                Pm[i, j] -= u[i] * u[j]
        Q = Pm * Q * Pm
    E, V = mp.eigsy(Q)
    idx = sorted(range(len(E)), key=lambda i: E[i])
    # skip the artificial zero eigenvalue along the pole direction in the pole-free case
    i0 = idx[0]
    lam = E[i0]
    c = np.array([float(V[r, i0]) for r in range(V.rows)])
    S_primes = [p for p in sl.primes_upto(int(P))] if P >= 2 else []
    zs, tail, deficit = zero_side(c, float(L), S_primes, x, sector)
    return dict(x=x, P=P, polefree=polefree, sector=sector, galerkin_lambda=float(lam),
                zero_sum=zs, zero_tail=tail, deficit=deficit, zero_side_QS=zs + tail + deficit)


if __name__ == '__main__':
    rows = []
    cases = [(5.06, 3, False, 'odd'), (5.1, 3, False, 'odd'), (3.08, 2, False, 'odd'), (3.13, 2, False, 'odd'),
             (7.05, 5, False, 'odd'), (7.1, 5, False, 'odd'), (2.13, 1, False, 'odd'), (2.2, 1, False, 'odd'),
             (3.3, 1, True, 'even'), (3.35, 1, True, 'even'), (3.2, 2, True, 'odd'), (3.14, 2, True, 'odd'),
             (5.1, 3, False, 'even'), (4.5, 2, True, 'even')]
    if len(sys.argv) > 1 and sys.argv[1] == 'polefree':
        cases = [c for c in cases if c[2] or c[3] == 'even']
    for (x, P, pf_, sec) in cases:
        r = case(x, P, pf_, sector=sec)
        rows.append(r)
        print(json.dumps(r), flush=True)
    json.dump(rows, open(os.path.join(HERE, 'crosscheck_galerkin_zero_side%s.json' % ('_polefree' if len(sys.argv) > 1 else '')), 'w'), indent=1)
