"""Semi-local Weil window forms.

Q_S^F on L^2[-L/2, L/2], L = log x, in both parity sectors, built on the validated wpw.build
(spectral-operator lens; reproduces CCM's zeta table to 2e-34).  We only change the arithmetic data:

  * 'zeta'          : Lambda(n) for all n <= x                      (full Weil form of zeta)
  * S-local, S=S(P) : Lambda(n) only for n = p^k with p <= P          (primes > P deleted)
  * surgery fake F = zeta * E_{p0,c},  E = 1 + c p0^{-s} + p0^{1-2s}:
        Lambda_F(p0^k) = log p0 (1 - b1^k - b2^k),  b1 + b2 = -c, b1 b2 = p0,
        conductor p0^2  ->  + 2 log p0 * Id   (orthonormal basis)
    golden fake / H4 / W1(5,5) all have the same zero set  zeros(xi) u zeros(2cosh((s-1/2)log5)+sqrt5)
    hence the same Weil form: this is (p0, c) = (5, 5).

Weil form convention (wpw): W_F(f^* * f) = pole + arch - sum_n Lambda_F(n) n^{-1/2} (f(log n) + f(-log n)),
equal to sum_rho F^(g_rho) conj F^(conj g_rho) by the explicit formula.
"""
import mpmath as mp
import wpw


def primes_upto(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return [i for i in range(n + 1) if s[i]]


def lam_zeta(nmax):
    return wpw.von_mangoldt(nmax)


def lam_slocal(nmax, P):
    lam = wpw.von_mangoldt(nmax)
    out = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        if lam[n] != 0:
            # n = p^k ; p = exp(lam)
            p = int(mp.nint(mp.exp(lam[n])))
            if p <= P:
                out[n] = lam[n]
    return out


def surgery_roots(p0, c):
    p0 = mp.mpf(p0)
    c = mp.mpf(c)
    disc = c * c - 4 * p0
    if disc >= 0:
        r = mp.sqrt(disc)
        return (-c + r) / 2, (-c - r) / 2
    r = mp.sqrt(-disc)
    return mp.mpc(-c / 2, r / 2), mp.mpc(-c / 2, -r / 2)


def lam_surgery(nmax, p0, c, base=None):
    lam = wpw.von_mangoldt(nmax) if base is None else list(base)
    b1, b2 = surgery_roots(p0, c)
    lp = mp.log(p0)
    k, n = 1, p0
    while n <= nmax:
        val = lp * (-(b1 ** k) - (b2 ** k))
        lam[n] = lam[n] + mp.re(val)
        k += 1
        n *= p0
    return lam


def build_form(x, N, sector, arith, dps=50, panels=None):
    """arith: ('zeta',) | ('slocal', P) | ('surgery', p0, c) | ('surgery_slocal', p0, c, P)"""
    mp.mp.dps = dps
    x = mp.mpf(x)
    nmax = int(mp.floor(x))
    shift = mp.mpf(0)
    if arith[0] == 'zeta':
        Lam = lam_zeta(nmax)
    elif arith[0] == 'slocal':
        Lam = lam_slocal(nmax, arith[1])
    elif arith[0] == 'surgery':
        Lam = lam_surgery(nmax, arith[1], arith[2])
        shift = 2 * mp.log(arith[1])
    elif arith[0] == 'surgery_slocal':
        base = lam_slocal(nmax, arith[3])
        Lam = lam_surgery(nmax, arith[1], arith[2], base=base) if arith[1] <= arith[3] else base
        shift = 2 * mp.log(arith[1])
    else:
        raise ValueError(arith)
    Q, L = wpw.build(x, N, 'zeta', sector, Lam=Lam, panels=panels)
    if shift != 0:
        for i in range(Q.rows):
            Q[i, i] += shift
    return Q, L


def eigs(Q):
    E = mp.eigsy(Q, eigvals_only=True)
    return sorted(E)


def eigpairs(Q):
    E, V = mp.eigsy(Q)
    idx = sorted(range(len(E)), key=lambda i: E[i])
    return [E[i] for i in idx], [[V[r, i] for r in range(V.rows)] for i in idx]
