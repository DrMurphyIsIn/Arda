"""Common machinery for Guinand-Weil explicit-formula checks (single process, mpmath).

Convention (self-dual F with real coefficients, completion Phi = R * gamma * F, Phi(s) = Phi(1-s)):
  zeros rho <-> gamma_rho = (rho - 1/2)/i  (complex when rho is off the line)
  h even, entire, Gaussian-type;  hhat(x) = int h(r) e^{-irx} dr  (even)
  SUM_rho h(gamma_rho) = m*[h(i/2)+h(-i/2)] + (1/pi) int_R h(r) A(r) dr
                         - (1/pi) SUM_{n>=2} Lambda_F(n) n^{-1/2} hhat(log n)
  where A(r) = Re (gamma'/gamma)(1/2+ir), m = order of the pole of F at s=1 (killed by R).
Test function: h(r) = exp(-(r-T)^2/(2w^2)) + exp(-(r+T)^2/(2w^2)),
               hhat(x) = 2 w sqrt(2 pi) cos(T x) exp(-w^2 x^2/2).
"""
import mpmath as mp


def make_h(T, w):
    T = mp.mpf(T); w = mp.mpf(w)
    def h(z):
        return mp.exp(-(z - T) ** 2 / (2 * w * w)) + mp.exp(-(z + T) ** 2 / (2 * w * w))
    def hhat(x):
        return 2 * w * mp.sqrt(2 * mp.pi) * mp.cos(T * x) * mp.exp(-w * w * x * x / 2)
    return h, hhat


def arch_term(h, A, T, w, halfwidth=14):
    """(1/pi) * int_R h(r) A(r) dr, with h concentrated near +-T; A even."""
    T = mp.mpf(T); w = mp.mpf(w)
    a, b = T - halfwidth * w, T + halfwidth * w
    pts = [a + (b - a) * k / 28 for k in range(29)]
    if a > 0:
        I = 2 * mp.quad(lambda r: h(r) * A(r), pts)  # two bumps, A even, h even
        # contribution of the far tails / cross terms is < exp(-halfwidth^2/2) * max|A|
        return I / mp.pi
    # centered bump: integrate symmetric range
    lo = -(abs(T) + halfwidth * w)
    pts = [lo + (-2 * lo) * k / 56 for k in range(57)]
    return mp.quad(lambda r: h(r) * A(r), pts) / mp.pi


def prime_term(Lam, hhat, N):
    """-(1/pi) sum_{n=2}^{N} Lam[n] n^{-1/2} hhat(log n); Lam: dict or list."""
    s = mp.mpf(0)
    if isinstance(Lam, dict):
        it = Lam.items()
    else:
        it = ((n, Lam[n]) for n in range(2, min(N, len(Lam) - 1) + 1))
    for n, L in it:
        if n < 2 or n > N or L == 0:
            continue
        s += L * mp.power(n, -0.5) * hhat(mp.log(n))
    return -s / mp.pi


def vonmangoldt_list(N):
    Lam = [mp.mpf(0)] * (N + 1)
    sieve = [True] * (N + 1)
    for p in range(2, N + 1):
        if sieve[p]:
            for q in range(p * p, N + 1, p):
                sieve[q] = False
            lp = mp.log(p)
            pk = p
            while pk <= N:
                Lam[pk] = lp
                pk *= p
    return Lam


def log_deriv_coeffs(a, N):
    """Lambda_F(n) for F = sum a[n] n^{-s}, a[1] = 1, via a(n) log n = sum_{d|n} Lambda(d) a(n/d)."""
    Lam = [mp.mpf(0)] * (N + 1)
    divs = [[] for _ in range(N + 1)]
    for d in range(2, N + 1):
        for m in range(d, N + 1, d):
            divs[m].append(d)
    for n in range(2, N + 1):
        s = a[n] * mp.log(n)
        for d in divs[n]:
            if d < n:
                s -= Lam[d] * a[n // d]
        Lam[n] = s  # a[1] = 1
    return Lam


def zero_sum(h, zeros_upper):
    """zeros_upper: list of complex zeros rho with Im rho > 0 (each off-line quadruple contributes
    rho and 1-conj(rho)). Returns SUM over ALL zeros (both half planes) of h(gamma), h even."""
    s = mp.mpf(0)
    for rho in zeros_upper:
        g = (mp.mpc(rho) - mp.mpf(1) / 2) / mp.j
        s += h(g) + h(-g)
    return s
