#!/usr/bin/env python3
"""
Weil explicit formula for zeta and Gram matrices of Weil's quadratic functional.

Exploration code only.  Nothing here is progress on RH.  conjecture1_proved = False.

CONVENTION (validated numerically by `--validate`, see WEIL_POSITIVITY_SEARCH_2026-10-11.md):

  g : R -> R, compactly supported (or Gaussian-decaying), smooth enough.
  F_g(s) = int g(x) e^{(s-1/2)x} dx,  so for rho = 1/2 + i*gamma:  F_g(rho) = h(gamma),
  h(t) = int g(x) e^{itx} dx.

  sum_rho F_g(rho)  =  W(g)  :=  POLE - PRIME - CONST + ARCH, where
     POLE  = F_g(0) + F_g(1) = int g(x) 2 cosh(x/2) dx
     PRIME = sum_{n>=2} Lambda(n) n^{-1/2} (g(log n) + g(-log n))
     CONST = (log pi + euler_gamma) g(0)
     ARCH  = int_0^inf [ 2 e^{-2x} g(0) - e^{-x/2} (g(x) + g(-x)) ] / (1 - e^{-2x}) dx
  (ARCH - CONST = (1/2pi) int h(r) [Re psi(1/4 + i r/2) - log pi] dr; derivation in the note.)

  Weil form on test functions f: B(f1, f2) = W(f1 * f2~), f2~(x) = f2(-x) (real f).
  Under RH, B(f, f) = sum_gamma |F_f(1/2 + i gamma)|^2 >= 0.

Two bases:
  * cubic B-splines on a uniform grid in [-a, a]:  phi_j(x) = M4((x - c_j)/h), h = 2a/(n+3).
    phi_j * phi_k~ (x) = h * M8((x - (c_j - c_k))/h) depends only on j-k, so G is EXACTLY Toeplitz
    (W is a translation-invariant functional of g).  Only n numbers W(h M8((x - m h)/h)) are needed.
  * Hermite functions phi_k(x) = sigma^{-1/2} psi_k(x/sigma), sigma chosen so that all n of them
    are below `tol` outside [-a, a].  Cross-correlations are displacement-operator matrix elements
    (closed form with generalized Laguerre polynomials); ARCH by Gauss-Legendre panels.
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys
import json
import math
import time
import argparse
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO_FILES = [
    os.path.join(HERE, "zeros20000.json"),  # mpmath.zetazero, 22 significant digits (zeros_compute.py)
    os.path.join(os.path.dirname(HERE), "zeros2000.json"),
]


# ----------------------------------------------------------------------------------------------
# arithmetic
# ----------------------------------------------------------------------------------------------
def prime_powers(X):
    """[(n, log p)] for prime powers n = p^k <= X."""
    X = int(math.floor(X))
    if X < 2:
        return []
    sieve = bytearray([1]) * (X + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(X ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    out = []
    for p in range(2, X + 1):
        if sieve[p]:
            q = p
            while q <= X:
                out.append((q, p))
                q *= p
    out.sort()
    return [(n, mp.log(p)) for n, p in out]


def load_zeros(nmax=None):
    for f in ZERO_FILES:
        if os.path.exists(f):
            z = json.load(open(f))
            if nmax:
                z = z[:nmax]
            return [mp.mpf(s) for s in z]
    raise FileNotFoundError("no zeros file")


# ----------------------------------------------------------------------------------------------
# B-splines
# ----------------------------------------------------------------------------------------------
_BINOM = {}


def bspline(k, x):
    """Centered cardinal B-spline of order k (degree k-1), support [-k/2, k/2], integral 1."""
    x = mp.mpf(x)
    half = mp.mpf(k) / 2
    if x <= -half or x >= half:
        return mp.mpf(0)
    if k not in _BINOM:
        _BINOM[k] = [math.comb(k, i) for i in range(k + 1)]
    s = mp.mpf(0)
    for i in range(k + 1):
        t = x + half - i
        if t > 0:
            s += (-1) ** i * _BINOM[k][i] * t ** (k - 1)
        else:
            break
    return s / math.factorial(k - 1)


def sinc(u):
    return mp.mpf(1) if u == 0 else mp.sin(u) / u


# ----------------------------------------------------------------------------------------------
# generic functional
# ----------------------------------------------------------------------------------------------
def arch_integrand(g, g0, x, arch_exp=mp.mpf(1) / 2):
    with mp.extradps(30):
        x = mp.mpf(x)
        e2 = mp.exp(-2 * x)
        return (2 * e2 * g0 - mp.exp(-arch_exp * x) * (g(x) + g(-x))) / (-mp.expm1(-2 * x))


def W_components(g, A, breaks=(), pole=None, prime_lambda=None, lfun=None):
    """Components of W(g) for g supported in [-A, A]; `breaks` = points where g is not smooth.
    prime_lambda: optional list of (n, c_n) replacing (n, Lambda(n)) (used by controls).
    lfun: None for zeta; or dict(arch_exp=, const_coef=, pole=False) for another degree-1
    self-dual L-function, e.g. Davenport-Heilbronn: arch_exp=3/2 (Gamma((s+1)/2)),
    const_coef = euler + log(pi) - log(q), no pole."""
    A = mp.mpf(A)
    g0 = g(mp.mpf(0))
    arch_exp = mp.mpf(1) / 2 if lfun is None else lfun["arch_exp"]
    const_coef = (mp.log(mp.pi) + mp.euler) if lfun is None else lfun["const_coef"]
    if lfun is not None and not lfun.get("pole", False):
        pole = mp.mpf(0)
    if pole is None:
        pts = sorted(set([-A, A] + [mp.mpf(b) for b in breaks if -A < b < A]))
        pole = mp.quad(lambda x: g(x) * 2 * mp.cosh(x / 2), pts)
    pp = prime_lambda if prime_lambda is not None else prime_powers(mp.exp(A))
    prime = mp.mpf(0)
    for n, L in pp:
        ln = mp.log(n)
        if ln >= A:
            break
        prime += L / mp.sqrt(n) * (g(ln) + g(-ln))
    const = const_coef * g0
    bp = set([mp.mpf(0), A])
    for b in breaks:
        b = abs(mp.mpf(b))
        if 0 < b < A:
            bp.add(b)
    bp = sorted(bp)
    arch = mp.quad(lambda x: arch_integrand(g, g0, x, arch_exp), bp) - g0 * mp.log(-mp.expm1(-2 * A))
    W = pole - prime - const + arch
    return dict(pole=pole, prime=prime, const=const, arch=arch, W=W)


# ----------------------------------------------------------------------------------------------
# B-spline Gram matrix (Toeplitz)
# ----------------------------------------------------------------------------------------------
def spline_entry(h, m, prime_lambda=None, lfun=None):
    """Components of W(g_m), g_m(x) = h*M8((x - m h)/h) = phi_j * phi_k~ with j - k = m."""
    h = mp.mpf(h)
    d = m * h
    g = lambda x: h * bspline(8, (x - d) / h)
    A = abs(d) + 4 * h
    breaks = [d + i * h for i in range(-4, 5)]
    S = mp.sinh(h / 4) / (h / 4)
    pole = h * h * 2 * mp.cosh(d / 2) * S ** 8
    return W_components(g, A, breaks, pole=pole, prime_lambda=prime_lambda, lfun=lfun)


def toeplitz(col):
    n = len(col)
    return mp.matrix([[col[abs(i - j)] for j in range(n)] for i in range(n)])


def spline_gram(a, n, prime_lambda=None, lfun=None):
    """Return dict of Toeplitz matrices G, POLE, PRIME, CONST, ARCH, MASS and the grid."""
    a = mp.mpf(a)
    h = 2 * a / (n + 3)
    cols = {k: [] for k in ("pole", "prime", "const", "arch", "W")}
    for m in range(n):
        c = spline_entry(h, m, prime_lambda, lfun)
        for k in cols:
            cols[k].append(c[k])
    mass = [h * bspline(8, m) for m in range(n)]
    out = {k: toeplitz(v) for k, v in cols.items()}
    out["G"] = out.pop("W")
    out["MASS"] = toeplitz(mass)
    out["cols"] = cols
    out["h"] = h
    out["centers"] = [-a + (j + 2) * h for j in range(n)]
    return out


def spline_basis_eval(a, n, x):
    a = mp.mpf(a)
    h = 2 * a / (n + 3)
    return [bspline(4, (x - (-a + (j + 2) * h)) / h) for j in range(n)]


# ----------------------------------------------------------------------------------------------
# Hermite Gram matrix
# ----------------------------------------------------------------------------------------------
def hermite_values(n, u):
    """Normalized Hermite functions psi_0..psi_{n-1} at u."""
    u = mp.mpf(u)
    v = [mp.pi ** mp.mpf(-0.25) * mp.exp(-u * u / 2)]
    if n > 1:
        v.append(mp.sqrt(2) * u * v[0])
    for k in range(1, n - 1):
        v.append(mp.sqrt(mp.mpf(2) / (k + 1)) * u * v[k] - mp.sqrt(mp.mpf(k) / (k + 1)) * v[k - 1])
    return v[:n]


def hermite_ustar(n, tol):
    """Smallest u* (grid 0.05) with max_k |psi_k(u)| <= tol for all u >= u*."""
    u = mp.sqrt(2 * n + 1)
    while True:
        if max(abs(x) for x in hermite_values(n, u)) <= tol:
            # check that it stays below beyond
            if all(max(abs(x) for x in hermite_values(n, u + t)) <= tol for t in (0.5, 1, 2, 4)):
                return u
        u += mp.mpf("0.05")


def hermite_corr(n, sigma, x):
    """C_jk(x) = int phi_j(y) phi_k(y - x) dy  (displacement-operator matrix elements)."""
    alpha = mp.mpf(x) / (sigma * mp.sqrt(2))
    t = alpha * alpha
    e = mp.exp(-t / 2)
    C = [[mp.mpf(0)] * n for _ in range(n)]
    # j = k + d, d >= 0: sqrt(k!/j!) alpha^d e^{-t/2} L_k^{(d)}(t)
    pref0 = e
    for d in range(n):
        if d > 0:
            pref0 = pref0 * alpha / mp.sqrt(d)
        pref = pref0
        Lm1, L = mp.mpf(0), mp.mpf(1)
        for k in range(n - d):
            if k == 1:
                Lm1, L = L, 1 + d - t
            elif k > 1:
                Lm1, L = L, ((2 * k - 1 + d - t) * L - (k - 1 + d) * Lm1) / k
            if k > 0:
                pref = pref * mp.sqrt(mp.mpf(k) / (k + d))
            val = pref * L
            C[k + d][k] = val
            if d:
                C[k][k + d] = val if d % 2 == 0 else -val
    return C


def hermite_moment(n, lam):
    """int psi_j(u) e^{lam u} du for j < n."""
    lam = mp.mpf(lam)
    P = [mp.mpf(1), 2 * lam]
    for j in range(1, n):
        P.append(2 * lam * P[j] + 2 * j * P[j - 1])
    c = mp.sqrt(2) * mp.pi ** mp.mpf(0.25) * mp.exp(lam * lam / 2)
    out = []
    norm = mp.mpf(1)
    for j in range(n):
        if j:
            norm *= 2 * j
        out.append(c * P[j] / mp.sqrt(norm))
    return out


_GL_CACHE = {}


def gl_nodes(q):
    """Gauss-Legendre nodes/weights on [-1,1] at current precision (Newton on P_q)."""
    key = (q, mp.mp.dps)
    if key in _GL_CACHE:
        return _GL_CACHE[key]
    xs, ws = [], []
    for i in range(1, q + 1):
        x = mp.cos(mp.pi * (i - mp.mpf(0.25)) / (q + mp.mpf(0.5)))
        for _ in range(100):
            p0, p1 = mp.mpf(1), x
            for k in range(2, q + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = q * (x * p1 - p0) / (x * x - 1)
            dx = p1 / dp
            x -= dx
            if abs(dx) < mp.mpf(10) ** (-mp.mp.dps - 5):
                break
        p0, p1 = mp.mpf(1), x
        for k in range(2, q + 1):
            p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
        dp = q * (x * p1 - p0) / (x * x - 1)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    _GL_CACHE[key] = (xs, ws)
    return xs, ws


def hermite_gram(a, n, tol=mp.mpf("1e-30"), panels=None, q=24, prime_lambda=None, verbose=False):
    a = mp.mpf(a)
    ustar = hermite_ustar(n, tol)
    sigma = a / ustar
    X = 2 * a
    # pole terms
    m0 = [mp.sqrt(sigma) * v for v in hermite_moment(n, -sigma / 2)]  # F_j(0)
    m1 = [mp.sqrt(sigma) * v for v in hermite_moment(n, sigma / 2)]   # F_j(1)
    POLE = mp.matrix(n, n)
    for j in range(n):
        for k in range(n):
            POLE[j, k] = m0[j] * m1[k] + m1[j] * m0[k]
    CONST = (mp.log(mp.pi) + mp.euler) * mp.eye(n)
    # primes
    PRIME = mp.matrix(n, n)
    pp = prime_lambda if prime_lambda is not None else prime_powers(mp.exp(X))
    for nn, L in pp:
        ln = mp.log(nn)
        if ln >= X:
            break
        C = hermite_corr(n, sigma, ln)
        w = L / mp.sqrt(nn)
        for j in range(n):
            for k in range(j, n, 2):
                v = w * (C[j][k] + C[k][j])
                PRIME[j, k] += v
                if k != j:
                    PRIME[k, j] += v
    # arch: Gauss-Legendre panels on [0, X]
    if panels is None:
        # total phase ~ X * ustar / sigma; ~1.5 rad per panel
        panels = int(mp.ceil(X * ustar / sigma / 1.5)) + 4
    xs, ws = gl_nodes(q)
    ARCH = mp.matrix(n, n)
    hp = X / (2 * panels)
    for p in range(panels):
        mid = X * (2 * p + 1) / (2 * panels)
        for xi, wi in zip(xs, ws):
            x = mid + hp * xi
            w = wi * hp
            with mp.extradps(20):
                e2 = mp.exp(-2 * x)
                den = -mp.expm1(-2 * x)
                ex = mp.exp(-x / 2)
            C = hermite_corr(n, sigma, x)
            for j in range(n):
                for k in range(j, n, 2):
                    s = C[j][k] + C[k][j]
                    if j == k:
                        with mp.extradps(20):
                            v = (2 * e2 - ex * s) / den
                    else:
                        v = -ex * s / den
                    ARCH[j, k] += w * v
    for j in range(n):
        for k in range(j + 1, n):
            ARCH[k, j] = ARCH[j, k]
        ARCH[j, j] -= mp.log(-mp.expm1(-2 * X))
    G = POLE - PRIME - CONST + ARCH
    return dict(G=G, pole=POLE, prime=PRIME, const=CONST, arch=ARCH, MASS=mp.eye(n),
                sigma=sigma, ustar=ustar, panels=panels, q=q)


def hermite_zero_side(n, sigma, zeros):
    """sum over zeros (both signs) of F_j(rho) F_k(1 - rho) for the Hermite basis, assuming RH
    for the listed zeros: 4 pi sigma sum_{gamma>0} Re(i^{j-k}) psi_j(sigma gamma) psi_k(sigma gamma)."""
    Z = mp.matrix(n, n)
    for g in zeros:
        v = hermite_values(n, sigma * g)
        for j in range(n):
            for k in range(j, n, 2):
                s = (-1) ** ((k - j) // 2) * v[j] * v[k]
                Z[j, k] += s
    for j in range(n):
        for k in range(j, n, 2):
            Z[j, k] *= 4 * mp.pi * sigma
            Z[k, j] = Z[j, k]
    return Z


# ----------------------------------------------------------------------------------------------
# linear algebra helpers
# ----------------------------------------------------------------------------------------------
def gen_eig(G, M):
    """Eigen-decomposition of the pencil (G, M), M SPD.  Returns (eigs ascending, coefficient
    vectors as columns of an mp.matrix, M-orthonormal)."""
    L = mp.cholesky(M)
    Li = mp.inverse(L)
    S = Li * G * Li.T
    n = S.rows
    for i in range(n):
        for j in range(i + 1, n):
            s = (S[i, j] + S[j, i]) / 2
            S[i, j] = S[j, i] = s
    E, Q = mp.eigsy(S)
    order = sorted(range(n), key=lambda i: E[i])
    ev = [E[i] for i in order]
    V = Li.T * Q
    Vs = mp.matrix(n, n)
    for c, i in enumerate(order):
        for r in range(n):
            Vs[r, c] = V[r, i]
    return ev, Vs


# ----------------------------------------------------------------------------------------------
# validation
# ----------------------------------------------------------------------------------------------
def zero_side_spline(s, d, zeros):
    """g(x) = M8((x-d)/s): h(t) = s e^{itd} sinc(ts/2)^8; sum over +-gamma = 2 sum Re h."""
    tot = mp.mpf(0)
    for g in zeros:
        tot += 2 * s * mp.cos(g * d) * sinc(g * s / 2) ** 8
    return tot


def tail_spline(s, T):
    """Upper bound for the zero-side tail beyond height T: int_T^inf (1/2pi) log(t/2pi) 2 s (2/(ts))^8 dt."""
    f = lambda t: mp.log(t / (2 * mp.pi)) / (2 * mp.pi) * 2 * s * (2 / (t * s)) ** 8
    return mp.quad(f, [T, mp.inf])


def bump(x):
    x = mp.mpf(x)
    if abs(x) >= 1:
        return mp.mpf(0)
    return mp.exp(-1 / (1 - x * x))


def validate(out_csv=None):
    mp.mp.dps = 40
    zeros = load_zeros()
    T = zeros[-1]
    print("zeros loaded: %d, last gamma = %s" % (len(zeros), mp.nstr(T, 15)))
    rows = []

    def report(name, comp, zs, tail):
        diff = comp["W"] - zs
        rows.append((name, mp.nstr(comp["W"], 25), mp.nstr(zs, 25), mp.nstr(diff, 5), mp.nstr(tail, 5)))
        print("%-38s W=%s  zeros=%s  diff=%s  tail<=%s" % rows[-1])

    # 1. B-spline M8 tests (exactly the Gram-entry shape), including non-even shifts
    for s, d in [(mp.mpf(1) / 4, 0), (mp.mpf(1) / 2, 0), (mp.mpf(1), 0), (mp.mpf(1) / 4, mp.mpf("0.3")),
                 (mp.mpf(1) / 2, mp.mpf("1.7")), (mp.mpf(1) / 8, mp.mpf("2.5"))]:
        g = lambda x, s=s, d=d: bspline(8, (x - d) / s)
        A = abs(d) + 4 * s
        S = mp.sinh(s / 4) / (s / 4)
        pole = s * 2 * mp.cosh(d / 2) * S ** 8
        comp = W_components(g, A, [d + i * s for i in range(-4, 5)], pole=pole)
        # check the closed-form pole against quadrature once
        zs = zero_side_spline(s, d, zeros)
        report("M8((x-%s)/%s) supp[%s,%s]" % (mp.nstr(d, 3), mp.nstr(s, 3), mp.nstr(d - 4 * s, 3), mp.nstr(d + 4 * s, 3)),
               comp, zs, tail_spline(s, T))
    # 2. C-infinity bumps on [-1,1] and [-2,2] (task's examples); zero side by quadrature at dps 40.
    for R in (1, 2):
        g = lambda x, R=R: bump(x / R)
        comp = W_components(g, R, [0])
        nz = 1000 if R == 1 else 500
        zs = mp.mpf(0)
        for gm in zeros[:nz]:
            # h(gamma) = 2 int_0^R bump(x/R) cos(gamma x) dx ; split into ~ gamma*R/pi pieces
            npc = int(gm * R / mp.pi) + 4
            pts = [R * mp.mpf(i) / npc for i in range(npc + 1)]
            zs += 2 * 2 * mp.quad(lambda x: g(x) * mp.cos(gm * x), pts)
        # crude tail bound: |h(t)| <= C exp(-sqrt(2 R t)) ; report the last term size as a proxy
        last = abs(2 * mp.quad(lambda x: g(x) * mp.cos(zeros[nz - 1] * x), [R * mp.mpf(i) / 200 for i in range(201)]))
        report("bump(x/%d) supp[-%d,%d] (%d zeros)" % (R, R, R, nz), comp, zs, last * nz)
    if out_csv:
        import csv
        with open(out_csv, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["test", "W_prime_arch_side", "zero_side", "difference", "tail_bound"])
            w.writerows(rows)
    return rows


def validate_hermite(a=1, n=24, out_csv=None):
    """Closed-form checks for the Hermite machinery + whole-matrix comparison with the zero side."""
    mp.mp.dps = 40
    tol = mp.mpf("1e-30")
    # closed forms vs quadrature
    ustar = hermite_ustar(n, tol)
    sigma = mp.mpf(a) / ustar
    phi = lambda k, y: hermite_values(k + 1, y / sigma)[k] / mp.sqrt(sigma)
    x0 = mp.mpf("0.37")
    C = hermite_corr(n, sigma, x0)
    errs = []
    for (j, k) in [(0, 0), (3, 1), (1, 3), (7, 2), (n - 1, n - 3), (5, 5)]:
        q = mp.quad(lambda y: phi(j, y) * phi(k, y - x0), mp.linspace(-2 * a, 2 * a, 41))
        errs.append(abs(q - C[j][k]))
    m0 = hermite_moment(n, mp.mpf("-0.2"))
    q = mp.quad(lambda u: hermite_values(6, u)[5] * mp.exp(mp.mpf("-0.2") * u), [-30, 0, 30])
    errs.append(abs(q - m0[5]))
    print("Hermite closed forms: max |closed - quad| = %s" % mp.nstr(max(errs), 5))
    t0 = time.time()
    H = hermite_gram(a, n, tol)
    t1 = time.time()
    zeros = load_zeros()
    Rmax = H["ustar"] / H["sigma"]
    zz = [g for g in zeros if g < Rmax + 200]
    Z = hermite_zero_side(n, H["sigma"], zz)
    D = H["G"] - Z
    md = max(abs(D[i, j]) for i in range(n) for j in range(n))
    mg = max(abs(H["G"][i, j]) for i in range(n) for j in range(n))
    print("Hermite a=%s n=%d sigma=%s u*=%s: Gram build %.1fs, zeros used %d (gamma<%s); max|G - zero side| = %s, max|G| = %s"
          % (a, n, mp.nstr(H["sigma"], 6), mp.nstr(H["ustar"], 5), t1 - t0, len(zz), mp.nstr(Rmax + 200, 6), mp.nstr(md, 5), mp.nstr(mg, 5)))
    # panel convergence check
    H2 = hermite_gram(a, n, tol, panels=H["panels"] * 2)
    dd = max(abs(H2["G"][i, j] - H["G"][i, j]) for i in range(n) for j in range(n))
    print("  quadrature check: max change on doubling panels = %s" % mp.nstr(dd, 5))
    if out_csv:
        with open(out_csv, "w") as f:
            f.write("a,n,sigma,ustar,closed_form_err,max_abs_G_minus_zero_side,max_abs_G,panel_doubling_change,zeros_used\n")
            f.write("%s,%d,%s,%s,%s,%s,%s,%s,%d\n" % (a, n, mp.nstr(H["sigma"], 10), mp.nstr(H["ustar"], 6), mp.nstr(max(errs), 5),
                                                      mp.nstr(md, 5), mp.nstr(mg, 5), mp.nstr(dd, 5), len(zz)))
    return md, dd


def validate_spline_gram(a=1, n=20, out_csv=None):
    """Whole B-spline Gram matrix vs zero side (entry m: s=h, d=m h, times h)."""
    mp.mp.dps = 40
    zeros = load_zeros()
    S = spline_gram(a, n)
    h = S["h"]
    worst = mp.mpf(0)
    lines = []
    for m in range(n):
        zs = h * zero_side_spline(h, m * h, zeros)
        diff = S["cols"]["W"][m] - zs
        worst = max(worst, abs(diff))
        lines.append((m, mp.nstr(S["cols"]["W"][m], 20), mp.nstr(zs, 20), mp.nstr(diff, 4)))
    tail = h * tail_spline(h, zeros[-1])
    print("spline Gram a=%s n=%d h=%s: max |entry - zero side| = %s (tail bound %s)" % (a, n, mp.nstr(h, 6), mp.nstr(worst, 5), mp.nstr(tail, 5)))
    if out_csv:
        with open(out_csv, "w") as f:
            f.write("m,W_entry,zero_side,difference\n")
            for l in lines:
                f.write("%d,%s,%s,%s\n" % l)
    return worst, tail


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--validate", action="store_true")
    args = ap.parse_args()
    if args.validate:
        validate(os.path.join(HERE, "results", "validation_explicit_formula.csv"))
        validate_spline_gram(1, 20, os.path.join(HERE, "results", "validation_spline_gram.csv"))
        validate_hermite(1, 24, os.path.join(HERE, "results", "validation_hermite_gram.csv"))
