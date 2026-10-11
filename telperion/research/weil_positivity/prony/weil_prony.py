"""weil_prony.py -- recover zeta ordinates from the PRIME side of Weil's explicit formula.

SEARCH FOR STRUCTURE, NOT A PROOF.  Nothing here is progress on RH; conjecture1_proved = False.

Conventions (validated numerically in validate_explicit_formula()):
  g compactly supported in [-A, A], continuous;  h(r) := ghat(r) := int g(x) e^{irx} dx,
  F(s) := int g(x) e^{(s-1/2)x} dx, so F(1/2 + i r) = h(r), F(0) = h(i/2), F(1) = h(-i/2).
  ZERO SIDE   Z(g) := sum_rho F(rho) = sum_{gamma} h(gamma)   (gamma over ordinates, both signs,
                                                                with multiplicity; rho = 1/2 + i gamma)
  PRIME SIDE  W(g) := F(0) + F(1) + g(0) log(q/pi) + Arch_k(g)
                     - sum_n c(n) n^{-1/2} (g(log n) + g(-log n))
  for zeta: c = Lambda, q = 1, kappa = 1/4, pole term present.
  Arch_k(g) := (1/2pi) int h(r) Re psi(kappa + i r/2) dr
             = -gamma_E g(0) + int_0^inf [2 g(0) e^{-2x} - (g(x)+g(-x)) e^{-2 kappa x}] / (1-e^{-2x}) dx
  (x-space form from Gauss' integral for psi; kappa = 1/4 for zeta, 3/4 for odd characters / DH.)
  The prompt's "archimedean term" is  g(0) log(pi) - Arch_{1/4}(g).

Fourier basis on [-a, a]:  phi_j(x) = (2a)^{-1/2} e^{i pi j x / a},  j = -N..N,  omega := pi/a.
  u_j(gamma) := phihat_j(gamma) = sqrt(2a) sinc(gamma a + pi j)  (sinc t = sin t / t)
             = sqrt(2a) (-1)^j sin(gamma a) / (gamma a + pi j)        [a CAUCHY vector, not Vandermonde]
  g_jk := phi_j * conj(phi_k(-.))  supported in [-2a, 2a]; ghat_jk = u_j u_k (real).
  G_jk := W(g_jk) = sum_gamma u_j(gamma) u_k(gamma).  G is REAL symmetric.
  Closed form (derived in the note):  with E_jk the even part of g_jk on [0, 2a],
     j != k, d = j-k :  G_jk = (-1)^d (T(k) - T(j)) / (pi d)                       [LOEWNER matrix]
        T(m) := 2 P C(m) - S_k(m) - Ps(m)
        C(m)  = int_0^{2a} sin(m w x) cosh(x/2) dx = -m w (cosh a - 1) / (m^2 w^2 + 1/4)
        S_k(m)= int_0^{2a} sin(m w x) e^{-2 kappa x} / (1 - e^{-2x}) dx
        Ps(m) = sum_{n <= e^{2a}} c(n) n^{-1/2} sin(m w log n)
     j == k :  G_kk = P D1(k) + log(q/pi) - gamma_E - log(1 - e^{-4a}) + D2_k(k) - 2 Pc(k)
        D1(k) = 4 int_0^{2a} (1 - x/2a) cos(k w x) cosh(x/2) dx
        D2(k) = int_0^{2a} [2e^{-2x} - 2(1-x/2a) cos(k w x) e^{-2 kappa x}] / (1-e^{-2x}) dx
        Pc(k) = sum c(n) n^{-1/2} (1 - log n / 2a) cos(k w log n)
  (P = 1 if the form has the zeta pole term F(0)+F(1), else 0.)
  First-moment matrix (W applied to i g_jk'), zero side sum_gamma gamma u_j u_k:
     j != k :  K_jk = -(-1)^d (k T(k) - j T(j)) / (a d)
     j == k :  K_kk = T(k)/a - k w G_kk
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, json, time, math
import numpy as np
import mpmath as mp
import scipy.linalg as sla
import scipy.optimize as sopt
import scipy.integrate as sint

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = "/private/tmp/claude-0/-Users-peterwmurphy/d468a49a-41a3-402a-a634-199ecc771fa2/scratchpad/weil_prony"
EULER = float(mp.euler)

# ----------------------------------------------------------------------------- arithmetic

def mangoldt(M):
    """Lambda(n) for n = 0..M as float array (exact log p)."""
    lam = np.zeros(M + 1)
    sieve = np.ones(M + 1, bool); sieve[:2] = False
    for p in range(2, int(M ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    for p in np.nonzero(sieve)[0]:
        lp = math.log(p); q = p
        while q <= M:
            lam[q] = lp; q *= p
    return lam


def chi_mod4(n):
    n = np.asarray(n); r = n % 4
    return np.where(r == 1, 1.0, np.where(r == 3, -1.0, 0.0))


def chi_mod3(n):
    n = np.asarray(n); r = n % 3
    return np.where(r == 1, 1.0, np.where(r == 2, -1.0, 0.0))


DH_KAPPA = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)


def dh_coeffs(M):
    """Davenport-Heilbronn f(s) = sum a(n) n^{-s}, a(n) = Re chi(n) + kappa Im chi(n), chi mod 5 with chi(2) = i.
    Returns a (n=0..M) and b with -f'/f(s) = sum b(n) n^{-s} (Dirichlet-series log-derivative, via
    a(n) log n = sum_{d|n} b(d) a(n/d), a(1) = 1)."""
    chi_vals = {0: 0j, 1: 1, 2: 1j, 4: -1, 3: -1j}   # 2^0=1,2^1=2,2^2=4,2^3=3 (mod 5)
    n = np.arange(M + 1)
    cv = np.array([chi_vals[int(r)] for r in range(5)])[n % 5]
    a = cv.real + DH_KAPPA * cv.imag
    a[0] = 0.0
    b = np.zeros(M + 1)
    logn = np.log(np.maximum(n, 1))
    acc = a * logn
    for d in range(1, M + 1):
        b[d] = acc[d]                     # all proper-divisor contributions already subtracted
        if b[d] != 0.0 and 2 * d <= M:
            # subtract b(d) a(m/d) from acc[m] for m = 2d, 3d, ...
            acc[2 * d::d] -= b[d] * a[2:M // d + 1]
    return a, b


# ----------------------------------------------------------------------------- forms

class Form:
    """A 'prime-side' quadratic form: coefficients c(n) (n=0..M), pole flag, conductor q, kappa."""
    def __init__(self, name, c, pole=True, q=1.0, kappa=0.25):
        self.name, self.c, self.pole, self.q, self.kappa = name, np.asarray(c, float), pole, q, kappa


def zeta_form(M):
    return Form("zeta", mangoldt(M), True, 1.0, 0.25)


# ----------------------------------------------------------------------------- explicit formula (mpmath)

def cos4_window(A):
    """g(x) = cos^4(pi x / 2A) on [-A, A]: even, C^3, ghat ~ r^-5. Returns (g, ghat) as mp functions."""
    A = mp.mpf(A)
    def g(x):
        x = mp.mpf(x)
        return mp.cos(mp.pi * x / (2 * A)) ** 4 if abs(x) <= A else mp.mpf(0)
    def ghat(r):
        r = mp.mpf(r) if not isinstance(r, mp.mpc) else r
        w = mp.pi / A
        # cos^4 = 3/8 + cos(w x)/2 + cos(2 w x)/8 ; int_{-A}^{A} cos(c x) cos(r x) dx
        def I(c):
            def piece(t):
                return 2 * A if t == 0 else 2 * mp.sin(t * A) / t
            return (piece(r - c) + piece(r + c)) / 2
        return mp.mpf(3) / 8 * I(0) + I(w) / 2 + I(2 * w) / 8
    return g, ghat


def prime_side_mp(g, A, form, Mmax=None):
    """W(g) at mp precision for even g supported in [-A, A]."""
    g0 = g(0)
    F01 = mp.quad(lambda x: 2 * g(x) * 2 * mp.cosh(x / 2), mp.linspace(0, A, 9)) if form.pole else mp.mpf(0)
    kap = mp.mpf(form.kappa)
    def ai(x):
        return (2 * g0 * mp.exp(-2 * x) - 2 * g(x) * mp.exp(-2 * kap * x)) / (-mp.expm1(-2 * x))
    arch = -mp.euler * g0 + mp.quad(ai, mp.linspace(0, A, 9)) - g0 * mp.log(-mp.expm1(-2 * mp.mpf(A)))
    M = int(math.floor(math.exp(A)))
    ps = mp.mpf(0)
    for n in np.nonzero(form.c[:M + 1])[0]:
        n = int(n)
        cn = mp.log(int(round(math.exp(form.c[n])))) if form.name == "zeta" else mp.mpf(form.c[n])  # exact log p
        ps += cn / mp.sqrt(n) * 2 * g(mp.log(n))
    return F01 + g0 * mp.log(mp.mpf(form.q) / mp.pi) + arch - ps, dict(F01=F01, arch=arch, primes=ps)


def arch_r_form(ghat, kappa=0.25, R=400):
    """(1/2pi) int ghat(r) Re psi(kappa + i r/2) dr, by direct quadrature in r (cross-check of x-form)."""
    f = lambda r: ghat(r) * mp.re(mp.digamma(mp.mpf(kappa) + 1j * r / 2))
    pts = mp.linspace(0, R, 401)
    val = mp.quad(f, pts)
    return 2 * val / (2 * mp.pi)   # even integrand


def validate_explicit_formula(zeros, out_lines, As=(2.0, 6.0, 12.0)):
    mp.mp.dps = 40
    lam = mangoldt(int(math.exp(max(As))) + 2)
    form = Form("zeta", lam)
    res = []
    for A in As:
        g, gh = cos4_window(A)
        W, parts = prime_side_mp(g, A, form)
        zs = mp.mpf(0)
        for gam in zeros:
            zs += 2 * gh(mp.mpf(gam))
        T = zeros[-1]
        # tail bound: |ghat(r)| <= C r^-5 ; use density integral with |ghat| envelope
        env = abs(gh(mp.mpf(T))) if True else 0
        res.append((A, W, zs, W - zs))
        out_lines.append(f"A={A:5.1f}  prime side W = {mp.nstr(W, 25)}   zero side (K={len(zeros)}) = {mp.nstr(zs, 25)}   diff = {mp.nstr(W - zs, 5)}")
        out_lines.append(f"         parts: F(0)+F(1) = {mp.nstr(parts['F01'], 20)}  Arch = {mp.nstr(parts['arch'], 20)}  primes = {mp.nstr(parts['primes'], 20)}")
    # cross-check archimedean x-form vs r-form at A = 2
    mp.mp.dps = 25
    g, gh = cos4_window(2.0)
    g0 = g(0)
    ax = -mp.euler * g0 + mp.quad(lambda x: (2 * g0 * mp.exp(-2 * x) - 2 * g(x) * mp.exp(-x / 2)) / (-mp.expm1(-2 * x)), mp.linspace(0, 2, 9)) - g0 * mp.log(-mp.expm1(-mp.mpf(4)))
    ar = arch_r_form(gh, 0.25, R=600)
    out_lines.append(f"Arch x-form vs r-form (A=2, r-integral truncated at 600): {mp.nstr(ax, 18)} vs {mp.nstr(ar, 18)}  diff {mp.nstr(ax - ar, 5)}")
    mp.mp.dps = 40
    return res


# ----------------------------------------------------------------------------- Gram matrix (Fourier basis)

def _gl(n, lo, hi):
    x, w = np.polynomial.legendre.leggauss(n)
    return (hi - lo) / 2 * x + (hi + lo) / 2, (hi - lo) / 2 * w


def families(a, N, form):
    """T(m), diag G_kk, and Pc/Ps pieces for m, k = 0..N (double precision; integrals by composite GL)."""
    w = math.pi / a
    L = 2 * a
    M = int(math.floor(math.exp(L)))
    c = form.c[:M + 1]
    nz = np.nonzero(c)[0]
    cn = c[nz] / np.sqrt(nz)
    ln = np.log(nz)
    # composite Gauss-Legendre on [0, 2a]: panels of width <= 0.25 and <= quarter period
    npan = int(max(32, math.ceil(L / 0.25), 4 * N + 8))
    xs, ws = [], []
    for p in range(npan):
        x, wt = _gl(24, L * p / npan, L * (p + 1) / npan)
        xs.append(x); ws.append(wt)
    x = np.concatenate(xs); wq = np.concatenate(ws)
    den = -np.expm1(-2 * x)
    ek = np.exp(-2 * form.kappa * x)
    m = np.arange(0, N + 1)
    S = np.array([np.sum(wq * np.sin(mm * w * x) * ek / den) for mm in m])
    C = -m * w * (math.cosh(a) - 1) / (m ** 2 * w ** 2 + 0.25)
    Ps = np.array([math.fsum(cn * np.sin(mm * w * ln)) for mm in m])
    T = (2 * C if form.pole else 0 * C) - S - Ps
    D1 = np.array([np.sum(wq * 4 * (1 - x / L) * np.cos(k * w * x) * np.cosh(x / 2)) for k in m])
    D2 = np.array([np.sum(wq * (2 * np.exp(-2 * x) - 2 * (1 - x / L) * np.cos(k * w * x) * ek) / den) for k in m])
    Pc = np.array([math.fsum(cn * (1 - ln / L) * np.cos(k * w * ln)) for k in m])
    diag = (D1 if form.pole else 0 * D1) + math.log(form.q / math.pi) - EULER - math.log(-math.expm1(-2 * L)) + D2 - 2 * Pc
    return dict(T=T, diag=diag, S=S, C=C, Ps=Ps, D1=D1, D2=D2, Pc=Pc, M=M)


def gram_from_families(a, N, fam):
    """Assemble G and K (indices j = -N..N) from T (odd in m) and diag (even in k)."""
    js = np.arange(-N, N + 1)
    Tm = np.where(js >= 0, fam["T"][np.abs(js)], -fam["T"][np.abs(js)])
    Dg = fam["diag"][np.abs(js)]
    J, Kk = np.meshgrid(js, js, indexing="ij")
    d = J - Kk
    TJ, TK = Tm[:, None], Tm[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        G = np.where(d != 0, (-1.0) ** np.abs(d) * (TK - TJ) / (math.pi * d), 0.0)
        K = np.where(d != 0, -(-1.0) ** np.abs(d) * (Kk * TK - J * TJ) / (a * d), 0.0)
    G[np.diag_indices_from(G)] = Dg
    w = math.pi / a
    K[np.diag_indices_from(K)] = Tm / a - js * w * Dg
    return G, K, js


def gram(a, N, form):
    fam = families(a, N, form)
    G, K, js = gram_from_families(a, N, fam)
    return G, K, js, fam


def atoms(gam, a, js):
    """u(gamma) columns, gamma array (real or complex)."""
    gam = np.atleast_1d(gam)
    t = gam[None, :] * a + math.pi * js[:, None]
    with np.errstate(divide="ignore", invalid="ignore"):
        s = np.where(np.abs(t) < 1e-12, 1.0, np.sin(t) / np.where(t == 0, 1, t))
    return math.sqrt(2 * a) * s


def gram_zero_side(zeros, a, js, with_K=True):
    """sum over +-gamma of u u^T (and gamma u u^T), plus smooth-density tail beyond the last zero."""
    U = atoms(np.asarray(zeros), a, js)
    Um = U[::-1, :]          # u(-gamma)_j = u(gamma)_{-j}
    G = U @ U.T + Um @ Um.T
    K = (U * zeros) @ U.T - (Um * zeros) @ Um.T if with_K else None
    # tail: density (1/2pi) log(t/2pi), sin^2 averaged to 1/2
    T0 = zeros[-1] + 0.5 * (zeros[-1] - zeros[-2])
    def tail_entry(j, k, moment):
        def f(t):
            base = 2 * a * 0.5 * (-1.0) ** (j + k)
            p = base / ((t * a + math.pi * j) * (t * a + math.pi * k))
            q = base / ((t * a - math.pi * j) * (t * a - math.pi * k))
            dens = math.log(t / (2 * math.pi)) / (2 * math.pi)
            return dens * ((p + q) if moment == 0 else t * (p - q))
        v, _ = sint.quad(f, T0, np.inf, limit=200)
        return v
    # boundary correction: smooth count N0(T) = theta(T)/pi + 1 vs the K zeros actually summed
    th = float(mp.siegeltheta(T0))
    dN = th / math.pi + 1 - len(zeros)
    def f_at(j, k, moment, t):
        base = 2 * a * 0.5 * (-1.0) ** (j + k)
        p = base / ((t * a + math.pi * j) * (t * a + math.pi * k))
        q = base / ((t * a - math.pi * j) * (t * a - math.pi * k))
        return (p + q) if moment == 0 else t * (p - q)
    n = len(js)
    Gt = np.zeros((n, n)); Kt = np.zeros((n, n))
    for i in range(n):
        for k in range(i, n):
            Gt[i, k] = Gt[k, i] = tail_entry(js[i], js[k], 0) - dN * f_at(js[i], js[k], 0, T0)
            if with_K:
                Kt[i, k] = Kt[k, i] = tail_entry(js[i], js[k], 1) - dN * f_at(js[i], js[k], 1, T0)
    return G + Gt, (K + Kt if with_K else None), Gt


# ----------------------------------------------------------------------------- recovery

def music(G, a, js, m, gmax, step=0.01):
    """MUSIC with exact (sinc) steering vectors; returns refined local minima of noise-projection."""
    ev, V = np.linalg.eigh(G)
    order = np.argsort(-np.abs(ev))
    Us = V[:, order][:, :m]
    ev = ev[order]
    def P(g):
        u = atoms(np.array([g]), a, js)[:, 0]
        u = u / np.linalg.norm(u)
        return 1.0 - np.sum((Us.T @ u) ** 2)
    grid = np.arange(0.2, gmax, step)
    U = atoms(grid, a, js); U /= np.linalg.norm(U, axis=0)
    p = 1.0 - np.sum((Us.T @ U) ** 2, axis=0)
    idx = [i for i in range(1, len(p) - 1) if p[i] <= p[i - 1] and p[i] <= p[i + 1]]
    out = []
    for i in idx:
        r = sopt.minimize_scalar(P, bracket=(grid[i - 1], grid[i], grid[i + 1]), tol=1e-14)
        out.append((r.x, r.fun))
    return np.array(out).reshape(-1, 2), ev


def esprit_loewner(G, a, js, m):
    """Cauchy/Loewner 'ESPRIT': (gamma I + Omega) D u(gamma) = s(gamma) 1  =>  eigenvalues of
    -(P U)^+ (P Omega U) on the m-dim dominant subspace of D G D are the atom frequencies gamma."""
    w = math.pi / a
    D = np.diag((-1.0) ** np.abs(js))
    ev, V = np.linalg.eigh(D @ G @ D)
    U = V[:, np.argsort(-np.abs(ev))][:, :m]     # rank by |eigenvalue|: keep negative directions too
    n = len(js)
    P = np.eye(n) - np.ones((n, n)) / n
    Om = np.diag(w * js)
    A = P @ U; B = P @ Om @ U
    H = -np.linalg.lstsq(A, B, rcond=None)[0]
    return np.linalg.eigvals(H)


def fit_weights(G, a, js, gams):
    """LS weights for atoms u(g)u(g)^T + u(-g)u(-g)^T (one weight per positive ordinate)."""
    iu = np.triu_indices(len(js))
    cols = []
    for g in gams:
        u = atoms(np.array([g]), a, js)[:, 0]; um = u[::-1]
        cols.append((np.outer(u, u) + np.outer(um, um))[iu])
    Amat = np.array(cols).T
    wts, *_ = np.linalg.lstsq(Amat, G[iu], rcond=None)
    return wts


def nnls_fit(G, a, js, gmax, step=0.02):
    iu = np.triu_indices(len(js))
    grid = np.arange(0.5, gmax, step)
    U = atoms(grid, a, js); Um = U[::-1, :]
    A = np.empty((len(iu[0]), len(grid)))
    for c in range(len(grid)):
        A[:, c] = (np.outer(U[:, c], U[:, c]) + np.outer(Um[:, c], Um[:, c]))[iu]
    wts, rn = sopt.nnls(A, G[iu], maxiter=50 * len(grid))
    # merge clusters of contiguous nonzero weights
    nzi = np.nonzero(wts > 1e-6)[0]
    clusters = []
    for i in nzi:
        if clusters and i - clusters[-1][-1] <= 2:
            clusters[-1].append(i)
        else:
            clusters.append([i])
    out = []
    for cl in clusters:
        W = wts[cl].sum()
        out.append((float(np.sum(grid[cl] * wts[cl]) / W), float(W)))
    return out, rn


def lanczos(G, v0, k):
    n = len(v0)
    Q = np.zeros((n, k + 1)); al = np.zeros(k); be = np.zeros(k)
    q = v0 / np.linalg.norm(v0); Q[:, 0] = q
    for i in range(k):
        z = G @ Q[:, i]
        al[i] = Q[:, i] @ z
        z -= Q[:, :i + 1] @ (Q[:, :i + 1].T @ z)
        z -= Q[:, :i + 1] @ (Q[:, :i + 1].T @ z)
        be[i] = np.linalg.norm(z)
        if be[i] < 1e-14:
            return al[:i + 1], be[:i + 1]
        Q[:, i + 1] = z / be[i]
    return al, be




# ----------------------------------------------------------------------------- tapering, Ritz, mp Gram

def taper_basis(js, p):
    """Orthonormal basis of {x : sum_j (-1)^j j^r x_j = 0, r < p} = trig polys on [-a,a] vanishing to
    order p at the endpoints; atoms restricted to it decay like gamma^{-(p+1)} out of band."""
    if p == 0:
        return np.eye(len(js))
    C = np.array([((-1.0) ** np.abs(js)) * (js.astype(float) ** r) for r in range(p)])
    return sla.null_space(C)


def music_Q(G, a, js, m, gmax, Q, step=0.005, thresh=0.05):
    GQ = Q.T @ G @ Q
    ev, V = np.linalg.eigh(GQ)
    order = np.argsort(-np.abs(ev))
    Us = V[:, order][:, :m]
    def P(g):
        u = Q.T @ atoms(np.array([g]), a, js)[:, 0]
        return 1.0 - np.sum((Us.T @ (u / np.linalg.norm(u))) ** 2)
    grid = np.arange(0.2, gmax, step)
    U = Q.T @ atoms(grid, a, js); U /= np.linalg.norm(U, axis=0)
    pv = 1.0 - np.sum((Us.T @ U) ** 2, axis=0)
    out = []
    for i in range(1, len(pv) - 1):
        if pv[i] <= pv[i - 1] and pv[i] <= pv[i + 1] and pv[i] < thresh:
            r = sopt.minimize_scalar(P, bracket=(grid[i - 1], grid[i], grid[i + 1]), tol=1e-14)
            out.append((r.x, r.fun))
    return np.array(out).reshape(-1, 2)


def fit_weights_Q(G, a, js, gams, Q):
    GQ = Q.T @ G @ Q
    iu = np.triu_indices(GQ.shape[0])
    cols = []
    for g in gams:
        u = atoms(np.array([g]), a, js)[:, 0]; um = u[::-1]
        uq, umq = Q.T @ u, Q.T @ um
        cols.append((np.outer(uq, uq) + np.outer(umq, umq))[iu])
    A = np.array(cols).T
    w, *_ = np.linalg.lstsq(A, GQ[iu], rcond=None)
    res = GQ[iu] - A @ w
    return w, np.linalg.norm(res) / np.linalg.norm(GQ[iu])


def ritz(G, K, m):
    """Rayleigh-Ritz of 'multiplication by gamma' on L^2(zero measure), compressed to the dominant
    m-dim eigenspace of G: eigenvalues of Gs^{-1} Ks.  Real when Gs is positive definite."""
    ev, V = np.linalg.eigh(G)
    o = np.argsort(-np.abs(ev))
    Us = V[:, o][:, :m]
    return np.linalg.eigvals(np.linalg.solve(Us.T @ G @ Us, Us.T @ K @ Us))


def families_mp(a, N, form, dps=40):
    """Same as families() at mp precision (quadrature by mp.quad on panels; exact log p for zeta)."""
    mp.mp.dps = dps
    a_ = mp.mpf(a); w = mp.pi / a_; L = 2 * a_
    M = int(math.floor(math.exp(2 * a)))
    nz = [int(n) for n in np.nonzero(form.c[:M + 1])[0]]
    if form.name == "zeta":
        cn = [mp.log(int(round(math.exp(form.c[n])))) / mp.sqrt(n) for n in nz]
    else:
        cn = [mp.mpf(form.c[n]) / mp.sqrt(n) for n in nz]
    ln = [mp.log(n) for n in nz]
    kap = mp.mpf(form.kappa)
    pan = mp.linspace(0, L, max(8, 2 * N + 2))
    T, diag = [], []
    for m in range(N + 1):
        S = mp.quad(lambda x: mp.sin(m * w * x) * mp.exp(-2 * kap * x) / (-mp.expm1(-2 * x)), pan)
        C = -m * w * (mp.cosh(a_) - 1) / (m ** 2 * w ** 2 + mp.mpf(1) / 4)
        Ps = mp.fsum(c * mp.sin(m * w * l) for c, l in zip(cn, ln))
        T.append((2 * C if form.pole else 0) - S - Ps)
        D1 = mp.quad(lambda x: 4 * (1 - x / L) * mp.cos(m * w * x) * mp.cosh(x / 2), pan)
        D2 = mp.quad(lambda x: (2 * mp.exp(-2 * x) - 2 * (1 - x / L) * mp.cos(m * w * x) * mp.exp(-2 * kap * x)) / (-mp.expm1(-2 * x)), pan)
        Pc = mp.fsum(c * (1 - l / L) * mp.cos(m * w * l) for c, l in zip(cn, ln))
        diag.append((D1 if form.pole else 0) + mp.log(mp.mpf(form.q) / mp.pi) - mp.euler - mp.log(-mp.expm1(-2 * L)) + D2 - 2 * Pc)
    return T, diag


def gram_mp(a, N, form, dps=40):
    T, diag = families_mp(a, N, form, dps)
    js = list(range(-N, N + 1)); n = len(js)
    G = mp.matrix(n, n)
    Tm = lambda m: T[m] if m >= 0 else -T[-m]
    for i, j in enumerate(js):
        for k_, k in enumerate(js):
            d = j - k
            G[i, k_] = diag[abs(j)] if d == 0 else (-1) ** abs(d) * (Tm(k) - Tm(j)) / (mp.pi * d)
    return G, np.array(js)


# ----------------------------------------------------------------------------- L-function zeros (controls)

def hurwitz_L(coeffs, q):
    """s -> sum_{r=1}^{q-1} coeffs[r] q^{-s} zeta(s, r/q)."""
    def L(s):
        return mp.power(q, -s) * mp.fsum(mp.mpf(coeffs[r]) * mp.zeta(s, mp.mpf(r) / q) for r in range(1, q) if coeffs[r] != 0)
    return L


def zeros_on_line(L, tmax, step=0.05, tmin=0.5):
    mp.mp.dps = 20
    ts = np.arange(tmin, tmax, step)
    v = np.array([abs(L(mp.mpc(0.5, t))) for t in ts], float)
    out = []
    for i in range(1, len(v) - 1):
        if v[i] < v[i - 1] and v[i] < v[i + 1] and v[i] < 0.3:
            try:
                r = mp.findroot(L, mp.mpc(0.5, ts[i]))
                if abs(r.real - 0.5) < 1e-8 and abs(r.imag - ts[i]) < 2 * step:
                    out.append(float(r.imag))
            except Exception:
                pass
    return sorted(set(np.round(out, 10)))


# ----------------------------------------------------------------------------- driver

def _w(path, lines):
    with open(os.path.join(HERE, path), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def run_all(zeros_path):
    t0 = time.time()
    zeros = np.load(zeros_path)
    M = int(math.exp(12)) + 2
    lam = mangoldt(M)
    nn = np.arange(M + 1)
    zform = Form("zeta", lam)
    log = []
    def say(x):
        print(x, flush=True); log.append(x)

    # ---- A. validation
    say("== A. explicit formula validation ==")
    vlines = [f"zeros used: {len(zeros)} (gamma_K = {zeros[-1]:.6f}); zero list: zeros_rs.py (RS bracket + siegelz refine, index-checked vs mpmath.zetazero)"]
    validate_explicit_formula(zeros, vlines, As=(2.0, 6.0, 12.0))
    vlines.append("")
    vlines.append("Gram matrix: prime-side closed form vs zero side (10^4 zeros + smooth-density tail with N0(T) boundary correction)")
    vlines.append("a,N,max|G_prime-G_zero|,max|G|,max|K_prime-K_zero|,max|K|")
    for a in [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]:
        G, K, js, fam = gram(a, 30, zform)
        Gz, Kz, Gt = gram_zero_side(zeros, a, js)
        vlines.append(f"{a},{30},{np.abs(G-Gz).max():.3e},{np.abs(G).max():.3e},{np.abs(K-Kz).max():.3e},{np.abs(K).max():.3e}")
    for l in vlines: say(l)
    _w("validation.txt", vlines)

    # ---- B. zeta recovery
    say("== B. zeta recovery ==")
    rows = ["a,N,band,method,k,gamma_rec,gamma_true,err,weight"]
    summ = ["a,N,n,band,zeros_in_band,m_blind,min_eig,music0_found,music0_maxerr,music6_found,music6_maxerr,music6_mederr,esprit_maxerr,esprit_max_imag,ritz_maxerr,ritz_max_imag,w6_min,w6_max,w6_relres,wtrue_min,wtrue_max"]
    configs = [(a, N) for a in [1, 2, 3, 4, 5, 6] for N in [30, 60, 100]]
    configs += [(a, int(math.ceil(100 * a / math.pi))) for a in [1, 2, 3, 4, 5, 6]]   # fixed band ~100
    configs = sorted(set(configs))
    keep = {}
    for a, N in configs:
        a = float(a)
        G, K, js, fam = gram(a, N, zform)
        band = math.pi * N / a
        ev = np.linalg.eigvalsh(G)
        nzb = int(np.sum(zeros < band))
        m = int(np.sum(np.abs(ev) > 0.2 * 2 * a))
        def match(g):
            k = int(np.argmin(np.abs(zeros - g))); return k + 1, zeros[k], g - zeros[k]
        res = {}
        for p in (0, 6):
            Q = taper_basis(js, p)
            mQ = int(np.sum(np.abs(np.linalg.eigvalsh(Q.T @ G @ Q)) > 0.2 * 2 * a))
            pk = music_Q(G, a, js, mQ, band, Q)
            res[p] = pk
        pk6 = res[6][:, 0] if len(res[6]) else np.array([])
        Q6 = taper_basis(js, 6)
        w6, rr6 = fit_weights_Q(G, a, js, pk6, Q6) if len(pk6) else (np.array([np.nan]), np.nan)
        ztrue = zeros[zeros < band]
        wt, _ = fit_weights_Q(G, a, js, ztrue, Q6) if len(ztrue) else (np.array([np.nan]), np.nan)
        for p in (0, 6):
            for g, pv in res[p]:
                k, zt, e = match(g)
                wv = ""
                if p == 6:
                    wv = f"{w6[list(pk6).index(g)]:.6f}"
                rows.append(f"{a},{N},{band:.3f},music_p{p},{k},{g:.10f},{zt:.10f},{e:+.3e},{wv}")
        es = esprit_loewner(G, a, js, m); esp = es[es.real > 0]
        for g in sorted(esp, key=lambda x: x.real):
            k, zt, e = match(g.real)
            rows.append(f"{a},{N},{band:.3f},esprit_loewner,{k},{g.real:.10f}{g.imag:+.2e}j,{zt:.10f},{e:+.3e},")
        rz = ritz(G, K, m); rzp = rz[rz.real > 0]
        for g in sorted(rzp, key=lambda x: x.real):
            k, zt, e = match(g.real)
            rows.append(f"{a},{N},{band:.3f},ritz,{k},{g.real:.10f}{g.imag:+.2e}j,{zt:.10f},{e:+.3e},")
        def mx(arr):
            arr = np.asarray(arr)
            return f"{np.max(np.abs(arr)):.2e}" if len(arr) else "nan"
        # restrict error stats to ordinates matching a zero within 0.5 and below band
        def errs(vals):
            out = []
            for g in vals:
                k, zt, e = match(g)
                if abs(e) < 0.5: out.append(e)
            return np.array(out)
        e0, e6 = errs(res[0][:, 0] if len(res[0]) else []), errs(pk6)
        ee, er = errs(esp.real), errs(rzp.real)
        summ.append(",".join(map(str, [a, N, 2 * N + 1, f"{band:.2f}", nzb, m, f"{ev[0]:.2e}",
                     len(e0), mx(e0), len(e6), mx(e6), f"{np.median(np.abs(e6)):.2e}" if len(e6) else "nan",
                     mx(ee), f"{np.max(np.abs(esp.imag)):.1e}" if len(esp) else "nan",
                     mx(er), f"{np.max(np.abs(rzp.imag)):.1e}" if len(rzp) else "nan",
                     f"{np.nanmin(w6):.4f}", f"{np.nanmax(w6):.4f}", f"{rr6:.2e}", f"{np.nanmin(wt):.4f}", f"{np.nanmax(wt):.4f}"])))
        say(summ[-1])
        keep[(a, N)] = (G, K, js, pk6, w6)
    _w("recovery_zeta.csv", rows)
    _w("summary_zeta.csv", summ)

    # NNLS (N = 30)
    say("== B2. NNLS (N=30, grid step 0.02, w >= 0) ==")
    nl = ["a,N,gamma_nnls,weight,nearest_zero,err"]
    for a in [2.0, 3.0, 4.0, 5.0, 6.0]:
        N = 30
        G, K, js, fam = gram(a, N, zform)
        band = math.pi * N / a
        out, rn = nnls_fit(G, a, js, band + 3.0)
        for g, wv in out:
            k = int(np.argmin(np.abs(zeros - g)))
            nl.append(f"{a},{N},{g:.6f},{wv:.5f},{zeros[k]:.6f},{g-zeros[k]:+.2e}")
        nl.append(f"# a={a}: residual norm {rn:.3e} / ||G_upper|| {np.linalg.norm(G[np.triu_indices(len(js))]):.3e}")
        say(f"a={a}: {len(out)} NNLS atoms; residual {rn:.2e}")
    _w("nnls_zeta.csv", nl)

    # ---- C. controls
    say("== C. controls ==")
    Lz = {}
    Lz["chi4"] = zeros_on_line(hurwitz_L([0, 1, 0, -1], 4), 110)
    Lz["chi3"] = zeros_on_line(hurwitz_L([0, 1, -1], 3), 110)
    A_dh, B_dh = dh_coeffs(M)
    fdh = hurwitz_L([0] + [float(A_dh[r]) for r in range(1, 5)], 5)
    Lz["DH_line"] = zeros_on_line(fdh, 120)
    mp.mp.dps = 25
    dh_off = []
    for guess in [mp.mpc(0.8085, 85.6993), mp.mpc(0.6508, 114.1633)]:
        try:
            dh_off.append(mp.findroot(fdh, guess))
        except Exception as ex:
            say(f"DH off-line zero refine failed near {guess}: {ex}")
    lzl = [f"chi4 (L(s,chi_-4)) zeros on line up to 110: " + " ".join(f"{x:.6f}" for x in Lz['chi4']),
           f"chi3 (L(s,chi_-3)) zeros on line up to 110: " + " ".join(f"{x:.6f}" for x in Lz['chi3']),
           f"DH zeros on line up to 120: " + " ".join(f"{x:.6f}" for x in Lz['DH_line']),
           "DH off-line zeros (refined): " + " ".join(f"{mp.nstr(r, 12)}" for r in dh_off)]
    for l in lzl: say(l)
    _w("control_lfunction_zeros.txt", lzl)

    cforms = []
    for nm, chi in [("chi4", chi_mod4(nn)), ("chi3", chi_mod3(nn))]:
        for e in [0.05, 0.1, 0.3, -0.05, -0.1, -0.3]:
            cforms.append((f"{nm}_eps{e:+.2f}", Form(nm, lam * (1 + e * chi)), nm, e))
    cforms.append(("DH", Form("DH", B_dh, pole=False, q=5.0, kappa=0.75), "DH", None))
    cforms.insert(0, ("zeta", zform, None, 0.0))
    crow = ["form,a,N,band,min_eig,n_neg_eig(<-1e-8),m,esprit_max_imag,esprit_complex,ritz_max_imag,ritz_complex,music_peaks,peaks_matching_zeta,peaks_matching_L,unmatched,neg_weights,min_weight,weights_at_L_zeros"]
    cdetail = []
    for name, f, kind, e in cforms:
        for a in [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]:
            for N in sorted({60, int(math.ceil(100 * a / math.pi))}):
                G, K, js, fam = gram(a, N, f)
                band = math.pi * N / a
                ev = np.linalg.eigvalsh(G)
                nneg = int(np.sum(ev < -1e-8 * np.abs(ev).max()))
                m = int(np.sum(np.abs(ev) > 0.2 * 2 * a))
                es = esprit_loewner(G, a, js, m); esp = es[es.real > 0]
                ecx = [x for x in esp if abs(x.imag) > 1e-6]
                rz = ritz(G, K, m); rzp = rz[rz.real > 0]
                rcx = [x for x in rzp if abs(x.imag) > 1e-6]
                pk = music_Q(G, a, js, m, band, np.eye(len(js)))
                gam = pk[:, 0] if len(pk) else np.array([])
                w, rr = fit_weights_Q(G, a, js, gam, np.eye(len(js))) if len(gam) else (np.array([]), np.nan)
                lz = np.array(Lz.get(kind, []) if kind in ("chi4", "chi3") else Lz["DH_line"] if kind == "DH" else [])
                mz = [g for g in gam if np.min(np.abs(zeros - g)) < 0.05]
                ml = [g for g in gam if len(lz) and np.min(np.abs(lz - g)) < 0.05 and np.min(np.abs(zeros - g)) >= 0.05]
                un = [g for g in gam if g not in mz and g not in ml]
                wl = [f"{g:.4f}:{wv:+.3f}" for g, wv in zip(gam, w) if g in ml]
                crow.append(",".join(map(str, [name, a, N, f"{band:.1f}", f"{ev[0]:.2e}", nneg, m,
                    f"{max([abs(x.imag) for x in esp], default=0):.2e}", len(ecx),
                    f"{max([abs(x.imag) for x in rzp], default=0):.2e}", len(rcx),
                    len(gam), len(mz), len(ml), len(un), int(np.sum(w < 0)), f"{w.min():.3f}" if len(w) else "nan",
                    " ".join(wl)])))
                if rcx or ecx:
                    cdetail.append(f"{name} a={a} N={N}: complex ESPRIT {['%.4f%+.4fj' % (x.real, x.imag) for x in ecx]}  complex Ritz {['%.4f%+.4fj' % (x.real, x.imag) for x in rcx]}")
                say(crow[-1][:200])
    _w("controls.csv", crow)

    # oracle weight fit: atoms at the KNOWN zeta zeros and L(chi) zeros in band (tapered p=6 subspace);
    # prediction: weight 1 at zeta ordinates, eps at L(chi) ordinates, residual = -eps * (continuous
    # archimedean density of L(chi)) + out-of-band tail -> its most negative eigenvalue shows the failure.
    ol = ["form,a,N,band,mean_w_zeta,max|w_zeta-1|,w_L(first 6 L zeros),mean_w_L,residual_min_eig,residual_max_eig"]
    for name, f, kind, e in cforms:
        if kind not in ("chi4", "chi3"):
            continue
        for a in [3.0, 6.0]:
            N = int(math.ceil(100 * a / math.pi))
            G, K, js, fam = gram(a, N, f)
            band = math.pi * N / a
            Q = taper_basis(js, 6)
            zz = list(zeros[zeros < band - 3]); ll = [x for x in Lz[kind] if x < band - 3]
            w, rr = fit_weights_Q(G, a, js, zz + ll, Q)
            wz, wl = w[:len(zz)], w[len(zz):]
            def S(gs, ws):
                U = atoms(np.asarray(gs), a, js); Um = U[::-1]
                return (U * ws) @ U.T + (Um * ws) @ Um.T
            R = Q.T @ (G - S(zz + ll, w)) @ Q
            er = np.linalg.eigvalsh(R)
            ol.append(f"{name},{a},{N},{band:.1f},{wz.mean():.4f},{np.max(np.abs(wz-1)):.3f}," + " ".join(f"{x:+.3f}" for x in wl[:6]) + f",{wl.mean():+.4f},{er[0]:.3e},{er[-1]:.3e}")
            say(ol[-1])
    _w("controls_oracle_weights.csv", ol)
    _w("controls_complex_frequencies.txt", cdetail if cdetail else ["(none)"])

    # ---- D. residual (tail) spectrum
    say("== D. residual spectrum ==")
    rl = ["a,N,which,top10_eigs,min_eig,trace,||R-R_pred||_F/||R_pred||_F"]
    for a, N in [(2.0, 100), (3.0, 60), (3.0, 100), (6.0, 100)]:
        G, K, js, pk6, w6 = keep[(a, N)]
        band = math.pi * N / a
        # recovered atoms (MUSIC p=6 ordinates, unit weights) vs true in-band zeros
        def S(gs, ws):
            U = atoms(np.asarray(gs), a, js); Um = U[::-1]
            return (U * ws) @ U.T + (Um * ws) @ Um.T
        R_rec = G - S(pk6, np.ones(len(pk6)))
        zin = zeros[zeros < band]; zout = zeros[zeros >= band]
        R_true = G - S(zin, np.ones(len(zin)))
        Gz_out, _, Gt = gram_zero_side(zeros, a, js, with_K=False)
        R_pred = Gz_out - S(zin, np.ones(len(zin)))     # = sum over zeros above band + tail
        for nm, R in [("G - recovered(unit w)", R_rec), ("G - true in-band atoms", R_true)]:
            evr = np.linalg.eigvalsh(R)[::-1]
            rl.append(f"{a},{N},{nm}," + " ".join(f"{x:.3e}" for x in evr[:10]) + f",{evr[-1]:.2e},{np.trace(R):.4f},{np.linalg.norm(R-R_pred)/np.linalg.norm(R_pred):.2e}")
        # how well do the top eigenvectors of the tail align with the first few zeros above the band?
        evr, Vr = np.linalg.eigh(R_true); Vr = Vr[:, ::-1]
        nxt = zout[:8]
        U = atoms(nxt, a, js); U /= np.linalg.norm(U, axis=0)
        cap = np.sum((Vr[:, :8].T @ U) ** 2, axis=0)
        rl.append(f"# a={a} N={N}: first zeros above band {np.round(nxt,3).tolist()} ; fraction of each atom captured by top-8 tail eigenvectors {np.round(cap,3).tolist()}")
        for l in rl[-3:]: say(l)
    _w("residual_spectrum.csv", rl)

    # ---- E. Lanczos / Jacobi coefficients and Ritz table
    say("== E. Jacobi coefficients ==")
    jl = ["a,N,start,k,alpha_k,beta_k"]
    for a, N in [(3.0, 60), (6.0, 100), (2.0, 100)]:
        G, K, js, pk6, w6 = keep[(a, N)]
        e0 = (js == 0).astype(float)
        al, be = lanczos(G, e0, min(60, len(js) - 1))
        for k in range(len(al)):
            jl.append(f"{a},{N},e0,{k},{al[k]:.8e},{be[k]:.8e}")
        # even (cosine) start: constant function; also an 'all-ones' start (point mass delta-like)
        one = np.ones(len(js))
        al2, be2 = lanczos(G, one, min(60, len(js) - 1))
        for k in range(len(al2)):
            jl.append(f"{a},{N},ones,{k},{al2[k]:.8e},{be2[k]:.8e}")
    _w("jacobi_coefficients.csv", jl)

    # ---- F. mp precision PSD check + a=1 MUSIC at 40 digits
    say("== F. 40-digit Gram (PSD below double floor) ==")
    fl = ["a,N,dps,smallest 6 eigenvalues (mp),largest"]
    mp_res = {}
    for a, N in [(1.0, 20), (1.0, 30), (3.0, 20)]:
        tt = time.time()
        Gm, js = gram_mp(a, N, zform, dps=40)
        E, Qm = mp.eigsy(Gm)
        Ev = sorted([E[i] for i in range(len(js))])
        fl.append(f"{a},{N},40," + " ".join(mp.nstr(x, 6) for x in Ev[:6]) + f",{mp.nstr(Ev[-1], 8)}   [{time.time()-tt:.0f}s]")
        say(fl[-1])
        mp_res[(a, N)] = (Gm, E, Qm, js)
    # mp MUSIC at a=1, N=30: noise subspace from 40-digit eigenvectors, scan m
    a, N = 1.0, 30
    Gm, E, Qm, js = mp_res[(a, N)]
    n = len(js)
    order = sorted(range(n), key=lambda i: -abs(E[i]))
    Gd = np.array(Gm.tolist(), dtype=float)
    fl.append("")
    fl.append("a=1 (primes <= 7 only), N=30: MUSIC with 40-digit eigenvectors; m = signal dimension")
    for m in [20, 30, 40, 44, 48, 52]:
        sig = [order[i] for i in range(m)]
        Us = mp.matrix(n, m)
        for c, i in enumerate(sig):
            for r in range(n):
                Us[r, c] = Qm[r, i]
        def Pm(g):
            g = mp.mpf(g)
            u = mp.matrix([mp.sqrt(2 * mp.mpf(a)) * mp.sinc(g * a + mp.pi * j) for j in js])
            u = u / mp.norm(u)
            pr = Us.T * u
            return 1 - mp.fsum(x ** 2 for x in pr)
        mp.mp.dps = 40
        grid = np.arange(5.0, math.pi * N / a, 0.05)
        pv = [Pm(g) for g in grid]
        found = []
        for i in range(1, len(grid) - 1):
            if pv[i] < pv[i - 1] and pv[i] < pv[i + 1] and pv[i] < mp.mpf("1e-3"):
                lo, hi = grid[i - 1], grid[i + 1]
                for _ in range(40):   # golden-section in mp
                    m1 = lo + (hi - lo) * 0.381966; m2 = hi - (hi - lo) * 0.381966
                    if Pm(m1) < Pm(m2): hi = m2
                    else: lo = m1
                g = (lo + hi) / 2
                k = int(np.argmin(np.abs(zeros - g)))
                found.append((g, zeros[k], g - zeros[k], float(Pm(g))))
        good = [x for x in found if abs(x[2]) < 0.05]
        fl.append(f"  m={m}: {len(found)} peaks, {len(good)} within 0.05 of a zero; " +
                  "; ".join(f"{g:.6f}(err {e:+.1e})" for g, zt, e, pvv in found))
        say(fl[-1][:300])
    _w("mp_precision.txt", fl)
    _w("run_log.txt", log + [f"total time {time.time()-t0:.0f}s"])


def supplement(zeros_path):
    """(i) PSD threshold of the chi perturbation as eps -> 0; (ii) Lanczos of the Ritz (multiplication)
    operator S = Gs^{-1/2} Ks Gs^{-1/2} started from phi_0 (Jacobi matrix of the measure
    sum_gamma |u_0(gamma)|^2 delta_gamma as seen through the signal subspace); (iii) DH negative-eigenvalue
    check against the rank-2 prediction 2 (sinh(2 delta a)/(2 delta) - a)."""
    zeros = np.load(zeros_path)
    M = int(math.exp(12)) + 2
    lam = mangoldt(M); nn = np.arange(M + 1)
    out = ["(i) min eigenvalue of G_eps for c(n) = Lambda(n)(1 + eps chi_-4(n)), double precision"]
    out.append("a,N,eps,min_eig,min_eig/eps")
    for a, N in [(1.0, 30), (3.0, 60), (6.0, 100)]:
        for e in [0.0, 1e-12, 1e-9, 1e-6, 1e-3, -1e-6, -1e-3]:
            G, K, js, fam = gram(a, N, Form("chi4", lam * (1 + e * chi_mod4(nn))))
            mn = np.linalg.eigvalsh(G)[0]
            out.append(f"{a},{N},{e:+.0e},{mn:.3e},{(mn / e if e else float('nan')):.3e}")
    out.append("")
    out.append("(ii) Lanczos of the Ritz operator S (symmetric; eigenvalues = Ritz values ~ +-gamma) from phi_0")
    out.append("a,N,m,k,alpha_k,beta_k   [then: Ritz values > 0 vs true ordinates]")
    zform = Form("zeta", lam)
    for a, N in [(6.0, 100), (3.0, 60), (4.0, 128)]:
        G, K, js, fam = gram(a, N, zform)
        ev, V = np.linalg.eigh(G)
        m = int(np.sum(np.abs(ev) > 0.4 * a))
        o = np.argsort(-np.abs(ev)); Us = V[:, o][:, :m]
        Gs = Us.T @ G @ Us; Ks = Us.T @ K @ Us
        w_, Vg = np.linalg.eigh(Gs); Gm12 = Vg @ np.diag(w_ ** -0.5) @ Vg.T; G12 = Vg @ np.diag(w_ ** 0.5) @ Vg.T
        S = Gm12 @ Ks @ Gm12; S = (S + S.T) / 2
        v0 = G12 @ (Us.T @ (js == 0).astype(float))
        al, be = lanczos(S, v0, m - 1)
        for k in range(len(al)):
            out.append(f"{a},{N},{m},{k},{al[k]:+.6e},{be[k]:.6e}")
        rv = np.sort(np.linalg.eigvalsh(S)); rv = rv[rv > 0]
        zt = zeros[: len(rv)]
        out.append(f"# a={a} N={N}: Ritz>0 = " + " ".join(f"{x:.4f}" for x in rv))
        out.append(f"#              true  = " + " ".join(f"{x:.4f}" for x in zt))
        out.append(f"# max |Ritz - true| = {np.max(np.abs(rv - zt)):.3e}")
    out.append("")
    out.append("(iii) DH: two most negative eigenvalues vs rank-2 prediction -2 (sinh(2 d a)/(2 d) - a), d = 0.808517 - 1/2")
    A_dh, B_dh = dh_coeffs(M)
    d = 0.808517182456637 - 0.5
    for a in [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]:
        N = int(math.ceil(100 * a / math.pi))
        G, K, js, fam = gram(a, N, Form("DH", B_dh, pole=False, q=5.0, kappa=0.75))
        ev = np.linalg.eigvalsh(G)
        pred = -2 * (math.sinh(2 * d * a) / (2 * d) - a)
        out.append(f"a={a} N={N}: eig[0:2] = {ev[0]:.3f} {ev[1]:.3f} ; predicted (isolated pair, no overlap) {pred:.3f}")
    for l in out:
        print(l, flush=True)
    _w("supplement.txt", out)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "supp":
        supplement(sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "zeros_1e4.npy"))
    elif len(sys.argv) > 1 and sys.argv[1] == "run":
        run_all(sys.argv[2] if len(sys.argv) > 2 else os.path.join(SCR, "zeros10k.npy"))
    else:
        print(__doc__)
