"""Zhu-type one-stroke reduction R_{T#} of the window Weil form, Legendre basis, python-flint arb.

Convention (Zhu arXiv:2608.24827): f real, supp f in [-a, a], F(t) = int f e^{itu} du,
  Q(f) = Pole(f) + (1/pi) int_0^inf Psi_a(t) |F(t)|^2 dt,
  Psi_a(t) = Re psi(1/4 + it/2) - log pi - sum_{log n < 2a} 2 Lambda(n) n^{-1/2} cos(t log n).
Pole: even sector +2 F(i/2)^2, odd sector -2 (sum alpha_k c_k i_k(a/2))^2.
R(f) = Pole(f) + (1/pi) int_0^{T#} (Psi_a - beta*) |F|^2 dt + beta* ||f||^2 <= Q(f).
Legendre basis phi_n(u) = sqrt((2n+1)/(2a)) P_n(u/a), F_n(t) = i^n c_n j_n(a t), c_n = sqrt(2a(2n+1)).
This module is the matrix-builder layer; rigour add-ons live in certify.py.
"""
import math
import time
import flint
from flint import arb, acb, arb_mat


def prime_powers_below(bound_float):
    out = []
    n = 2
    while math.log(n) < bound_float:
        m, p = n, None
        for q in range(2, n + 1):
            if m % q == 0:
                p = q
                break
        while m % p == 0:
            m //= p
        if m == 1:
            out.append((n, p))
        n += 1
    return out


def primes_in_window(a):
    """prime powers n with log n < 2a (strict, Zhu's convention), decided in arb."""
    two_a = 2 * arb(a)
    res = []
    for (n, p) in prime_powers_below(2 * float(a) + 0.5):
        ln = arb(n).log()
        if ln < two_a:
            res.append((n, p))
        elif not (ln > two_a):
            raise ValueError("log n straddles 2a for n=%d" % n)
    return res


def comb_mass(a):
    s = arb(0)
    for (n, p) in primes_in_window(a):
        s += 2 * arb(p).log() / arb(n).sqrt()
    return s


def beta_star(a, Tsharp):
    T = arb(Tsharp)
    return (T / (2 * arb.pi())).log() - 1 / T - comb_mass(a)


def make_psi(a):
    plist = [(arb(p).log() * 2 / arb(n).sqrt(), arb(n).log()) for (n, p) in primes_in_window(a)]
    logpi = arb.pi().log()

    def psi(t):
        z = acb(arb(1) / 4, t / 2)
        v = z.digamma().real - logpi
        for (c, ln) in plist:
            v -= c * (t * ln).cos()
        return v
    return psi


def gl_rule(npts):
    return [arb.legendre_p_root(npts, k, weight=True) for k in range(npts)]


def panels(Tsharp, near_end=8.0, near_w=0.5, far_w=2.0):
    edges = []
    x = 0.0
    while x < min(near_end, Tsharp) - 1e-12:
        y = min(x + near_w, near_end, Tsharp)
        edges.append((x, y, 'near'))
        x = y
    while x < Tsharp - 1e-12:
        y = min(x + far_w, Tsharp)
        edges.append((x, y, 'far'))
        x = y
    return edges


def composite_nodes(Tsharp, near_end=8.0, near_w=0.5, near_n=32, far_w=2.0, far_n=48):
    rn = gl_rule(near_n)
    rf = gl_rule(far_n)
    nodes = []
    eds = panels(Tsharp, near_end, near_w, far_w)
    for (lo, hi, kind) in eds:
        rule = rn if kind == 'near' else rf
        c = (arb(lo) + arb(hi)) / 2
        h = (arb(hi) - arb(lo)) / 2
        for (r, w) in rule:
            tt = c + h * r
            # exact dyadic node (midpoint of the GL-root ball); the perturbation |tt - tmid| <= rad(tt)
            # is accounted for separately in the certificate (node-perturbation term).
            nodes.append((arb(tt.mid()), h * w))
    return nodes, eds


def _bessel_top(x, nu, want_bits=320):
    """rigorous ball for J_nu(x) with >= want_bits relative accuracy (adaptive precision)."""
    p = max(flint.ctx.prec, 256)
    while True:
        old = flint.ctx.prec
        flint.ctx.prec = p
        try:
            xx = arb(x)
            v = xx.bessel_j(nu)
        finally:
            flint.ctx.prec = old
        if v.rel_accuracy_bits() >= want_bits:
            return v
        p *= 2
        if p > 60000:
            raise RuntimeError("bessel_j precision blow-up")


def sph_j_all(x, nmax, base_prec=None):
    """[j_0(x), ..., j_nmax(x)] as rigorous arb balls, x real arb > 0.
    Start at N_top >= max(nmax, 1.3 x + 40) (decaying region) with two rigorous values from
    Arb's J_{n+1/2}; backward recurrence j_{n-1} = (2n+1)/x j_n - j_{n+1} at a working precision
    raised by ~1.0 x bits to absorb the ball-arithmetic wrapping in the oscillatory region
    (measured loss ~0.9 x bits; the recurrence is stable in exact arithmetic, only radii wrap)."""
    if base_prec is None:
        base_prec = flint.ctx.prec
    xf = float(x.mid())
    ntop = max(nmax, int(1.3 * xf) + 40)
    # ball-arithmetic wrapping: ~0.9x bits in the oscillatory region plus up to ~0.3x in the transition region
    # when ntop >> x; start at 1.3x extra and re-run with more precision if the output is not accurate enough.
    extra = int(1.3 * xf) + 128
    while True:
        out = _sph_j_backward(x, nmax, ntop, base_prec + extra)
        # accuracy test: absolute (scale 1/(x+1)) in the oscillatory range, relative in the decaying range
        tol = arb(2) ** (-(base_prec - 8))
        scale = 1 / (x + 1)
        ok = True
        n_osc = int(1.2 * xf) + 1
        for n, v in enumerate(out):
            if n <= n_osc:
                if not (v.rad() < tol * scale):
                    ok = False
                    break
            else:
                if not v.is_zero() and v.rel_accuracy_bits() < base_prec - 8:
                    ok = False
                    break
        if ok:
            return [v + 0 for v in out]
        extra += int(0.5 * xf) + 256
        if extra > 40 * xf + 20000:
            raise RuntimeError("sph_j_all: precision blow-up at x=%s" % xf)


def _sph_j_backward(x, nmax, ntop, wp):
    xf = float(x.mid())
    old = flint.ctx.prec
    flint.ctx.prec = wp
    try:
        half = arb(1) / 2
        pref = (arb.pi() / (2 * x)).sqrt()
        jp1 = pref * _bessel_top(x, ntop + 1 + half, wp + 32)
        jn = pref * _bessel_top(x, ntop + half, wp + 32)
        out = [None] * (nmax + 1)
        inv = 1 / x
        if ntop <= nmax:
            out[ntop] = jn
        for n in range(ntop, 0, -1):
            jm1 = (2 * n + 1) * inv * jn - jp1
            if n - 1 <= nmax:
                out[n - 1] = jm1
            jp1, jn = jn, jm1
    finally:
        flint.ctx.prec = old
    return out


def sph_i(n, y):
    """modified spherical Bessel i_n(y) = sqrt(pi/(2y)) I_{n+1/2}(y)."""
    return (arb.pi() / (2 * y)).sqrt() * y.bessel_i(n + arb(1) / 2)


def sector_modes(sector, N):
    return [2 * k for k in range(N)] if sector == 'even' else [2 * k + 1 for k in range(N)]


def build_R(a, Tsharp, N, sector='even', nodes=None, verbose=True):
    """Leading N x N block of R_{T#} in the given parity sector (orders 0,2,.. or 1,3,..).
    Returns (M as arb_mat, beta*, info)."""
    a_ = arb(a)
    modes = sector_modes(sector, N)
    nmax = modes[-1]
    bstar = beta_star(a, Tsharp)
    psi = make_psi(a)
    if nodes is None:
        nodes, _ = composite_nodes(Tsharp)
    t0 = time.time()
    cn = [(2 * a_ * (2 * n + 1)).sqrt() for n in modes]
    sg = []
    for n in modes:
        k = n // 2 if sector == 'even' else (n - 1) // 2
        sg.append(-1 if k % 2 else 1)
    rows = []
    wts = []
    pi = arb.pi()
    for (t, w) in nodes:
        js = sph_j_all(arb((a_ * t).mid()) if (a_ * t).rad() > 0 else a_ * t, nmax)
        rows.append([sg[i] * cn[i] * js[modes[i]] for i in range(N)])
        wts.append(w * (psi(t) - bstar) / pi)
    t1 = time.time()
    J = arb_mat(rows)
    WJ = arb_mat([[wts[i] * rows[i][k] for k in range(N)] for i in range(len(rows))])
    G = J.transpose() * WJ
    t2 = time.time()
    # pole
    y = a_ / 2
    pv = [cn[i] * sph_i(modes[i], y) for i in range(N)]
    sgn_pole = 2 if sector == 'even' else -2
    M = arb_mat(N, N)
    for i in range(N):
        for k in range(N):
            v = G[i, k] + sgn_pole * pv[i] * pv[k]
            if i == k:
                v += bstar
            M[i, k] = v
    if verbose:
        print("  build_R a=%s T#=%s N=%d %s: nodes=%d  bessel %.1fs  matmul %.1fs" %
              (a, Tsharp, N, sector, len(nodes), t1 - t0, t2 - t1))
    return M, bstar, dict(nodes=len(nodes))


def symmetrize(M):
    n = M.nrows()
    S = arb_mat(n, n)
    for i in range(n):
        for k in range(n):
            S[i, k] = (M[i, k] + M[k, i]) / 2
    return S


def min_eig_inverse_iter(M, iters=8, verbose=False):
    """Smallest eigenvalue estimate of symmetric PD-ish arb matrix via inverse iteration on midpoints."""
    n = M.nrows()
    Mm = M.mid()
    import random
    rnd = random.Random(12345)
    x = arb_mat([[arb(rnd.uniform(-1, 1))] for k in range(n)])
    lam = None
    for it in range(iters):
        y = Mm.solve(x)
        # normalise
        nrm = arb(0)
        for k in range(n):
            nrm += y[k, 0] ** 2
        nrm = nrm.sqrt()
        x = arb_mat([[y[k, 0].mid() / nrm.mid()] for k in range(n)])
        Mx = Mm * x
        num = arb(0)
        for k in range(n):
            num += x[k, 0] * Mx[k, 0]
        lam = num
        if verbose:
            print("   iter", it, lam.mid().str(5, radius=False))
    return lam, x
