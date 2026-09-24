"""Weil window forms on L^2[-L/2, L/2], L = log x, in BOTH parity sectors.

    QW_x(f) = W_F(f^* * f),   W_F = pole_F + arch_F - sum_n Lambda_F(n) n^{-1/2} (delta_{log n} + delta_{-log n})

F = 'zeta' or 'dh' (Davenport-Heilbronn, the negative control: same functional-equation shape,
no Euler product, zeros off the line).

Even sector: cosine basis phi_0 = L^{-1/2}, phi_k = (2/L)^{1/2} cos(k w t), w = 2 pi / L.  The closed
forms are those of the idea's weilwin.py (reproduced CCM's zeta table to 2e-34 at x = 9).
Odd sector: sine basis psi_k = (2/L)^{1/2} sin(k w t), k = 1..N.  The closed forms are derived here
(README section 3).  They differ from the even ones by the sign of every sum-frequency term, and the
zeta pole term becomes -8 b_j b_k (negative semidefinite) instead of +2 v_j v_k.

Validation (see validate_forms.py): (a) translation invariance forces the displacement identity
    Omega Q - Q Omega = l g^T - g l^T,   Omega = diag((k w)^2),
with l the boundary functional (f(L/2) in the even sector, f'(L/2) in the odd one); (b) brute-force
quadrature of W_F(f1^* * f2) from the definitions for a few matrix entries.
"""
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre


# ---------------------------------------------------------------- arithmetic data
def von_mangoldt(nmax):
    lam = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        m, p = n, None
        for q in range(2, n + 1):
            if m % q == 0:
                p = q
                break
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = mp.log(p)
    return lam


def kappa_dh():
    s5 = mp.sqrt(5)
    return (mp.sqrt(10 - 2 * s5) - 2) / (s5 - 1)


def c_dh(n):
    k = kappa_dh()
    return {1: mp.mpf(1), 2: k, 3: -k, 4: mp.mpf(-1), 0: mp.mpf(0)}[n % 5]


def lambda_dh(nmax):
    """-D'/D = sum Lambda_D(n) n^{-s}:  sum_{d | n} c(d) Lambda_D(n/d) = c(n) log n."""
    cs = [mp.mpf(0)] + [c_dh(n) for n in range(1, nmax + 1)]
    lam = [mp.mpf(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = cs[n] * mp.log(n)
        for d in range(2, n + 1):
            if n % d == 0:
                acc -= cs[d] * lam[n // d]
        lam[n] = acc
    return lam


def xi_dh(s):
    """Completed DH function (pi/5)^{-(1+s)/2} Gamma((1+s)/2) D(s)."""
    k = kappa_dh()
    D = mp.power(5, -s) * (mp.zeta(s, mp.mpf(1) / 5) + k * mp.zeta(s, mp.mpf(2) / 5)
                           - k * mp.zeta(s, mp.mpf(3) / 5) - mp.zeta(s, mp.mpf(4) / 5))
    return mp.power(mp.pi / 5, -(1 + s) / 2) * mp.gamma((1 + s) / 2) * D


# ---------------------------------------------------------------- quadrature pieces
def _gl_nodes(a, b, panels, degree=5):
    gl = GaussLegendre(mp.mp)
    base = gl.calc_nodes(degree, mp.mp.prec)   # 3 * 2^(degree-1) = 48 nodes per panel
    h = (b - a) / panels
    out = []
    for p in range(panels):
        lo = a + p * h
        c = lo + h / 2
        r = h / 2
        for (xx, ww) in base:
            out.append((c + r * xx, r * ww))
    return out


def _integrals(L, N, kind, panels):
    """S[m] = int_0^L sin(m w u) W(u) du, Cc[m] = int (1 - cos(m w u)) W(u) du,
    Cu[m] = int u cos(m w u) W(u) du, Cfix = int_0^L (e^{-2u}/u - W(u)) du,
    with W(u) = e^{u/2}/sinh u (zeta, Gamma(s/2)) or e^{-u/2}/sinh u (DH, Gamma((1+s)/2))."""
    om = 2 * mp.pi / L
    if kind == 'zeta':
        wfun = lambda u: mp.exp(u / 2) / mp.sinh(u)
    else:
        wfun = lambda u: mp.exp(-u / 2) / mp.sinh(u)
    S = [mp.mpf(0)] * (N + 1)
    Cc = [mp.mpf(0)] * (N + 1)
    Cu = [mp.mpf(0)] * (N + 1)
    Cfix = mp.mpf(0)
    for (u, wt) in _gl_nodes(mp.mpf(0), L, panels):
        wu = wfun(u)
        Cfix += wt * (mp.exp(-2 * u) / u - wu)
        th = om * u
        c1, s1 = mp.cos(th), mp.sin(th)
        cm, sm = mp.mpf(1), mp.mpf(0)          # cos(m th), sin(m th) by rotation
        for m in range(N + 1):
            S[m] += wt * sm * wu
            Cc[m] += wt * (1 - cm) * wu
            Cu[m] += wt * u * cm * wu
            cm, sm = cm * c1 - sm * s1, sm * c1 + cm * s1
    return S, Cc, Cu, Cfix


def build(x, N, kind='zeta', sector='even', Lam=None, panels=None):
    """Galerkin matrix of QW_x in the given parity sector.  Returns (Q, L).
    even: basis phi_0..phi_N (size N+1);  odd: basis psi_1..psi_N (size N)."""
    x = mp.mpf(x)
    L = mp.log(x)
    om = 2 * mp.pi / L
    c0 = -mp.log(mp.pi) if kind == 'zeta' else mp.log(mp.mpf(5) / mp.pi)
    if panels is None:
        panels = max(40, 2 * N)
    S, Cc, Cu, Cfix = _integrals(L, N, kind, panels)
    CL = Cfix + mp.e1(2 * L) + c0
    nmax = int(mp.floor(x))
    if Lam is None:
        Lam = von_mangoldt(nmax) if kind == 'zeta' else lambda_dh(nmax)
    sgn = 1 if sector == 'even' else -1          # sign of every sum-frequency term
    idx = list(range(0, N + 1)) if sector == 'even' else list(range(1, N + 1))
    M = len(idx)
    a = {k: (1 / mp.sqrt(L) if k == 0 else mp.sqrt(2 / L)) for k in idx}
    Q = mp.matrix(M, M)
    # archimedean part: g(0) CL + int_0^L (g(0) - g_e(u)) W(u) du
    for p, j in enumerate(idx):
        for q, k in enumerate(idx):
            if j == k:
                if k == 0:
                    Q[p, q] = Cu[0] / L + CL
                else:
                    Q[p, q] = Cc[k] + Cu[k] / L + sgn * S[k] / (k * om * L) + CL
            else:
                s = (-1) ** (j + k)
                val = (S[k] - S[j]) / ((j - k) * om) - sgn * (S[j] + S[k]) / ((j + k) * om)
                Q[p, q] = -(a[j] * a[k] * s / 2) * val
    # pole part (zeta only): int g(u) 2 cosh(u/2) du = A1 B2 + B1 A2
    if kind == 'zeta':
        if sector == 'even':
            v = [a[j] * (-1) ** j * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4) for j in idx]
            for p in range(M):
                for q in range(M):
                    Q[p, q] += 2 * v[p] * v[q]
        else:
            b = [a[j] * (-1) ** j * (j * om) * mp.sinh(L / 4) / ((j * om) ** 2 + mp.mpf(1) / 4)
                 for j in idx]
            for p in range(M):
                for q in range(M):
                    Q[p, q] += -8 * b[p] * b[q]
    # prime part: -2 sum Lambda(n) n^{-1/2} g_e(log n)
    for n in range(2, nmax + 1):
        if Lam[n] == 0:
            continue
        y = mp.log(n)
        coef = -2 * Lam[n] / mp.sqrt(n)
        sn = {k: mp.sin(k * om * y) for k in idx}
        cs = {k: mp.cos(k * om * y) for k in idx}
        for p, j in enumerate(idx):
            for q in range(p, M):
                k = idx[q]
                if j == k:
                    if k == 0:
                        g = (L - y) / L
                    else:
                        g = ((L - y) * cs[k] - sgn * sn[k] / (k * om)) / L
                else:
                    s = (-1) ** (j + k)
                    g = (a[j] * a[k] * s / 2) * ((sn[k] - sn[j]) / ((j - k) * om)
                                                 - sgn * (sn[j] + sn[k]) / ((j + k) * om))
                Q[p, q] += coef * g
                if q != p:
                    Q[q, p] += coef * g
    return Q, L


def boundary_functional(L, N, sector):
    """l with l^T c = f(L/2) (even sector) or f'(L/2) (odd sector) for f = sum c_k basis_k."""
    om = 2 * mp.pi / L
    if sector == 'even':
        return [1 / mp.sqrt(L)] + [mp.sqrt(2 / L) * (-1) ** k for k in range(1, N + 1)]
    return [mp.sqrt(2 / L) * (k * om) * (-1) ** k for k in range(1, N + 1)]


def omega2(L, N, sector):
    om = 2 * mp.pi / L
    ks = range(0, N + 1) if sector == 'even' else range(1, N + 1)
    return [(k * om) ** 2 for k in ks]


# ---------------------------------------------------------------- transforms and their zeros
def transform(c, L, z, sector='even'):
    """F(z) = int f(u) e^{izu} du for f = sum c_k basis_k.
    even: F(z) = (2 sin(zL/2)/z) h(z^2),  h(w) = c_0 L^{-1/2} + sum_k d_k w/(w - (k w)^2),
          d_k = c_k (2/L)^{1/2} (-1)^k;
    odd:  F(z) = 2i sin(zL/2) h_o(z^2),   h_o(w) = sum_k e_k/(w - (k w)^2),
          e_k = c_k (2/L)^{1/2} (-1)^k (k w)."""
    om = 2 * mp.pi / L
    w = z * z
    if sector == 'even':
        h = c[0] / mp.sqrt(L)
        for k in range(1, len(c)):
            h += c[k] * mp.sqrt(2 / L) * (-1) ** k * w / (w - (k * om) ** 2)
        return 2 * mp.sin(z * L / 2) / z * h
    ho = 0
    for i in range(len(c)):
        k = i + 1
        ho += c[i] * mp.sqrt(2 / L) * (-1) ** k * (k * om) / (w - (k * om) ** 2)
    return 2j * mp.sin(z * L / 2) * ho


def w_roots(c, L, sector='even'):
    """Roots w of the secular function h (even) or h_o (odd): the zeros of F are +-sqrt(w) (plus
    the trivial zeros +-k w, k > N, of sin(zL/2), and z = 0 in the odd sector).  Computed as the
    eigenvalues of an arrowhead-type matrix diag(delta) + u 1^T (secular equation)."""
    om = 2 * mp.pi / L
    if sector == 'even':
        d = [c[k] * mp.sqrt(2 / L) * (-1) ** k for k in range(1, len(c))]
        delta = [(k * om) ** 2 for k in range(1, len(c))]
        # h(w) = alpha + sum_k beta_k/(w - delta_k), alpha = c0 L^{-1/2} + sum d_k, beta_k = d_k delta_k
        alpha = c[0] / mp.sqrt(L) + sum(d)
        beta = [d[i] * delta[i] for i in range(len(d))]
        n = len(delta)
        A = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                A[i, j] = -beta[i] / alpha
            A[i, i] += delta[i]
        ev = mp.eig(A, left=False, right=False)
        return list(ev)
    e = [c[i] * mp.sqrt(2 / L) * (-1) ** (i + 1) * ((i + 1) * om) for i in range(len(c))]
    delta = [((i + 1) * om) ** 2 for i in range(len(c))]
    # h_o(w) = sum e_k/(w - delta_k): N-1 roots; eigenvalues of the deflated pencil.  Use
    # h_o(w) = 0  <=>  e_N + sum_{k<N} e_k (w - delta_N)/(w - delta_k) = 0 multiplied out:
    #   (sum_k e_k) + sum_{k<N} e_k (delta_k - delta_N)/(w - delta_k) = 0
    alpha = sum(e)
    n = len(delta) - 1
    beta = [e[i] * (delta[i] - delta[-1]) for i in range(n)]
    A = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            A[i, j] = -beta[i] / alpha
        A[i, i] += delta[i]
    ev = mp.eig(A, left=False, right=False)
    return list(ev)


def classify_w(ws, tol):
    """Count secular roots in the open upper half w-plane, on the negative real axis, and on the
    positive real axis (|Im w| <= tol |w| counts as real)."""
    up = sum(1 for w in ws if mp.im(w) > tol * max(1, abs(w)))
    down = sum(1 for w in ws if mp.im(w) < -tol * max(1, abs(w)))
    neg = sum(1 for w in ws if abs(mp.im(w)) <= tol * max(1, abs(w)) and mp.re(w) < 0)
    pos = len(ws) - up - down - neg
    return up, down, neg, pos
