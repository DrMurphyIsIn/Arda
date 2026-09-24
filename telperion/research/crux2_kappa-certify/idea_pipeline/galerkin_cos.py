"""RIGOROUS Galerkin matrices of the (untruncated) window Weil form Q_x in the cosine / sine bases of
L^2[-L/2, L/2], L = log x, for F = zeta or Davenport-Heilbronn D -- Arb ball arithmetic throughout.

Closed forms of the build are those of telperion/research/crux_spectral-operator/wpw.py (validated there
by the displacement identity to 1e-40).  What is new here: every archimedean integral is replaced by an
EXACT closed form, so no quadrature error enters.  With W(u) = sum_j 2 e^{-beta_j u}, beta_j = beta0 + 2j
(zeta: W = e^{u/2}/sinh u, beta0 = 1/2;  D: W = e^{-u/2}/sinh u, beta0 = 3/2), k = m omega, omega = 2pi/L:
  S[m]  = int_0^L sin(ku) W  = Im psi(beta0/2 + ik/2) - sum_j 2k e^{-beta_j L}/(beta_j^2+k^2)
  Cc[m] = int_0^L (1-cos ku) W = Re psi((beta0+ik)/2) - psi(beta0/2) - sum_j 2 e^{-beta_j L} k^2/(beta_j(beta_j^2+k^2))
  Cu[m] = int_0^L u cos(ku) W = (1/2) Re psi'((beta0+ik)/2) - sum_j 2 e^{-beta_j L} Re[L/(beta_j-ik) + 1/(beta_j-ik)^2]
  CL    = psi(beta0/2) + c0 + sum_j 2 e^{-beta_j L}/beta_j,     c0 = -log pi (zeta), log(5/pi) (D)
(the psi / psi' pieces are the exact sums over j of the untruncated integrals; the e^{-beta_j L} series are
geometric and are truncated with an explicit tail ball).  Prime side exact (finite).  Pole (zeta only):
even +2 v v^T, odd -8 b b^T.
"""
import math
import flint
from flint import arb, acb, arb_mat


def von_mangoldt(nmax):
    lam = [arb(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        m, p = n, None
        for q in range(2, n + 1):
            if m % q == 0:
                p = q
                break
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = arb(p).log()
    return lam


def dh_kappa():
    s5 = arb(5).sqrt()
    return ((10 - 2 * s5).sqrt() - 2) / (s5 - 1)


def lambda_dh(nmax):
    k = dh_kappa()
    cval = {1: arb(1), 2: k, 3: -k, 4: arb(-1), 0: arb(0)}
    cs = [arb(0)] + [cval[n % 5] for n in range(1, nmax + 1)]
    lam = [arb(0)] * (nmax + 1)
    for n in range(2, nmax + 1):
        acc = cs[n] * arb(n).log()
        for d in range(2, n + 1):
            if n % d == 0:
                acc -= cs[d] * lam[n // d]
        lam[n] = acc
    return lam


def _geom_tail(coef_bound, beta_next, L):
    """ball [-B, B] with B = coef_bound e^{-beta_next L}/(1 - e^{-2L})."""
    B = coef_bound * (-beta_next * L).exp() / (1 - (-2 * L).exp())
    return arb(0, B.upper())


def integrals(L, N, kind):
    beta0 = arb(1) / 2 if kind == 'zeta' else arb(3) / 2
    c0 = -arb.pi().log() if kind == 'zeta' else (arb(5) / arb.pi()).log()
    om = 2 * arb.pi() / L
    # number of geometric terms: e^{-2 J L} < 2^{-(prec+20)}
    prec = flint.ctx.prec
    J = int(math.ceil((prec + 20) * math.log(2) / (2 * float(L.mid())))) + 2
    betas = [beta0 + 2 * j for j in range(J)]
    ebl = [(-b * L).exp() for b in betas]
    beta_next = beta0 + 2 * J
    psi_half = (beta0 / 2).digamma()
    S = []
    Cc = []
    Cu = []
    for m in range(N + 1):
        k = om * m
        z = acb(beta0 / 2, k / 2)
        dg = z.digamma()
        tg = z.polygamma(1)
        s_geo = arb(0)
        c_geo = arb(0)
        u_geo = arb(0)
        for b, e in zip(betas, ebl):
            den = b * b + k * k
            s_geo += 2 * k * e / den
            c_geo += 2 * e * k * k / (b * den)
            w = acb(b, -k)
            u_geo += 2 * e * (acb(L) / w + 1 / (w * w)).real
        s_geo += _geom_tail(arb(1) / beta0, beta_next, L)
        c_geo += _geom_tail(arb(2) / beta0, beta_next, L)
        u_geo += _geom_tail(2 * (L / beta0 + 1 / (beta0 * beta0)), beta_next, L)
        S.append(dg.imag - s_geo if m > 0 else arb(0))
        Cc.append(dg.real - psi_half - c_geo if m > 0 else arb(0))
        Cu.append(tg.real / 2 - u_geo)
    cl_geo = arb(0)
    for b, e in zip(betas, ebl):
        cl_geo += 2 * e / b
    cl_geo += _geom_tail(arb(2) / beta0, beta_next, L)
    CL = psi_half + c0 + cl_geo
    return S, Cc, Cu, CL


def build(x, N, kind='zeta', sector='even'):
    """Rigorous Galerkin matrix (arb_mat) of Q_x in the given sector.  x: arb (exact or ball)."""
    L = x.log() if isinstance(x, arb) else arb(x).log()
    om = 2 * arb.pi() / L
    S, Cc, Cu, CL = integrals(L, N, kind)
    nmax = int(math.floor(float(x.upper()) if isinstance(x, arb) else x))
    Lam = von_mangoldt(nmax) if kind == 'zeta' else lambda_dh(nmax)
    sgn = 1 if sector == 'even' else -1
    idx = list(range(0, N + 1)) if sector == 'even' else list(range(1, N + 1))
    M = len(idx)
    aa = {k: ((1 / L).sqrt() if k == 0 else (2 / L).sqrt()) for k in idx}
    Q = [[arb(0)] * M for _ in range(M)]
    for p, j in enumerate(idx):
        for q, k in enumerate(idx):
            if j == k:
                if k == 0:
                    v = Cu[0] / L + CL
                else:
                    v = Cc[k] + Cu[k] / L + sgn * S[k] / (k * om * L) + CL
            else:
                s = -1 if (j + k) % 2 else 1
                val = (S[k] - S[j]) / ((j - k) * om) - sgn * (S[j] + S[k]) / ((j + k) * om)
                v = -(aa[j] * aa[k] * s / 2) * val
            Q[p][q] = v
    if kind == 'zeta':
        sh = (L / 4).sinh()
        if sector == 'even':
            vv = [aa[j] * (-1) ** j * sh / ((j * om) ** 2 + arb(1) / 4) for j in idx]
            for p in range(M):
                for q in range(M):
                    Q[p][q] += 2 * vv[p] * vv[q]
        else:
            bb = [aa[j] * (-1) ** j * (j * om) * sh / ((j * om) ** 2 + arb(1) / 4) for j in idx]
            for p in range(M):
                for q in range(M):
                    Q[p][q] += -8 * bb[p] * bb[q]
    for n in range(2, nmax + 1):
        if Lam[n] == 0:
            continue
        if isinstance(x, arb) and x.is_exact() and x == n:
            continue        # n = x: g(log x) = g(L) = 0 exactly (the term vanishes identically)
        y = arb(n).log()
        if not (y < L):
            if y > L:
                continue
            raise ValueError("log n straddles L")
        coef = -2 * Lam[n] / arb(n).sqrt()
        sn = {k: (k * om * y).sin() for k in idx}
        cs = {k: (k * om * y).cos() for k in idx}
        for p, j in enumerate(idx):
            for q in range(p, M):
                k = idx[q]
                if j == k:
                    if k == 0:
                        g = (L - y) / L
                    else:
                        g = ((L - y) * cs[k] - sgn * sn[k] / (k * om)) / L
                else:
                    s = -1 if (j + k) % 2 else 1
                    g = (aa[j] * aa[k] * s / 2) * ((sn[k] - sn[j]) / ((j - k) * om)
                                                  - sgn * (sn[j] + sn[k]) / ((j + k) * om))
                Q[p][q] += coef * g
                if q != p:
                    Q[q][p] += coef * g
    return arb_mat(Q), L


def rayleigh(Q, c):
    """c^T Q c / c^T c for a list of exact arb coefficients (ball)."""
    n = Q.nrows()
    num = arb(0)
    den = arb(0)
    for i in range(n):
        den += c[i] * c[i]
        row = arb(0)
        for k in range(n):
            row += Q[i, k] * c[k]
        num += c[i] * row
    return num, den
