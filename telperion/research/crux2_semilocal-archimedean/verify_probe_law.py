"""Independent (builder-stage) verification of the load-bearing step of the semi-local horizon.

conjecture1_proved = False.  Nothing here is about the location of zeta zeros beyond using the
first 2000 zeros (all verified on the critical line) to EVALUATE a zero sum.

Checks, all in the normalisation Phi(u) = sum_n (4 pi^2 n^4 e^{9u/2} - 6 pi n^2 e^{5u/2}) e^{-pi n^2 e^{2u}}:
  (1) Phi^ = Xi: 2 int_0^oo Phi(u) cos(tu) du = xi(1/2 + it)   (mpmath, t = 0, 5, 10, gamma_1)
  (2) Phi' < 0 on (0, 3]                                      (Csordas-Norfolk-Varga; grid check)
  (3) overlap h(log q) of the sharp probe g_x = Phi' 1_[-L/2, L/2] against
        leading form  64 pi^6 q^{11/2} Delta e^{-2 pi q}
        refined form  32 pi^6 q^{13/2} e^{-2 pi q} int_{-eps}^{eps} e^{-2 pi q (cosh w - 1)} dw,  eps = log(x/q)
  (4) full value Q(g_x) from the zero side, sum_rho |tail^(gamma)|^2 (first 2000 zeros + density
      tail), against the asymptotic Phi'(L/2)^2 log x/(2 pi x)
  (5) probe onset Delta(q): smallest x - q with Q(g_x) + 2 (log q/sqrt q) h(log q) < 0, against the
      law  Delta e^{2 pi Delta} = sqrt(q)/(4 pi),  i.e.  Delta = W0(sqrt q / 2)/(2 pi)
All exponentially small quantities are carried scaled by e^{2 pi q} (one factor e^{pi q} per Phi').
Output: verify_probe_law.json (+ stdout).
"""
import json
import os
import numpy as np
import mpmath as mp
from scipy.special import lambertw
from scipy.optimize import brentq

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = np.array(json.load(open(os.path.join(HERE, '..', 'zeros2000.json'))), dtype=float)


# ------------------------------------------------------------------ the Polya kernel
def phi_mp(u, M=6):
    u = mp.mpf(u)
    return mp.fsum((4 * mp.pi**2 * n**4 * mp.e**(4.5 * u) - 6 * mp.pi * n**2 * mp.e**(2.5 * u))
                   * mp.e**(-mp.pi * n**2 * mp.e**(2 * u)) for n in range(1, M + 1))


def dphi_scaled(u, shift=0.0, M=6):
    """Phi'(u) * e^{shift} (odd in u), vectorised float64."""
    u = np.asarray(u, dtype=float)
    sgn = np.sign(u)
    v = np.abs(u)
    e2 = np.exp(2 * v)
    out = np.zeros_like(v)
    for n in range(1, M + 1):
        A = 4 * np.pi**2 * n**4 * np.exp(4.5 * v) - 6 * np.pi * n**2 * np.exp(2.5 * v)
        dA = 18 * np.pi**2 * n**4 * np.exp(4.5 * v) - 15 * np.pi * n**2 * np.exp(2.5 * v)
        with np.errstate(under='ignore', over='ignore'):
            E = np.exp(-np.pi * n * n * e2 + shift)
        out = out + (dA - A * 2 * np.pi * n * n * e2) * E
    return sgn * out


def gl(a, b, n):
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (a + b), 0.5 * (b - a) * w


def panels(a, b, npan, deg):
    X, W = [], []
    edges = np.linspace(a, b, npan + 1)
    for e0, e1 in zip(edges[:-1], edges[1:]):
        x, w = gl(e0, e1, deg)
        X.append(x)
        W.append(w)
    return np.concatenate(X), np.concatenate(W)


# ------------------------------------------------------------------ (1) normalisation
def check_xi():
    mp.mp.dps = 30
    rows = []
    for t in [0, 5, 10, 14.134725141734693790]:
        lhs = 2 * mp.quad(lambda u: phi_mp(u) * mp.cos(t * u), [0, 0.25, 0.5, 1, 2])
        s = mp.mpf(1) / 2 + 1j * t
        xi = 0.5 * s * (s - 1) * mp.pi**(-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
        rows.append(dict(t=float(t), phi_hat=float(lhs), xi=float(mp.re(xi)), abs_diff=float(abs(lhs - xi))))
    return rows


# ------------------------------------------------------------------ (2) sign of Phi'
def check_dphi_sign():
    u = np.linspace(1e-4, 3.0, 30001)
    d = dphi_scaled(u)
    # beyond u ~ 1.2 the value underflows to 0 in float64; check the scaled version there
    d2 = np.array([dphi_scaled(np.array([x]), shift=np.pi * np.exp(2 * x))[0] for x in u[::100]])
    return dict(max_unscaled=float(d.max()), n_neg=int((d < 0).sum()), n_zero_underflow=int((d == 0).sum()),
                max_scaled_on_subgrid=float(d2.max()))


# ------------------------------------------------------------------ (3) overlap
def overlap_scaled(q, x, npan=8, deg=60):
    """h_{g_x}(log q) * e^{2 pi q}."""
    L = np.log(x)
    lq = np.log(q)
    lo, hi = lq - L / 2, L / 2
    if lo >= hi:
        return 0.0
    v, w = panels(lo, hi, npan, deg)
    sh = np.pi * q
    return float(np.sum(w * dphi_scaled(v, sh) * dphi_scaled(v - lq, sh)))


def overlap_leading(q, x):
    return -64 * np.pi**6 * q**5.5 * (x - q)


def overlap_refined(q, x):
    eps = np.log(x / q)
    w, wt = gl(-eps, eps, 200)
    I = np.sum(wt * np.exp(-2 * np.pi * q * (np.cosh(w) - 1)))
    return -32 * np.pi**6 * q**6.5 * I


# ------------------------------------------------------------------ (4) zero-side full value
def q_zero_side_scaled(x, shift):
    """Q(g_x) * e^{2 shift}: sum over zeros of |tail^(gamma)|^2, tail = Phi' 1_{|u| > L/2}."""
    L = np.log(x)
    b = L / 2
    V, W = [], []
    for lo, hi, n in [(0, 0.004, 80), (0.004, 0.02, 80), (0.02, 0.08, 80), (0.08, 0.3, 80), (0.3, 1.5, 80)]:
        v, w = gl(b + lo, b + hi, n)
        V.append(v)
        W.append(w)
    v = np.concatenate(V)
    w = np.concatenate(W)
    d = dphi_scaled(v, shift)
    S = np.sin(np.outer(ZEROS, v)) @ (w * d)          # int_b^oo Phi' sin(gamma u) du
    main = np.sum(2 * (2 * S) ** 2)                   # |tail^|^2 = 4 S^2; zeros at +-gamma
    # density tail beyond the last zero: with Phi'(u) ~ Phi'(b) e^{-kappa (u - b)} near the edge,
    # |tail^(t)|^2 = 4 Phi'(b)^2 [kappa sin(tb) + t cos(tb)]^2/(kappa^2 + t^2)^2, average
    # 2 Phi'(b)^2/(kappa^2 + t^2); kappa = -Phi''(b)/Phi'(b) ~ 2 pi x (local decay rate).
    T = ZEROS[-1]
    db = dphi_scaled(np.array([b]), shift)[0]
    hstep = 1e-7
    kappa = -(dphi_scaled(np.array([b + hstep]), shift)[0] - db) / hstep / db
    tail = 2 * mp.quad(lambda t: (mp.log(t / (2 * mp.pi)) / (2 * mp.pi)) * 2 * db**2 / (kappa**2 + t**2),
                       [T, mp.inf])
    return float(main + tail), float(tail)


def q_asymptotic_scaled(x, shift):
    L = np.log(x)
    db = dphi_scaled(np.array([L / 2]), shift)[0]
    return float(db**2 * np.log(x) / (2 * np.pi * x))


def qs_scaled(q, delta):
    x = q + delta
    sh = np.pi * q
    Q, _ = q_zero_side_scaled(x, sh)
    h = overlap_scaled(q, x)
    return Q + 2 * np.log(q) / np.sqrt(q) * h, Q, h


def onset(q, lo=0.01, hi=1.2):
    f = lambda d: qs_scaled(q, d)[0]
    grid = np.linspace(lo, hi, 60)
    vals = [f(d) for d in grid]
    for (a, fa), (b, fb) in zip(zip(grid[:-1], vals[:-1]), zip(grid[1:], vals[1:])):
        if fa > 0 and fb < 0:
            return brentq(f, a, b, xtol=1e-5)
    return None


def main():
    out = {}
    out['xi_normalisation'] = check_xi()
    print('Phi^ = Xi:', out['xi_normalisation'], flush=True)
    out['dphi_sign'] = check_dphi_sign()
    print('Phi\' sign:', out['dphi_sign'], flush=True)
    rows = []
    for q in [7, 13, 47, 97, 199]:
        for delta in [0.1, 0.2]:
            x = q + delta
            h = overlap_scaled(q, x)
            rows.append(dict(q=q, delta=delta, h_scaled=h, ratio_leading=h / overlap_leading(q, x),
                             ratio_refined=h / overlap_refined(q, x)))
            print('overlap', rows[-1], flush=True)
    out['overlap'] = rows
    rows = []
    for q in [7, 13, 47, 97, 199]:
        x = q + 0.2
        sh = np.pi * q
        Q, tail = q_zero_side_scaled(x, sh)
        A = q_asymptotic_scaled(x, sh)
        rows.append(dict(q=q, x=x, Q_scaled=Q, density_tail_part=tail, ratio_to_asymptotic=Q / A))
        print('Q', rows[-1], flush=True)
    out['Q_zero_side'] = rows
    rows = []
    for q in [7, 11, 13, 23, 47, 97, 199]:
        d = onset(q)
        law = float(np.real(lambertw(np.sqrt(q) / 2)) / (2 * np.pi))
        rows.append(dict(q=q, probe_onset=d, W0_law=law, logq_over_4pi=float(np.log(q) / (4 * np.pi))))
        print('onset', rows[-1], flush=True)
    out['onsets'] = rows
    json.dump(out, open(os.path.join(HERE, 'verify_probe_law.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
