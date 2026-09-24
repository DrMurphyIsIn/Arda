"""Float (non-rigorous) implementation of the Polymath15 quantities, for exploration only.

Source: D.H.J. Polymath, "Effective approximation of heat flow evolution of the Riemann xi
function, and a new upper bound for the de Bruijn-Newman constant", Res. Math. Sci. 6 (2019),
arXiv:1904.12438v2 ("P15").  Equation numbers below refer to arXiv v2.

Everything here is double precision / mpmath and is NOT a certificate.  The certified versions
live in p15_arb.py (python-flint / Arb ball arithmetic).  The formulas are kept textually parallel
so the two can be cross-checked (see selftest.py).

Conventions (P15 section 1, identical to the dbn island DBNDefs.lean):
    Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u})
    H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du,     H_0(z) = xi(1/2 + i z/2) / 8.
"""
import cmath
import math

import mpmath
import numpy as np

PI = math.pi


# --- P15 (6)-(10): M_0, alpha, M_t --------------------------------------------------------------

def alpha(s):
    """P15 (9): alpha(s) = 1/(2s) + 1/(s-1) + (1/2) Log(s/(2 pi))."""
    return 1 / (2 * s) + 1 / (s - 1) + 0.5 * cmath.log(s / (2 * PI))


def log_M0(s):
    """P15 (7): log M_0(s) = Log s + Log(s-1) - (s/2) log pi + log(sqrt(2 pi)/16)
    + (s/2 - 1/2) Log(s/2) - s/2."""
    return (cmath.log(s) + cmath.log(s - 1) - (s / 2) * math.log(PI)
            + math.log(math.sqrt(2 * PI) / 16) + (s / 2 - 0.5) * cmath.log(s / 2) - s / 2)


def log_Mt(t, s):
    """P15 (10): M_t(s) = exp((t/4) alpha(s)^2) M_0(s)."""
    return (t / 4) * alpha(s) ** 2 + log_M0(s)


def N_of(x, t):
    """P15 (19): N = floor(sqrt(x/(4 pi) + t/16))."""
    return int(math.floor(math.sqrt(x / (4 * PI) + t / 16)))


# --- P15 (14)-(18): f_t -------------------------------------------------------------------------

def ft_parts(x, y, t, N=None):
    """Return dict with f_t(x+iy) and its ingredients (P15 (14)-(18))."""
    if N is None:
        N = N_of(x, t)
    sp = complex((1 + y) / 2, -x / 2)          # s_+ = (1+y-ix)/2
    sm = complex((1 - y) / 2, x / 2)           # s_- = (1-y+ix)/2
    al_sp = alpha(sp)
    sstar = sp + (t / 2) * al_sp                # (17)
    kappa = (t / 2) * (alpha(sm) - al_sp.conjugate())   # (18); alpha((1+y+ix)/2) = conj alpha(s_+)
    lgam = log_Mt(t, sm) - log_Mt(t, sp)        # (16)
    gam = cmath.exp(lgam)
    n = np.arange(1, N + 1, dtype=float)
    ln = np.log(n)
    bn = np.exp((t / 4) * ln * ln)             # (15)
    S1 = np.sum(bn * np.exp(-sstar * ln))
    S2 = np.sum(bn * np.exp(y * ln) * np.exp(-(sstar.conjugate() + kappa) * ln))
    f = S1 + gam * S2
    return dict(f=f, N=N, sstar=sstar, kappa=kappa, gamma=gam, S1=S1, S2=S2,
                sp=sp, sm=sm, bn=bn, ln=ln)


def Ct_over_Bt(x, y, t):
    """P15 Corollary 6.4: C_t(x+iy) / B_t(x+iy)."""
    Tp = x / 2 + PI * t / 8
    a = math.sqrt(Tp / (2 * PI))
    N = int(math.floor(a))
    p = 1 - 2 * (a - N)
    U = cmath.exp(-1j * ((Tp / 2) * math.log(Tp / (2 * PI)) - Tp / 2 - PI / 8))
    C0 = (cmath.exp(PI * 1j * (p * p / 2 + 3 / 8)) - 1j * math.sqrt(2) * math.cos(PI * p / 2)) / (2 * math.cos(PI * p))
    lM0 = log_M0(complex(0, Tp))
    sp = complex((1 + y) / 2, -x / 2)
    lBt = log_Mt(t, sp)
    # C_t = 2 e^{-pi i y/8} (-1)^N exp(t pi^2/64) Re(M0(iT') C0 U e^{pi i/8});
    # divide by B_t = M_t(s_+).  Work with the ratio M0(iT')/B_t to avoid underflow.
    ratio = cmath.exp(lM0 - lBt)               # M0(iT') / B_t
    phase_Bt = cmath.exp(1j * (lBt.imag))      # B_t / |B_t|
    # Re(M0 C0 U e^{i pi/8}) / B_t = |M0|/|B_t| * Re(e^{i arg M0} C0 U e^{i pi/8}) / phase_Bt
    absr = abs(ratio)
    argM0 = cmath.exp(1j * lM0.imag)
    re_part = (argM0 * C0 * U * cmath.exp(1j * PI / 8)).real
    C = 2 * cmath.exp(-PI * 1j * y / 8) * ((-1) ** N) * math.exp(t * PI * PI / 64) * absr * re_part / phase_Bt
    return C


# --- P15 (44), (59), (71)-(74): error terms -------------------------------------------------

def eps_tn(t, s, ln):
    """P15 (44) at s = sigma + iT (T = |Im s|), vectorised over ln = log n."""
    T = abs(s.imag)
    a = alpha(complex(s.real, T))
    d = np.abs(a - ln) ** 2
    return np.expm1(((t * t / 8) * d + t / 4 + 1 / 6) / (T - 3.33))


def eps_tilde(t, sigma, T):
    """P15 (59): (0.397*9^sigma/(a-0.865) + 5/(3(T-6))) exp(3.49/(T-4)), a = sqrt((T+pi t/8)/(2 pi))."""
    a = math.sqrt((T + PI * t / 8) / (2 * PI))
    return (0.397 * 9 ** sigma / (a - 0.865) + 5 / (3 * (T - 6))) * math.exp(3.49 / (T - 4))


def error_terms(x, y, t, parts=None):
    """Exact P15 error quantities e_A, e_B, e_C, e_C0 ((71)-(74)); valid in region (5):
    0 < t <= 1/2, 0 <= y <= 1, x >= 200."""
    if parts is None:
        parts = ft_parts(x, y, t)
    ln, bn = parts['ln'], parts['bn']
    sstar, kappa, gam = parts['sstar'], parts['kappa'], parts['gamma']
    sp, sm = parts['sp'], parts['sm']
    eA = abs(gam) * np.sum(np.exp(y * ln) * bn * np.exp(-(sstar.real + kappa.real) * ln) * eps_tn(t, sm, ln))
    eB = np.sum(bn * np.exp(-sstar.real * ln) * eps_tn(t, sp, ln))
    Tp = x / 2 + PI * t / 8
    common = math.exp(t * PI * PI / 64) * math.exp((log_M0(complex(0, Tp)) - log_Mt(t, sp)).real)
    et = eps_tilde(t, (1 - y) / 2, x / 2) + eps_tilde(t, (1 + y) / 2, x / 2)
    return dict(eA=eA, eB=eB, eC=common * et, eC0=common * (1 + et))


# --- Direct evaluation for small x (P15 (35): heat-kernel average of xi) ------------------------

def xi(s):
    s = mpmath.mpc(s)
    return 0.5 * s * (s - 1) * mpmath.power(mpmath.pi, -s / 2) * mpmath.gamma(s / 2) * mpmath.zeta(s)


def Ht_direct(x, y, t, dps=30):
    """H_t(x+iy) = int_R (1/8) xi((1-y+ix)/2 + sqrt(t) v) e^{-v^2}/sqrt(pi) dv  (P15 (35))."""
    with mpmath.workdps(dps):
        rt = mpmath.sqrt(t)
        s0 = mpmath.mpc((1 - y) / 2, x / 2)
        f = lambda v: xi(s0 + rt * v) * mpmath.exp(-v * v)
        val = mpmath.quad(f, [-12, -4, -1, 0, 1, 4, 12]) / (8 * mpmath.sqrt(mpmath.pi))
        return complex(val)


def Bt(x, y, t):
    return cmath.exp(log_Mt(t, complex((1 + y) / 2, -x / 2)))
