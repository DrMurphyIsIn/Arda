"""Certified (Arb ball arithmetic, python-flint) implementation of the Polymath15 quantities.

Reference: D.H.J. Polymath, arXiv:1904.12438v2 (Res. Math. Sci. 6 (2019) art. 31), "P15".
Every function accepts acb/arb *balls*; the result encloses the exact value for every point of
the input balls.  "Certified" in this project means: a rigorous consequence of (a) Arb's
enclosure semantics, (b) the published P15 theorems quoted in README.md, section 2.

Objects (P15 numbering):
  alpha (9), log M_0 (7), M_t (10), gamma (16), s_* (17), kappa (18), N (19), f_t (14),
  C_t (Cor 6.4), eps_{t,n} (44), eps~ (59), e_A e_B e_C e_{C,0} (71)-(74).
In the notation used here, with z = x + iy and s_+ = (1 - iz)/2, s_- = (1 + iz)/2,
    w_+ = s_+ + (t/2) alpha(s_+)   (= s_*),      w_- = s_- + (t/2) alpha(s_-)   (= conj(s_*) + kappa - y),
    f_t(z) = sum_{n<=N} b_n n^{-w_+} + gamma(z) sum_{n<=N} b_n n^{-w_-},   gamma = M_t(s_-)/M_t(s_+),
which is P15 (14) rewritten; it is holomorphic in z on every N-segment [x_N, x_{N+1}).
"""
from flint import arb, acb, ctx

I = acb(0, 1)


def PI():
    return arb.pi()


# --------------------------------------------------------------------------------------------
# P15 (7)-(10)
# --------------------------------------------------------------------------------------------

def alpha(s):
    return 1 / (2 * s) + 1 / (s - 1) + (s / (2 * PI())).log() / 2


def alpha_p(s):
    """alpha'(s) = -1/(2 s^2) - 1/(s-1)^2 + 1/(2 s)   (P15 (42))."""
    return -1 / (2 * s * s) - 1 / ((s - 1) * (s - 1)) + 1 / (2 * s)


def log_M0(s):
    pi = PI()
    return (s.log() + (s - 1).log() - (s / 2) * pi.log() + ((2 * pi).sqrt() / 16).log()
            + (s / 2 - arb(1) / 2) * (s / 2).log() - s / 2)


def log_Mt(t, s):
    a = alpha(s)
    return (t / 4) * a * a + log_M0(s)


def dlog_Mt(t, s):
    """d/ds log M_t(s) = (t/2) alpha alpha' + alpha."""
    a = alpha(s)
    return (t / 2) * a * alpha_p(s) + a


def N_range(x_lo, x_hi, t):
    """N = floor(sqrt(x/(4 pi) + t/16)) at both ends (t may be a ball); returns (N_lo, N_hi) as
    rigorous integers, or None if a floor is ambiguous."""
    out = []
    for x in (x_lo, x_hi):
        a = (arb(x) / (4 * PI()) + arb(t) / 16).sqrt()
        fl = a.floor()
        u = fl.unique_fmpz() if hasattr(fl, 'unique_fmpz') else None
        if u is None:
            lo, hi = int(a.lower().floor().mid()), int(a.upper().floor().mid())
            if lo != hi:
                return None
            out.append(lo)
        else:
            out.append(int(u))
    return tuple(out)


def xN(N, t):
    """x_N = 4 pi N^2 - pi t/4 : the smallest x with floor(sqrt(x/4pi + t/16)) = N."""
    return 4 * PI() * N * N - PI() * arb(t) / 4


# --------------------------------------------------------------------------------------------
# Dirichlet data
# --------------------------------------------------------------------------------------------

class Coeffs:
    """log n and b_n^t = exp((t/4) log^2 n) for n = 1..Nmax, for a fixed t (arb ball ok)."""

    def __init__(self, t, Nmax):
        self.t = arb(t)
        self.ln = [arb(0)] + [arb(n).log() for n in range(2, Nmax + 1)]
        self.bn = [arb(1)] + [((self.t / 4) * l * l).exp() for l in self.ln[1:]]
        self.Nmax = Nmax

    def extend(self, Nmax):
        for n in range(self.Nmax + 1, Nmax + 1):
            l = arb(n).log()
            self.ln.append(l)
            self.bn.append(((self.t / 4) * l * l).exp())
        self.Nmax = max(self.Nmax, Nmax)


def ft_all(z, t, N, C, want_deriv=True, want_err=True, want_C=True, moll=None):
    """Evaluate on the ball z (N fixed on the ball):
        f      = f_t(z)                                   (P15 (14))
        df     = f_t'(z)                                  (complex derivative)
        err_AB = e_A + e_B (upper bound, exact defs (71),(72))
        common = exp(t pi^2/64) |M_0(iT')| / |M_t(s_+)|   (so e_C0 = common (1 + et), e_C = common * et)
        et     = eps~(s_-) + eps~(s_+)                   (59)
        CB     = C_t(z)/B_t(z)  (or None if the C_0(p) enclosure is not finite)
        E      = Euler mollifier prod_{p in moll} (1 - b_p p^{-w_+})   (optional)
    """
    t = arb(t)
    pi = PI()
    sp = (1 - I * z) / 2
    sm = (1 + I * z) / 2
    ap, am = alpha(sp), alpha(sm)
    wp = sp + (t / 2) * ap
    wm = sm + (t / 2) * am
    lMt_p = (t / 4) * ap * ap + log_M0(sp)
    lMt_m = (t / 4) * am * am + log_M0(sm)
    gam = (lMt_m - lMt_p).exp()
    Sp = acb(0)
    Sm = acb(0)
    Spd = acb(0)
    Smd = acb(0)
    ln, bn = C.ln, C.bn
    for n in range(N):
        l = ln[n]
        b = bn[n]
        ep = b * (-wp * l).exp()
        em = b * (-wm * l).exp()
        Sp += ep
        Sm += em
        if want_deriv and n > 0:
            Spd += ep * l
            Smd += em * l
    out = {}
    f = Sp + gam * Sm
    out['f'] = f
    out['gamma'] = gam
    out['wp'] = wp
    if want_deriv:
        dwp = (-I / 2) * (1 + (t / 2) * alpha_p(sp))
        dwm = (I / 2) * (1 + (t / 2) * alpha_p(sm))
        dgam = gam * (I / 2) * (dlog_Mt(t, sm) + dlog_Mt(t, sp))
        out['df'] = -dwp * Spd + dgam * Sm - gam * dwm * Smd
    if want_err:
        x = z.real
        y = z.imag
        T = x / 2
        agam = gam.abs_upper()
        eA = arb(0)
        eB = arb(0)
        # eps_{t,n}(s) = expm1((t^2/8 |alpha(s) - log n|^2 + t/4 + 1/6)/(T - 3.33)), T = |Im s| = x/2
        den = T - arb('3.33')
        base = t / 4 + arb(1) / 6
        for n in range(N):
            l = ln[n]
            b = bn[n]
            epsp = ((t * t / 8) * ((ap - l).abs_upper() ** 2) + base) / den
            epsm = ((t * t / 8) * ((am - l).abs_upper() ** 2) + base) / den
            eB += b * (-(wp.real) * l).exp() * epsp.expm1()
            eA += b * (-(wm.real) * l).exp() * epsm.expm1()
        out['err_AB'] = (agam * eA + eB).upper()
        Tp = T + pi * t / 8
        common = (t * pi * pi / 64 + (log_M0(I * Tp) - lMt_p).real).exp()
        a = (Tp / (2 * pi)).sqrt()
        et = arb(0)
        for sig in ((1 - y) / 2, (1 + y) / 2):
            et += (arb('0.397') * arb(9) ** sig / (a - arb('0.865')) + arb(5) / (3 * (T - 6))) * (arb('3.49') / (T - 4)).exp()
        out['common'] = common.upper()
        out['et'] = et.upper()
        if want_C:
            out['CB'] = Ct_over_Bt(z, t, lMt_p, Tp=Tp, N=N)
    if moll is not None:
        E = acb(1)
        for p in moll:
            lp = arb(p).log()
            E *= 1 - ((t / 4) * lp * lp).exp() * (-wp * lp).exp()
        out['E'] = E
    return out


def C0_of_p(p):
    """P15 (53) with the removable singularities at p = +-1/2 handled by the mean-value form."""
    pi = PI()
    half = arb(1) / 2

    def Nf(q):
        return (pi * I * (q * q / 2 + arb(3) / 8)).exp() - I * arb(2).sqrt() * (pi * q / 2).cos()

    def Nfp(q):
        return pi * I * q * (pi * I * (q * q / 2 + arb(3) / 8)).exp() + I * arb(2).sqrt() * (pi / 2) * (pi * q / 2).sin()

    c = (pi * p).cos()
    if not c.contains(0) and float(c.abs_lower()) > 1e-3:
        return Nf(acb(p)) / (2 * c)
    for s0 in (half, -half):
        h = p - s0
        if float(h.abs_upper()) < 0.05:
            # cos(pi p) = cos(pi s0 + pi h) = -sgn(s0) sin(pi h); N(s0 + h) = h * mean(N'(s0 + [0,1] h))
            hb = arb(0).union(h)
            Np = Nfp(acb(s0 + hb))
            sinc = (pi * h).sinc()          # sin(pi h)/(pi h), analytic at 0
            sgn = -1 if s0 > 0 else 1
            # C0 = N(s0+h) / (2 cos(pi p)) = h Np / (2 * sgn * sin(pi h)) = Np / (2 sgn pi sinc)
            return Np / (2 * sgn * pi * sinc)
    return Nf(acb(p)) / (2 * c)


def Ct_over_Bt(z, t, lMt_p=None, Tp=None, N=None):
    """C_t(z)/B_t(z) with C_t from P15 Cor 6.4:
        C_t = 2 e^{-pi i y/8} (-1)^N exp(t pi^2/64) Re(M_0(iT') C_0(p) U e^{pi i/8}),  B_t = M_t(s_+)."""
    t = arb(t)
    pi = PI()
    x, y = z.real, z.imag
    if Tp is None:
        Tp = x / 2 + pi * t / 8
    a = (Tp / (2 * pi)).sqrt()
    if N is None:
        N = int(a.floor().mid())
    p = 1 - 2 * (a - N)
    U = (-I * ((Tp / 2) * (Tp / (2 * pi)).log() - Tp / 2 - pi / 8)).exp()
    C0 = C0_of_p(p)
    if lMt_p is None:
        lMt_p = log_Mt(t, (1 - I * z) / 2)
    # Re(M_0(iT') C_0 U e^{i pi/8}) / B_t ; M_0(iT')/B_t computed in log form
    lM0 = log_M0(I * Tp)
    # write M_0(iT') = exp(lM0);  Re(exp(lM0) W) = |exp(lM0)| Re(exp(i Im lM0) W)
    W = (I * lM0.imag).exp() * C0 * U * (pi * I / 8).exp()
    re = W.real * (lM0.real).exp()
    val = 2 * (-pi * I * y / 8).exp() * (t * pi * pi / 64).exp() * re * (-lMt_p).exp()
    if N % 2 == 1:
        val = -val
    return val


# --------------------------------------------------------------------------------------------
# Direct evaluation of H_t(z) for small x via the heat-kernel form P15 (35)
#   H_t(z) = (1/(8 sqrt(pi))) int_R xi((1+iz)/2 + sqrt(t) v) e^{-v^2} dv
# --------------------------------------------------------------------------------------------

def xi(s):
    """Riemann xi(s) = s(s-1)/2 pi^{-s/2} Gamma(s/2) zeta(s) (entire).  Uses xi(s) = xi(1-s)
    when Re s < 1/2 (same entire function, so the enclosure is valid on every ball)."""
    if float(s.real.mid()) < 0.5:
        s = 1 - s
    pi = PI()
    return s * (s - 1) / 2 * pi ** (-s / 2) * (s / 2).gamma() * s.zeta()


def xi_and_deriv(s):
    """(xi(s), xi'(s)) via Arb power series (length 2)."""
    from flint import acb_series
    flip = float(s.real.mid()) < 0.5
    if flip:
        s = 1 - s
    old = ctx.cap
    ctx.cap = 2
    try:
        S = acb_series([s, 1])
        pi = PI()
        val = S * (S - 1) / 2 * (-(S / 2) * pi.log()).exp() * (S / 2).gamma() * S.zeta()
        c = val.coeffs()
        v0 = c[0] if len(c) > 0 else acb(0)
        v1 = c[1] if len(c) > 1 else acb(0)
    finally:
        ctx.cap = old
    if flip:
        v1 = -v1       # d/ds xi(1-s) = -xi'(1-s)
    return v0, v1


def _tail_bound(T, t, V, y_abs_max, weight_pow=0):
    """Rigorous bound for (1/(8 sqrt pi)) int_{|v|>V} |xi(s(v))| |v|^k e^{-v^2} dv, s(v) =
    (1-y)/2 + sqrt(t) v + iT, using for sigma' := max(sigma,1-sigma) >= 2:
        |xi(s)| <= 0.825 (sigma'^2 + T^2) pi^{-1} Gamma(sigma'/2)   (|Gamma(a+ib)| <= Gamma(a), zeta(sigma') <= zeta(2))
    and sigma' <= 1 + |y|/2 + sqrt(t)|v|;  g(v) = bound * v^k e^{-v^2} satisfies g(V+u) <= g(V) e^{-V u}
    for V >= 8 (checked numerically at call sites), so int_V^inf g <= g(V)/V."""
    rt = arb(t).sqrt()
    sig = 1 + arb(y_abs_max) / 2 + rt * V
    # need sigma' >= 2 (zeta(sigma') <= zeta(2), pi^{-sigma'/2} <= 1/pi) and sigma'/2 >= 1.4616 (Gamma increasing)
    if float(sig.lower()) < 2.93 or V < 8:
        return None
    g = arb('0.825') * (sig * sig + arb(T) ** 2) / PI() * (sig / 2).gamma() * arb(V) ** weight_pow * (-arb(V) ** 2).exp()
    return 2 * g / V / (8 * PI().sqrt())


def Ht_direct(z, t, want_deriv=False, V=None, prec=None, rel_tol_bits=40):
    """Enclosure of H_t(z) (and optionally H_t'(z)) on the ball z via P15 (35).  t is an arb (ball ok),
    t >= 0.  The v-integral over [-V, V] is done by Arb's rigorous integrator; the tails are bounded
    by _tail_bound and added as a radius."""
    old = ctx.prec
    # |H_t(x+iy)| is of size ~exp(-pi x/8); Arb's integrator stops at max(abs_tol, rel_tol*|I|), so the
    # absolute tolerance and the working precision must be scaled to that size (else it stops early
    # and returns a correct but useless wide ball).
    xmax = float(z.real.abs_upper())
    scale_bits = int(1.4427 * 3.1416 * xmax / 8) + 1
    need = scale_bits + rel_tol_bits + 64
    ctx.prec = max(prec or 0, need, old)
    abs_tol = arb(2) ** (-(scale_bits + rel_tol_bits + 20))
    try:
        t = arb(t)
        pi = PI()
        s0 = (1 + I * z) / 2
        rt = t.sqrt() if float(t.upper()) > 0 else arb(0)
        T = float(z.real.upper()) / 2
        if V is None:
            V = int((3.1416 * T / 4 + 80) ** 0.5) + 4
        V = max(V, 9)
        yabs = float(z.imag.abs_upper())
        c = 1 / (8 * pi.sqrt())
        if float(t.upper()) == 0.0:
            if want_deriv:
                v0, v1 = xi_and_deriv(s0)
                return v0 / 8, (I / 2) * v1 / 8
            return xi(s0) / 8
        rt_ok = True
        f0 = lambda v, a: xi(s0 + rt * v) * (-(v * v)).exp()
        tol = arb(2) ** (-rel_tol_bits)
        H = acb.integral(f0, -V, V, rel_tol=tol, abs_tol=abs_tol, eval_limit=400000) * c
        tb = _tail_bound(T, t.upper(), V, yabs, 0)
        if tb is None:
            raise ValueError('tail bound not applicable')
        H += acb(arb(0, tb.upper()), arb(0, tb.upper()))
        if not want_deriv:
            return H
        f1 = lambda v, a: xi_and_deriv(s0 + rt * v)[1] * (-(v * v)).exp()
        D = acb.integral(f1, -V, V, rel_tol=tol, abs_tol=abs_tol, eval_limit=400000) * c * (I / 2)
        # tail for xi': Cauchy on a unit disk: |xi'(s)| <= max_{|w-s|=1}|xi(w)|, i.e. sigma'+1 in the bound
        tb1 = _tail_bound(T + 1, t.upper(), V, yabs + 2, 0)
        D += acb(arb(0, tb1.upper()), arb(0, tb1.upper()))
        return H, D
    finally:
        ctx.prec = old


# --------------------------------------------------------------------------------------------
# Direct evaluation from the definition (P15 (4)), for small x and any 0 <= t <= 1/2:
#   H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du,
#   Phi(u) = sum_{n>=1} (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u}).
# Used for the barrier at X = 55/8 and for condition (i) there (x <= 8, no cancellation issue).
# --------------------------------------------------------------------------------------------

def Phi_trunc(u, nmax):
    pi = PI()
    e4 = (4 * u).exp()
    e5 = (5 * u).exp()
    e9 = (9 * u).exp()
    s = 0
    for n in range(1, nmax + 1):
        n2 = n * n
        s += (2 * pi * pi * n2 * n2 * e9 - 3 * pi * n2 * e5) * (-pi * n2 * e4).exp()
    return s


def Ht_phi(z, t, U=arb('1.25'), nmax=6, rel_tol_bits=50):
    """Enclosure of H_t(z) for a ball z (|Re z| small), 0 <= t <= 1/2 (ball ok), via P15 (4).
    Error terms (rigorous, README 4.1):
      n > nmax truncation on [0,U]:  sum_{n>nmax} (2pi^2 n^4 + 3 pi n^2) e^{-pi n^2} * U e^{tU^2} cosh(|y|U)
      u > U tail:                    e^{tU^2} cosh(|y|U) e^{9U} (2pi^2 + 3pi) * 2 e^{-pi e^{4U}}   (needs pi e^{4U} >= 10)
    """
    pi = PI()
    t = arb(t)
    U = arb(U)
    zz = z
    f = lambda u, a: (t * u * u).exp() * Phi_trunc(u, nmax) * (zz * u).cos()
    val = acb.integral(f, 0, U, rel_tol=arb(2) ** (-rel_tol_bits), eval_limit=200000)
    yabs = z.imag.abs_upper()
    tu = t.upper()
    trunc = arb(0)
    for n in range(nmax + 1, nmax + 40):
        n2 = n * n
        trunc += (2 * pi * pi * n2 * n2 + 3 * pi * n2) * (-pi * n2).exp()
    trunc = trunc * 2        # geometric remainder beyond nmax+39 is far below this factor-2 slack
    trunc = trunc * U * (tu * U * U).exp() * (yabs * U).cosh()
    W = (4 * U).exp()
    assert float((pi * W).lower()) >= 10
    tail = (tu * U * U).exp() * (yabs * U).cosh() * (9 * U).exp() * (2 * pi * pi + 3 * pi) * 2 * (-pi * W).exp()
    r = (trunc + tail).upper()
    return val + acb(arb(0, r), arb(0, r))
