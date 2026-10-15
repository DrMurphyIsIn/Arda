"""WALL-3 track T helpers: certified finite power sums and Beurling zeta_P enclosures.

conjecture1_proved = False.  Nothing here is progress on RH.  Trust class of every output: ARB (python-flint
ball arithmetic) or EXACT (Fractions); neither is a kernel theorem.  The Beurling enclosure is CONDITIONAL on the
caller's remainder hypothesis |N(x) - A x| <= C x^theta for x >= X, which the sidecar records verbatim.

Run with ~/rh-team/wall2/T/venv/bin/python (it has python-flint and telperion; arb_fakes is on Arda main 2dfc6eeee, and t3tools is on the unpushed branch
wall3/telperion-certs).
"""
from __future__ import annotations

from fractions import Fraction

from flint import acb, acb_series, arb, ctx


# ------------------------------------------------------------------------------------------------ helpers
def _arb(x):
    if isinstance(x, arb):
        return x
    if isinstance(x, (int, Fraction)):
        x = Fraction(x)
        return arb(f"{x.numerator}/{x.denominator}")
    return arb(str(x))  # decimal string is read exactly ("0.1" is the rational 1/10, enclosed)


def _acb(z):
    """z as acb: an acb, a number, a decimal string, or a (re, im) pair of strings/Fractions."""
    if isinstance(z, acb):
        return z
    if isinstance(z, (tuple, list)):
        return acb(_arb(z[0]), _arb(z[1]))
    return acb(_arb(z))


def _frac(x: arb):
    from telperion.rh_jensen.coefficients import _arb_ball_to_fractions
    return _arb_ball_to_fractions(x)


# ------------------------------------------------------------------------------------------------ power sums
def gauss_pow_sum_exact(b, z, nu):
    """Exact S_nu = sum_j b_j z_j^nu for Gaussian rationals b_j, z_j given as (re, im) Fraction pairs.
    Returns (re, im, |S|^2) as Fractions."""
    sr = si = Fraction(0)
    for (br, bi), (zr, zi) in zip(b, z):
        pr, pi = Fraction(1), Fraction(0)
        zr, zi, br, bi = map(Fraction, (zr, zi, br, bi))
        for _ in range(nu):
            pr, pi = pr * zr - pi * zi, pr * zi + pi * zr
        sr += br * pr - bi * pi
        si += br * pi + bi * pr
    return sr, si, sr * sr + si * si


def powersum_certify(b, z, nus, lower=None, mode="min", prec=256, exact=False):
    """Certify a finite Turan-type power-sum bound.

    b, z: lists of coefficients and nodes (see _acb; for exact=True, (re, im) Fraction pairs).
    nus: iterable of integer exponents.
    mode="min": certify min_{nu in nus} |S_nu| >= lower   (every nu clears the bound)
    mode="max": certify max_{nu in nus} |S_nu| >= lower   (Turan's form: some nu clears it; the witness is recorded)
    If lower is None, return the best certified bound instead of a verdict.
    Returns a sidecar dict; |S_nu|^2 is compared with lower^2 in exact Fractions."""
    nus = list(nus)
    rows = []
    if exact:
        for nu in nus:
            _, _, m2 = gauss_pow_sum_exact(b, z, nu)
            rows.append((nu, m2, m2))
    else:
        old = ctx.prec
        ctx.prec = prec
        try:
            B = [_acb(x) for x in b]
            Z = [_acb(x) for x in z]
            for nu in nus:
                s = sum((bj * zj ** nu for bj, zj in zip(B, Z)), acb(0))
                m2 = s.real * s.real + s.imag * s.imag  # not ** 2: arb pow on a ball containing 0 is nan
                lo, hi = _frac(m2)
                rows.append((nu, max(lo, Fraction(0)), hi))
        finally:
            ctx.prec = old
    if mode == "min":
        nu_w, lo2, _ = min(rows, key=lambda r: r[1])
    elif mode == "max":
        nu_w, lo2, _ = max(rows, key=lambda r: r[1])
    else:
        raise ValueError("mode must be 'min' or 'max'")
    out = {"kind": "powersum_" + mode, "trust_class": "exact" if exact else "arb", "n_terms": len(b),
           "nu_range": [min(nus), max(nus)], "n_nu": len(nus), "witness_nu": nu_w,
           "certified_sq_lower": str(lo2), "certified_lower_float": float(lo2) ** 0.5,
           "prec": None if exact else prec, "conjecture1_proved": False}
    if lower is not None:
        L = Fraction(lower)
        out["claim"] = f"{mode}_nu |S_nu| >= {L}"
        out["certified"] = bool(lo2 >= L * L) if L > 0 else True
        if not out["certified"]:
            # report whether the claim is FALSE (an upper bound below L) or merely not certified
            hi_rows = [r for r in rows if r[2] < L * L]
            out["refuted"] = (mode == "min" and bool(hi_rows)) or (mode == "max" and len(hi_rows) == len(rows))
    return out


# ------------------------------------------------------------------------------------------------ Beurling
class BeurlingZeta:
    """Conditional Arb enclosure of a Beurling zeta_P(s) = int_{1-}^inf x^{-s} dN(x), for Re s > theta.

    Data: the generalized integers n <= X with multiplicity, given by their LOGS (arb-convertible), and a
    remainder hypothesis H(A, C, theta, X):  |N(x) - A x| <= C x^theta for all x >= X.
    For sigma = Re s > max(theta, 0), s != 1:
        zeta_P(s) = sum_{n <= X} n^{-s}  -  N(X) X^{-s}  +  A s X^{1-s} / (s - 1)  +  E(s),
        E(s) = s int_X^inf (N(x) - A x) x^{-s-1} dx,
        |E(s)|  <= |s| C X^{theta-sigma} / (sigma - theta),
        |E'(s)| <= C X^{theta-sigma} [ 1/(sigma-theta) + |s| ( log X/(sigma-theta) + 1/(sigma-theta)^2 ) ].
    (Integrate by parts on [1, X]; N(1-) = 0.)  N(X) counts n <= X; X must not be (within the balls) a
    generalized integer, else the constructor refuses.
    Use as a callable for telperion.arb_fakes.rigorous_winding / certify_zero_box: f(acb_series) -> acb_series
    (it supports ctx.cap 1 and 2, which is all those routines use).  Pole: s = 1, residue A -- declare it with
    poles=[(1, 0)] if a box's closure contains it (callables carry no declared pole, so YOU must keep boxes off
    s = 1 or the count is zeros minus poles silently).

    Trust: ARB conditional on H.  If H is only observed numerically up to some x_max, the result is COMPUTED-
    conditional; say so."""

    def __init__(self, logs_with_mult, A, C, theta, X):
        self.A, self.C, self.theta, self.X = _arb(A), _arb(C), _arb(theta), _arb(X)
        self.theta_f = Fraction(str(theta)) if not isinstance(theta, Fraction) else theta
        self.logX = self.X.log()
        terms, NX = [], 0
        for lg, m in logs_with_mult:
            lg = _arb(lg)
            if lg < self.logX:
                terms.append((lg, int(m)))
                NX += int(m)
            elif lg > self.logX:
                continue
            else:
                raise ValueError(f"BeurlingZeta: a generalized integer (log {lg}) is not separated from X; "
                                 "choose a different X")
        self.terms, self.NX = terms, NX
        self.hypothesis = {"A": str(A), "C": str(C), "theta": str(theta), "X": str(X),
                           "statement": f"|N(x) - {A} x| <= {C} x^{theta} for all x >= {X}"}

    def __call__(self, s):
        cap = ctx.cap
        c0 = s.coeffs()[0]
        sig_lo = Fraction(_frac(c0.real)[0])
        if not sig_lo > self.theta_f:
            raise ValueError(f"BeurlingZeta: Re s >= {float(sig_lo)} is not > theta = {float(self.theta_f)}")
        acc = acb_series([0])
        for lg, m in self.terms:
            acc = acc + m * (-s * acb(lg)).exp()
        X = acb(self.X)
        main = acc - self.NX * (-s * acb(self.logX)).exp() + self.A * s * ((1 - s) * acb(self.logX)).exp() / (s - 1)
        # error balls, evaluated at the worst point of the s-ball: sigma >= sig_lo, |s| <= |c0|_upper
        sig = _arb(sig_lo)
        d = sig - self.theta
        absS = abs(c0).mid() + abs(c0).rad()
        absS = arb(absS.mid() + absS.rad())
        decay = ((self.theta - sig) * self.logX).exp()
        e0 = absS * self.C * decay / d
        e1 = self.C * decay * (1 / d + absS * (self.logX / d + 1 / (d * d)))
        coeffs = list(main.coeffs()) + [acb(0)] * max(0, cap - len(main.coeffs()))
        r0 = arb(0, e0.mid() + e0.rad())
        coeffs[0] = coeffs[0] + acb(r0, r0)
        if cap >= 2:
            r1 = arb(0, e1.mid() + e1.rad())
            coeffs[1] = coeffs[1] + acb(r1, r1)
        if cap > 2:
            raise ValueError("BeurlingZeta supports jets of order <= 1 (ctx.cap <= 2)")
        return acb_series(coeffs[:cap])


def integers_from_primes(log_primes, X, limit=2_000_000):
    """All generalized integers n <= X generated by the primes with the given logs, returned as
    (arb log n, 1) pairs (equal products are kept as separate entries, which is right for N).  Enumeration is
    pruned in floats with a margin; the logs themselves are exact Arb sums of the prime logs, and BeurlingZeta
    re-decides n <= X in Arb (refusing ties)."""
    import math
    LP = sorted((_arb(x) for x in log_primes), key=lambda a: float(a.mid()))
    lp = [float(a.mid()) for a in LP]
    lX = math.log(float(X)) + 1e-6
    out = []

    def rec(i, cur_f, cur_a):
        out.append((cur_a, 1))
        if len(out) > limit:
            raise RuntimeError("too many generalized integers; lower X")
        for j in range(i, len(lp)):
            if cur_f + lp[j] > lX:
                break
            rec(j, cur_f + lp[j], cur_a + LP[j])

    rec(0, 0.0, arb(0))
    return out
