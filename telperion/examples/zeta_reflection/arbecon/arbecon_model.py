"""Bit-exact Python reference model of the ArbEconomics Nat-only zeta evaluator (v2).

Every function here mirrors a Lean definition in Probes/ArbEconomics_Eval.lean operation by
operation (floor division = Nat.div with x/0 = 0, >> = Nat.shiftRight, & = Nat.land), so the
Lean kernel `decide` checks can be generated from it; any divergence makes a kernel check fail.

Semantics (P = precision bits, ONE = 2**P):
  * nonneg interval [lo, hi] (Nats) encloses x iff lo <= x*ONE <= hi
  * signed ball (pos, neg, rad) encloses x iff |x*ONE - (pos - neg)| <= rad

conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
"""
from dataclasses import dataclass
from fractions import Fraction
import math


def ndiv(a, b):
    return a // b if b else 0


def nsub(a, b):
    return a - b if a > b else 0


@dataclass(frozen=True)
class Cfg:
    P: int
    one: int
    two1: int
    oneSq: int
    tn: int
    tq: int
    hp: int
    hph: int
    rp: int
    umax: int
    tau: int
    dcos: tuple
    dsin: tuple
    lnfuel: int
    lnbig: int
    lnK: int
    sqfuel: int
    sqbig: int


def pi_half_ball(P):
    """(hp, rp) with |pi/2 * 2^P - hp| <= rp, justified by Mathlib pi_gt_d20 / pi_lt_d20."""
    lo = Fraction(314159265358979323846, 10**20) / 2
    hi = Fraction(314159265358979323847, 10**20) / 2
    one = 2 ** P
    hp = math.floor((lo + hi) / 2 * one)
    rp = math.ceil(max(hi * one - hp, hp - lo * one)) + 1
    return hp, rp


def taylor_tau(P, umax_num, umax_den, K):
    """ulps bound for the Complex.exp_bound remainder with n = 2K+2 at u <= umax."""
    n = 2 * K + 2
    u = Fraction(umax_num, umax_den)
    bound = u ** n * Fraction(n + 1, math.factorial(n) * n)
    return math.ceil(bound * 2 ** P)


def make_cfg(P, tn, tq, K=None, lnbig=None, sqbig=None):
    one = 2 ** P
    hp, rp = pi_half_ball(P)
    if K is None:
        K = 1
        while taylor_tau(P, 13, 16, K) > 1:
            K += 1
    umax = one * 13 // 16
    tau = taylor_tau(P, 13, 16, K)
    dcos = tuple(one * (2 * k - 1) * (2 * k) for k in range(K, 0, -1))
    dsin = tuple(one * (2 * k) * (2 * k + 1) for k in range(K, 0, -1))
    if lnbig is None:
        lnbig = 2 ** 13 if P <= 64 else 2 ** 16
    lnK = 1
    while one // (lnbig ** (lnK + 1) * (lnK + 1)) > 0:
        lnK += 1
    if sqbig is None:
        sqbig = 2 ** 14
    return Cfg(P, one, 2 * one, one * one, tn, tq, hp, hp // 2, rp, umax, tau, dcos, dsin,
               P + 1, lnbig, lnK, 12, sqbig)


# ---------------------------------------------------------------- generic specs

def log_loop(one, m, fuel):
    i, pw, S = 0, m, 0
    for _ in range(fuel):
        f = ndiv(one, pw * (i + 1))
        if f == 0:
            return S, i, pw
        S, i, pw = S + f, i + 1, pw * m
    return S, i, pw


def log_fix(one, m, K):
    i, pw, S = 0, m, 0
    for _ in range(K):
        S, i, pw = S + ndiv(one, pw * (i + 1)), i + 1, pw * m
    return S, i, pw


def isqrt_loop(A, g, fuel):
    for _ in range(fuel):
        g2 = (g + ndiv(A, g)) >> 1
        if g <= g2:
            return g
        g = g2
    return g


def horner(one, w, divs):
    h = one
    for D in divs:
        h = nsub(one, ndiv(w * h, D))
    return h


# ---------------------------------------------------------------- evaluator

@dataclass
class St:
    n: int
    llo: int
    lhi: int
    g: int
    reP: int
    reN: int
    reR: int
    imP: int
    imN: int
    imR: int


def init_state(c: Cfg):
    return St(1, 0, 0, c.one, c.one, 0, 0, 0, 0, 0)


def log_inc(c, m):
    if c.lnbig <= m:
        return log_fix(c.one, m, c.lnK)
    return log_loop(c.one, m, c.lnfuel)


def isqrt(c, m, A, g):
    if c.sqbig <= m:
        g1 = (g + ndiv(A, g)) >> 1
        return (g1 + ndiv(A, g1)) >> 1
    return isqrt_loop(A, g, c.sqfuel)


def rotate(b0, b1, C, rc, S0, sy, rs):
    if not b1:
        if not b0:
            return (C, True, rc), (S0, sy, rs)
        return (S0, not sy, rs), (C, True, rc)
    if not b0:
        return (C, False, rc), (S0, not sy, rs)
    return (S0, sy, rs), (C, False, rc)


def trig(c: Cfg, thlo, thhi):
    k = ndiv(thlo + c.hph, c.hp)
    M1 = thlo + thhi
    M2 = (k * c.hp) << 1
    pos = M2 <= M1
    mag = (nsub(M1, M2) if pos else nsub(M2, M1)) >> 1
    rphi = (nsub(thhi, thlo) >> 1) + k * c.rp + 2
    j = k % 4
    b0 = (j % 2) == 1
    b1 = 2 <= j
    if mag <= c.umax:
        w = (mag * mag) >> c.P
        C = horner(c.one, w, c.dcos)
        S0 = (mag * horner(c.one, w, c.dsin)) >> c.P
        return rotate(b0, b1, C, 3 + c.tau + rphi, S0, pos, 4 + c.tau + rphi)
    return rotate(b0, b1, 0, c.one, 0, pos, c.one)


def term_of(c: Cfg, s: St):
    m = s.n + 1
    S, K, pw = log_inc(c, m)
    llo = s.llo + S
    lhi = s.lhi + S + K + (ndiv(c.two1, pw) + 1)
    g = isqrt(c, m, ndiv(c.oneSq, m), s.g)
    q = ndiv(c.oneSq, m * g)
    b = g * g * m <= c.oneSq
    if 1 <= g:
        Rlo, Rhi = (g, q + 1) if b else (q, g)
    else:
        Rlo, Rhi = 0, c.one
    thlo = (c.tn * llo) >> c.tq
    thhi = ((c.tn * lhi) >> c.tq) + 1
    return llo, lhi, g, Rlo, Rhi, trig(c, thlo, thhi)


def tmul(c, Rlo, Rhi, vm, vr):
    return (Rhi * vm) >> c.P, ((Rhi * vr) >> c.P) + nsub(Rhi, Rlo) + 2


def step(c: Cfg, s: St) -> St:
    llo, lhi, g, Rlo, Rhi, ((cm, cs, cr), (sm, ss, sr)) = term_of(c, s)
    tre, rre = tmul(c, Rlo, Rhi, cm, cr)
    tim, rim = tmul(c, Rlo, Rhi, sm, sr)
    reP, reN = (s.reP + tre, s.reN) if cs else (s.reP, s.reN + tre)
    imP, imN = (s.imP, s.imN + tim) if ss else (s.imP + tim, s.imN)
    return St(s.n + 1, llo, lhi, g, reP, reN, s.reR + rre, imP, imN, s.imR + rim)


def run(c: Cfg, s: St, count):
    for _ in range(count):
        s = step(c, s)
    return s


# ---------------------------------------------------------------- Lean emission helpers

def lean_horner(one, divs, name):
    expr = str(one)
    for D in divs:
        expr = "Nat.sub %d (Nat.div (Nat.mul w (%s)) %d)" % (one, expr, D)
    return "def %s (w : Nat) : Nat :=\n  %s" % (name, expr)


def lean_lnf(c, name):
    K = c.lnK
    lines = ["def %s (m : Nat) : Nat × Nat × Nat :=" % name]
    lines.append("  let p1 := m")
    for i in range(2, K + 2):
        lines.append("  let p%d := Nat.mul p%d m" % (i, i - 1))
    S = "0"
    for i in range(K):
        S = "Nat.add (%s) (Nat.div %d (Nat.mul p%d %d))" % (S, c.one, i + 1, i + 1)
    lines.append("  (%s, %d, p%d)" % (S, K, K + 1))
    return "\n".join(lines)


def cfg_lean(c, hc, hs, lnf):
    return ("⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, [%s], [%s], %s, %s, %d, %d, %d, %s, %d, %d⟩" %
            (c.P, c.one, c.two1, c.oneSq, c.tn, c.tq, c.hp, c.hph, c.rp, c.umax, c.tau,
             ", ".join(map(str, c.dcos)), ", ".join(map(str, c.dsin)), hc, hs,
             c.lnfuel, c.lnbig, c.lnK, lnf, c.sqfuel, c.sqbig))


def st_lean(s):
    return "⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d⟩" % (
        s.n, s.llo, s.lhi, s.g, s.reP, s.reN, s.reR, s.imP, s.imN, s.imR)


# ---------------------------------------------------------------- numerics checks

def main():
    import mpmath
    import time
    mpmath.mp.dps = 40
    for (t, N) in [(14, 50), (100, 504), (1000, 3200), (1000, 20000)]:
        c = make_cfg(64, t, 0)
        t0 = time.time()
        s = run(c, init_state(c), N - 2)
        el = time.time() - t0
        assert s.n == N - 1
        one = c.one
        re = mpmath.mpf(s.reP - s.reN) / one
        im = mpmath.mpf(s.imP - s.imN) / one
        rr = mpmath.mpf(s.reR) / one
        ri = mpmath.mpf(s.imR) / one
        sv = mpmath.mpf(1) / 2 + 1j * t
        exact = mpmath.fsum(mpmath.power(n, -sv) for n in range(1, N))
        print(f"t={t} N={N} K={len(c.dcos)} lnK={c.lnK} tau={c.tau} py={el:.2f}s")
        print("   re err", float(re - exact.real), "rad", float(rr), "ok", abs(re - exact.real) <= rr)
        print("   im err", float(im - exact.imag), "rad", float(ri), "ok", abs(im - exact.imag) <= ri)


if __name__ == "__main__":
    main()
