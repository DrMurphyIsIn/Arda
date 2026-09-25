"""Bit-exact Python mirror of the OFF-LINE Nat-only zeta evaluator (lean/EMZetaOfflineEval.lean).

Every function mirrors a Lean definition operation by operation (floor division = Nat.div with
x/0 = 0, Nat.sub truncating at 0, >> = Nat.shiftRight), reusing the on-line model
`arbecon_model` for `logInc` and `trig` (unchanged in Lean).  A divergence makes a kernel
`decide` check fail, it never makes a wrong certificate.

sigma = (a - b) / q; s = sigma + i t, t = tn / 2^tq; accumulator k encloses
sum_{m <= n} (log m)^k m^(-s).

conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
"""
from dataclasses import dataclass
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arbecon_model as M  # noqa: E402

ndiv, nsub = M.ndiv, M.nsub


@dataclass(frozen=True)
class OCfg:
    a: int
    b: int
    q: int
    oneQ: int
    nfuel: int


def make_ocfg(c, a, b, q, nfuel=64):
    return OCfg(a, b, q, 2 ** (q * c.P), nfuel)


@dataclass(frozen=True)
class Acc:
    reP: int
    reN: int
    reR: int
    imP: int
    imN: int
    imR: int


ZERO = Acc(0, 0, 0, 0, 0, 0)


@dataclass(frozen=True)
class StO:
    n: int
    llo: int
    lhi: int
    g: int
    acc: tuple


@dataclass(frozen=True)
class TB:
    rs: bool
    rm: int
    rr: int
    is_: bool
    im: int
    ir: int


def root_loop(q, A, D, fuel, g):
    for _ in range(fuel):
        g2 = ndiv(nsub(q, 1) * g + ndiv(A, D * g ** nsub(q, 1)), q)
        if g <= g2:
            return g
        g = g2
    return g


def imC(P, hi, vm):
    return (hi * vm) >> P


def imR(P, lo, hi, vm, vr):
    return ((hi * vr) >> P) + ((nsub(hi, lo) * vm) >> P) + 3


def tb_mul(P, lo, hi, t):
    return TB(t.rs, imC(P, hi, t.rm), imR(P, lo, hi, t.rm, t.rr),
              t.is_, imC(P, hi, t.im), imR(P, lo, hi, t.im, t.ir))


def acc_add(x, t):
    reP, reN = (x.reP + t.rm, x.reN) if t.rs else (x.reP, x.reN + t.rm)
    imP, imN = (x.imP + t.im, x.imN) if t.is_ else (x.imP, x.imN + t.im)
    return Acc(reP, reN, x.reR + t.rr, imP, imN, x.imR + t.ir)


def add_chain(P, lo, hi, accs, t):
    out = []
    for x in accs:
        out.append(acc_add(x, t))
        t = tb_mul(P, lo, hi, t)
    return tuple(out)


def ampl(c, o, m, gprev):
    A = o.oneQ * m ** o.b
    D = m ** o.a
    g0 = gprev + ndiv(gprev, nsub(m, 1)) + 2
    g = root_loop(o.q, A, D, o.nfuel, g0)
    lo = g if g ** o.q * D <= A else 0
    hi = g + 1 if A <= (g + 1) ** o.q * D else c.one * m ** o.b
    return g, lo, hi


def term_tb(P, Xlo, Xhi, tr):
    (cm, cs, cr), (sm, ss, sr) = tr
    return TB(cs, imC(P, Xhi, cm), imR(P, Xlo, Xhi, cm, cr),
              not ss, imC(P, Xhi, sm), imR(P, Xlo, Xhi, sm, sr))


def step(c, o, s):
    m = s.n + 1
    S, K, pw = M.log_inc(c, m)
    llo = s.llo + S
    lhi = s.lhi + S + K + (ndiv(c.two1, pw) + 1)
    g, Xlo, Xhi = ampl(c, o, m, s.g)
    tr = M.trig(c, (c.tn * llo) >> c.tq, ((c.tn * lhi) >> c.tq) + 1)
    return StO(m, llo, lhi, g, add_chain(c.P, llo, lhi, s.acc, term_tb(c.P, Xlo, Xhi, tr)))


def run(c, o, s, count):
    for _ in range(count):
        s = step(c, o, s)
    return s


def init_state(c, p):
    return StO(1, 0, 0, c.one, (Acc(c.one, 0, 0, 0, 0, 0),) + (ZERO,) * p)


def ampl_ok(c, o, m, gprev):
    """True iff both root validations pass (no fallback) for term m."""
    A = o.oneQ * m ** o.b
    D = m ** o.a
    g, lo, hi = ampl(c, o, m, gprev)
    return (g ** o.q * D <= A) and (A <= (g + 1) ** o.q * D)


def acc_lean(x):
    return "⟨%d, %d, %d, %d, %d, %d⟩" % (x.reP, x.reN, x.reR, x.imP, x.imN, x.imR)


def st_lean(s):
    return "⟨%d, %d, %d, %d, [%s]⟩" % (s.n, s.llo, s.lhi, s.g, ", ".join(acc_lean(x) for x in s.acc))


def main():
    import mpmath
    mpmath.mp.dps = 40
    for (a, b, q, tn, tq, N, p) in [(3, 0, 10, 1000, 0, 400, 0), (6, 0, 5, 1000, 0, 400, 0),
                                    (0, 1, 1, 1999, 1, 400, 0), (1, 0, 2, 1000, 0, 300, 3)]:
        c = M.make_cfg(64, tn, tq, lnbig=256, sqbig=256)
        o = make_ocfg(c, a, b, q)
        s = init_state(c, p)
        fails = 0
        for _ in range(N - 1):
            if not ampl_ok(c, o, s.n + 1, s.g):
                fails += 1
            s = step(c, o, s)
        sig = mpmath.mpf(a - b) / q
        t = mpmath.mpf(tn) / 2 ** tq
        sv = sig + 1j * t
        one = c.one
        for k in range(p + 1):
            ex = mpmath.fsum(mpmath.log(n) ** k * mpmath.power(n, -sv) for n in range(1, N + 1))
            x = s.acc[k]
            re = mpmath.mpf(x.reP - x.reN) / one
            im = mpmath.mpf(x.imP - x.imN) / one
            print(f"sigma={float(sig)} t={float(t)} N={N} k={k} fails={fails}",
                  "re ok", abs(re - ex.real) <= mpmath.mpf(x.reR) / one, float(mpmath.mpf(x.reR) / one),
                  "im ok", abs(im - ex.imag) <= mpmath.mpf(x.imR) / one, float(mpmath.mpf(x.imR) / one))


if __name__ == "__main__":
    main()
