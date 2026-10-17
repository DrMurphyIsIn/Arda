"""Generate the kernel-checked zeta'-zero-free box of MM_speiser_box_probe (lean/SpeiserDerivBox.lean).

usage: gen_speiser_box.py [--check]

Target: deriv riemannZeta has no zero on [1/4, 3/8] x [6, 10] (NOT the Speiser wall: Speiser 1935
makes zeta' zero-free on the WHOLE open left strip equivalent to RH; one box decides nothing).

Cover: one column of 8 discs, centres 5/16 + i tc, tc = 25/4, 27/4, ..., 39/4, radius r = 13/50
(the box cells [1/4,3/8] x [tc-1/4, tc+1/4] have half-diagonal sqrt(17)/16 < 13/50).  Per disc: one
run of the off-line evaluator (N = 10 terms, p + 1 = 11 accumulators, the existing
`ArbEcon.Off.runO`) and ONE `decide +kernel` check `ArbEcon.Off.SpD.checkD`, whose soundness
`cell_deriv_ne_zero` (SpeiserDerivCore.lean) is: model polynomial M with exact Gaussian-rational
coefficients, sup_{|z-c| <= r + rho} |zeta(z) - M(z - c)| <= F rho, |M'(h)| > F on |h| <= r, Cauchy.

The Python side mirrors `checkD` exactly in Fractions and REFUSES to emit a failing certificate; it
also asserts the negative controls (a budget F = 1/10^9 must fail, and a corrupted accumulator
centre must fail) that the Lean file re-checks with `decide +kernel`.
conjecture1_proved = False.
"""
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arbecon_model as M  # noqa: E402
import offline_model as O  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "lean", "SpeiserDerivBox.lean")

# --------------------------------------------------------------------------- GQ mirror
Z = (Fr(0), Fr(0))


def add(a, b): return (a[0] + b[0], a[1] + b[1])
def neg(a): return (-a[0], -a[1])
def mul(a, b): return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
def nsq(a): return a[0] * a[0] + a[1] * a[1]
def inv(a): return (a[0] / nsq(a), -a[1] / nsq(a))
def l1(a): return abs(a[0]) + abs(a[1])
def ofQ(q): return (Fr(q), Fr(0))


def padd(P, Q):
    if not P:
        return list(Q)
    if not Q:
        return list(P)
    return [add(P[0], Q[0])] + padd(P[1:], Q[1:])


def pscale(a, Q): return [mul(a, b) for b in Q]


def pmul(P, Q):
    if not P:
        return []
    return padd(pscale(P[0], Q), [Z] + pmul(P[1:], Q))


def pderiv(P):
    if not P:
        return []
    return padd(P[1:], [Z] + pderiv(P[1:]))


def pnub(r, P):
    s = Fr(0)
    for a in reversed(P):
        s = l1(a) + r * s
    return s


def accQ(P, x): return (Fr(x.reP - x.reN, 2 ** P), Fr(x.imP - x.imN, 2 ** P))
def accRad(P, x): return Fr(x.reR + x.imR, 2 ** P)


def accSub(x2, x1):
    return O.Acc(x2.reP + x1.reN, x2.reN + x1.reP, x2.reR + x1.reR, x2.imP + x1.imN, x2.imN + x1.imP,
                 x2.imR + x1.imR)


def accsSub(xs2, xs1): return [accSub(a, b) for a, b in zip(xs2, xs1)]
def sf(k): return Fr((-1) ** k, math.factorial(k))
def qList(P, k, xs): return [mul(ofQ(sf(k + i)), accQ(P, x)) for i, x in enumerate(xs)]


def qErr(P, r, k, xs):
    s = Fr(0)
    for i in reversed(range(len(xs))):
        s = abs(sf(k + i)) * accRad(P, xs[i]) + r * s
    return s


def geoList(w, a, n):
    out = []
    for _ in range(n):
        out.append(a)
        a = mul(a, w)
    return out


def pochList(c, m):
    P = [(Fr(1), Fr(0))]
    for j in range(m):
        P = pmul(P, [add(c, ofQ(j)), (Fr(1), Fr(0))])
    return P


BETAN = {0: 108972864000, 2: -1816214400, 4: 43243200, 6: -1081080, 8: 27300, 10: -691}
LBETA = 1307674368000


def beta(i): return Fr(BETAN.get(i, 0), LBETA)


def corrPoly(c, N, n):
    P = [(Fr(1, 2), Fr(0))]
    for i in range(n):
        P = padd(P, pscale(ofQ(beta(i) / Fr(N) ** (i + 1)), pochList(c, i + 1)))
    return P


def gammaList(c, N, K, J):
    c1 = add(c, ofQ(-1))
    return padd(geoList(neg(inv(c1)), mul(ofQ(N), inv(c1)), J + 1), corrPoly(c, N, 2 * K - 1))


def cpQ(p): return Fr(p + 2, math.factorial(p + 1) * (p + 1))


def modelPoly(P, cQ, N, K, J, xs1, xs2):
    return padd(qList(P, 0, xs1), pmul(qList(P, 0, accsSub(xs2, xs1)), gammaList(cQ, N, K, J)))


def budgetQ(P, cQ, N, K, p, J, xs1, xs2, lhi, R, ER):
    Lq = Fr(lhi, 2 ** P)
    T = cpQ(p) * (R * Lq) ** (p + 1)
    GU = pnub(R, gammaList(cQ, N, K, J))
    return (ER + (N - 1) * T + T * GU + N * (R / cQ[1]) ** (J + 1) / (cQ[1] - R)
            + qErr(P, R, 0, xs1) + qErr(P, R, 0, accsSub(xs2, xs1)) * GU)


def derivTest(r, F, D):
    if not D:
        return False, None
    d0, Dt = D[0], D[1:]
    b = r * pnub(r, Dt) + F
    return (0 <= b and b * b < nsq(d0)), math.sqrt(float(nsq(d0))) - float(b)


def checkD(P, cQ, N, K, p, J, xs1, xs2, lhi, r, rho, F, ER):
    R = r + rho
    Lq = Fr(lhi, 2 ** P)
    ok = (1 <= K <= 6 and 2 <= N and len(xs1) == p + 1 and len(xs2) == p + 1 and 0 < rho and 0 <= r
          and R <= cQ[0] and cQ[0] + R <= 1 and R < cQ[1] and R * Lq <= 1 and 0 <= F and 0 <= ER)
    bud = budgetQ(P, cQ, N, K, p, J, xs1, xs2, lhi, R, ER)
    ok = ok and bud <= F * rho
    dt, margin = derivTest(r, F, pderiv(modelPoly(P, cQ, N, K, J, xs1, xs2)))
    return ok and dt, bud, margin


# --------------------------------------------------------------------------- parameters
N, K, p, J = 10, 3, 10, 7
SIG = Fr(5, 16)
R_ = Fr(13, 50)
RHO = Fr(1, 20)
F = Fr(1, 100)
TQ = 2
ROWS = [Fr(25 + 2 * i, 4) for i in range(8)]


def CK_upper(K):
    # the rational majorant of CK_le
    return (2 * (1 + (Fr(3141593) ** 2 / Fr(1000000) ** 2 / 6 - 1) / Fr(2) ** (2 * K - 1))
            / (Fr(6283184) ** (2 * K + 1) / Fr(1000000) ** (2 * K + 1)))


def remainder_cert(B):
    prod = Fr(1)
    for j in range(2 * K + 1):
        prod *= (1 + j) ** 2 + B * B
    Qr = Fr(math.isqrt(math.ceil(prod)) + 1)
    Qr = Fr(math.ceil(Qr / 10 ** 3) * 10 ** 3)
    assert Qr * Qr >= prod
    E = CK_upper(K) * Qr / Fr(N) ** (2 * K) / (2 * K)
    ER = Fr(math.ceil(E * 10 ** 9) + 1, 10 ** 9)
    assert ER >= E
    return Qr, ER


def frl(x):
    x = Fr(x)
    return "(%d : ℝ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℝ)" % (x.numerator, x.denominator)


def frq(x):
    x = Fr(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℚ)" % (x.numerator, x.denominator)


def build():
    cells = []
    Bmax = ROWS[-1] + R_ + RHO
    Qr, ER = remainder_cert(Bmax)
    for i, tc in enumerate(ROWS):
        tn = int(tc * 2 ** TQ)
        assert Fr(tn, 2 ** TQ) == tc
        c = M.make_cfg(64, tn, TQ, lnbig=256, sqbig=256)
        o = O.make_ocfg(c, SIG.numerator, 0, SIG.denominator)
        s = O.init_state(c, p)
        for _ in range(N - 2):
            assert O.ampl_ok(c, o, s.n + 1, s.g)
            s = O.step(c, o, s)
        s1 = s
        assert O.ampl_ok(c, o, s1.n + 1, s1.g)
        sN = O.step(c, o, s1)
        assert s1.n == N - 1 and sN.n == N
        cQ = (SIG, tc)
        ok, bud, margin = checkD(c.P, cQ, N, K, p, J, list(s1.acc), list(sN.acc), sN.lhi, R_, RHO, F, ER)
        assert ok, "cell %d fails (budget %s, margin %s)" % (i, float(bud), margin)
        bad, _, _ = checkD(c.P, cQ, N, K, p, J, list(s1.acc), list(sN.acc), sN.lhi, R_, RHO, Fr(1, 10 ** 9), ER)
        assert not bad, "negative control (F tiny) unexpectedly passes"
        cells.append(dict(i=i, tc=tc, tn=tn, o=o, s1=s1, sN=sN, budget=bud, margin=margin))
    # corrupted-centre control: shift the k = 1 accumulator of cell 0 by 2^60 / 2^64 = 1/16
    # corrupted-centre control: shift Re of the k = 1 accumulator after N terms of disc 0 by
    # M'(0) / gamma_0, which cancels M'(0) (a forged-data control the kernel must refuse)
    c0 = cells[0]
    cQ0 = (SIG, c0["tc"])
    d0 = pderiv(modelPoly(64, cQ0, N, K, J, list(c0["s1"].acc), list(c0["sN"].acc)))[0]
    g0 = gammaList(cQ0, N, K, J)[0]
    # mu_1 contains sf(1) * E_1 * gamma_0 = -E_1 gamma_0: shifting E_1 by d0 / gamma_0 cancels M'(0)
    dl = mul(d0, inv(g0))
    dre, dim = int(dl[0] * 2 ** 64), int(dl[1] * 2 ** 64)
    x = c0["sN"].acc[1]
    xbad = O.Acc(x.reP + max(dre, 0), x.reN + max(-dre, 0), x.reR, x.imP + max(dim, 0), x.imN + max(-dim, 0), x.imR)
    accbad = list(c0["sN"].acc)
    accbad[1] = xbad
    bad, _, _ = checkD(64, (SIG, c0["tc"]), N, K, p, J, list(c0["s1"].acc), accbad, c0["sN"].lhi, R_, RHO, F, ER)
    assert not bad, "corrupted-centre control unexpectedly passes"
    return cells, Qr, ER, Bmax, accbad


def emit(cells, Qr, ER, Bmax, accbad):
    L = []
    A = L.append
    A("/-  SpeiserDerivBox.lean -- MM_speiser_box_probe: `deriv riemannZeta` has NO zero on the closed box")
    A("    [1/4, 3/8] x [6, 10], KERNEL-CHECKED (GENERATED by arbecon/gen_speiser_box.py; do not edit).")
    A("")
    A("    8 discs, centres 5/16 + i tc (tc = 25/4, 27/4, ..., 39/4), radius r = 13/50, Cauchy radius")
    A("    rho = 1/20, budget F = 1/100.  Per disc: one off-line evaluator run (N = %d, %d accumulators," % (N, p + 1))
    A("    2 `decide +kernel` chunks) and ONE `decide +kernel` check `ArbEcon.Off.SpD.checkD`, assembled by")
    A("    `ArbEcon.Off.SpD.cell_deriv_ne_zero` (order-%d EM remainder, K = %d; Taylor order p = %d;" % (2 * K + 1, K, p))
    A("    geometric order J = %d).  Design margins |M'| - F - r ub: %s." % (J, ", ".join("%.3f" % cl["margin"] for cl in cells)))
    A("    Negative controls (`decide +kernel`, must be `false`): F = 1/10^9 on every disc; a corrupted")
    A("    accumulator centre on disc 0.")
    A("")
    A("    NOT the Speiser wall.  Speiser (1935): zeta' zero-free on the WHOLE open left strip")
    A("    0 < Re s < 1/2 is equivalent to RH; one box -- or any finite union -- decides nothing about RH.")
    A("    conjecture1_proved = False.")
    A("-/")
    A("import SpeiserDerivCore")
    A("")
    A("open Complex ZetaReflection ZetaReflection.EMHigh")
    A("")
    A("namespace ArbEcon.Off.SpeiserBox")
    A("")
    A("noncomputable section")
    A("")
    A("def oc : ArbEcon.Off.OCfg := ⟨%d, %d, %d, %d, %d⟩" % (cells[0]["o"].a, cells[0]["o"].b, cells[0]["o"].q, cells[0]["o"].oneQ, cells[0]["o"].nfuel))
    for cl in cells:
        i = cl["i"]
        A("def s%d_1 : ArbEcon.Off.StO := %s" % (i, O.st_lean(cl["s1"])))
        A("def s%d_N : ArbEcon.Off.StO := %s" % (i, O.st_lean(cl["sN"])))
    A("/-- Disc 0's accumulators after N terms with the k = 1 centre shifted by M'(0)/gamma_0, cancelling M'(0) (negative control). -/")
    A("def accBad0 : List ArbEcon.Off.Acc := [%s]" % ", ".join(O.acc_lean(x) for x in accbad))
    A("")
    A("end")
    A("")
    A("theorem hsig : (5 / 16 : ℝ) = (((5 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) / ((16 : ℕ) : ℝ) := by norm_num")
    A("")
    A("theorem hER : ArbEcon.Off.CK 3 * %s / ((10 : ℕ) : ℝ) ^ (2 * 3) / ((2 * 3 : ℕ) : ℝ) ≤ ((%s : ℚ) : ℝ) := by" % (frl(Qr), frq(ER)))
    A("  have hC0 := ArbEcon.Off.CK_nonneg 3")
    A("  have hmono : ArbEcon.Off.CK 3 * %s / ((10 : ℕ) : ℝ) ^ (2 * 3) / ((2 * 3 : ℕ) : ℝ)" % frl(Qr))
    A("      ≤ (2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * 3 - 1))")
    A("          / ((6283184 : ℝ) ^ (2 * 3 + 1) / 1000000 ^ (2 * 3 + 1))) * %s" % frl(Qr))
    A("        / ((10 : ℕ) : ℝ) ^ (2 * 3) / ((2 * 3 : ℕ) : ℝ) := by")
    A("    gcongr; exact ArbEcon.Off.CK_le 3")
    A("  refine le_trans hmono ?_")
    A("  norm_num")
    A("")
    cfg = lambda cl: "(ArbEcon.OrderK.cfg64 %d %d)" % (cl["tn"], TQ)
    for cl in cells:
        i, tc = cl["i"], cl["tc"]
        cf = cfg(cl)
        B = tc + R_ + RHO
        A("/-! ### Disc %d: centre 5/16 + i %s -/" % (i, tc))
        A("theorem chunk%d_1 : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc %d (ArbEcon.Off.StO.init %s %d)) s%d_1 = true := by" % (i, cf, N - 2, cf, p, i))
        A("  decide +kernel")
        A("theorem chunk%d_N : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc 1 s%d_1) s%d_N = true := by" % (i, cf, i, i))
        A("  decide +kernel")
        A("theorem check%d : ArbEcon.Off.SpD.checkD %s.P ⟨%s, %s⟩ %d %d %d %d s%d_1.acc s%d_N.acc s%d_N.lhi %s %s %s %s = true := by"
          % (i, cf, frq(SIG), frq(tc), N, K, p, J, i, i, i, frq(R_), frq(RHO), frq(F), frq(ER)))
        A("  decide +kernel")
        A("/-- Negative control: the budget F = 1/10^9 cannot be certified. -/")
        A("theorem check%d_neg : ArbEcon.Off.SpD.checkD %s.P ⟨%s, %s⟩ %d %d %d %d s%d_1.acc s%d_N.acc s%d_N.lhi %s %s (1 / 1000000000 : ℚ) %s = false := by"
          % (i, cf, frq(SIG), frq(tc), N, K, p, J, i, i, i, frq(R_), frq(RHO), frq(ER)))
        A("  decide +kernel")
        A("theorem ht%d : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (i, frl(tc), cl["tn"], TQ))
        A("theorem valid%d : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht%d" % (i, cf, frl(tc), cl["tn"], TQ, i))
        A("theorem ovalid%d : ArbEcon.Off.OValid %s oc (5 / 16 : ℝ) := ⟨by decide +kernel, by decide, hsig⟩" % (i, cf))
        A("theorem inv%d_1 : ArbEcon.Off.InvO %s (5 / 16 : ℝ) %s (%d - 1) s%d_1 :=" % (i, cf, frl(tc), N, i))
        A("  ArbEcon.Off.chunkO_sound _ oc _ _ 9 valid%d ovalid%d %d 1 (ArbEcon.Off.StO.init %s %d) s%d_1" % (i, i, N - 2, cf, p, i))
        A("    (ArbEcon.Off.initO_sound _ _ _ %d valid%d.one_eq) chunk%d_1" % (p, i, i))
        A("theorem inv%d_N : ArbEcon.Off.InvO %s (5 / 16 : ℝ) %s %d s%d_N :=" % (i, cf, frl(tc), N, i))
        A("  ArbEcon.Off.chunkO_sound _ oc _ _ 9 valid%d ovalid%d 1 %d s%d_1 s%d_N inv%d_1 chunk%d_N" % (i, i, N - 1, i, i, i, i))
        A("theorem hQ%d : pochNormSq 1 (((%s : ℚ) : ℝ) + (((%s : ℚ) : ℝ) + ((%s : ℚ) : ℝ))) (2 * %d + 1) ≤ %s ^ 2 := by"
          % (i, frq(tc), frq(R_), frq(RHO), K, frl(Qr)))
        A("  simp only [pochNormSq]")
        A("  norm_num")
        A("/-- Disc %d: `ζ'(s) ≠ 0` for `‖s - (5/16 + i %s)‖ ≤ 13/50`. -/" % (i, tc))
        A("theorem disc%d : ∀ s : ℂ, ‖s - ArbEcon.Off.sOfG (5 / 16 : ℝ) %s‖ ≤ ((%s : ℚ) : ℝ) → deriv riemannZeta s ≠ 0 :=" % (i, frl(tc), frq(R_)))
        A("  ArbEcon.Off.SpD.cell_deriv_ne_zero %s (5 / 16 : ℝ) %s ⟨%s, %s⟩ (by norm_num) (by norm_num) %d %d %d %d" % (cf, frl(tc), frq(SIG), frq(tc), K, N, p, J))
        A("    s%d_1 s%d_N inv%d_1 inv%d_N %s %s %s %s check%d %s (by norm_num) hQ%d hER" % (i, i, i, i, frq(R_), frq(RHO), frq(F), frq(ER), i, frl(Qr), i))
        A("")
    c0 = cells[0]
    A("/-- Negative control: a corrupted accumulator centre (k = 1, after N terms, disc 0) is refused. -/")
    A("theorem check0_corrupt : ArbEcon.Off.SpD.checkD %s.P ⟨%s, %s⟩ %d %d %d %d s0_1.acc accBad0 s0_N.lhi %s %s %s %s = false := by"
      % (cfg(c0), frq(SIG), frq(c0["tc"]), N, K, p, J, frq(R_), frq(RHO), frq(F), frq(ER)))
    A("  decide +kernel")
    A("")
    # the box
    A("/-- A box point lies in the disc of its row. -/")
    A("theorem dist_le_of_row (s : ℂ) (tc : ℝ) (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 3 / 8)")
    A("    (h3 : tc - 1 / 4 ≤ s.im) (h4 : s.im ≤ tc + 1 / 4) :")
    A("    ‖s - ArbEcon.Off.sOfG (5 / 16 : ℝ) tc‖ ≤ ((13 / 50 : ℚ) : ℝ) := by")
    A("  have hre : (s - ArbEcon.Off.sOfG (5 / 16 : ℝ) tc).re = s.re - 5 / 16 := by simp [ArbEcon.Off.sOfG]")
    A("  have him : (s - ArbEcon.Off.sOfG (5 / 16 : ℝ) tc).im = s.im - tc := by simp [ArbEcon.Off.sOfG]")
    A("  have hsq : ‖s - ArbEcon.Off.sOfG (5 / 16 : ℝ) tc‖ ^ 2 ≤ ((13 / 50 : ℚ) : ℝ) ^ 2 := by")
    A("    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]")
    A("    push_cast")
    A("    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h4)]")
    A("  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hsq")
    A("")
    A("end ArbEcon.Off.SpeiserBox")
    A("")
    A("open ArbEcon.Off.SpeiserBox in")
    A("/-- **MM_speiser_box_probe, hypothesis-free.**  `deriv riemannZeta` has no zero in the closed box")
    A("    `[1/4, 3/8] x [6, 10]`, strictly left of the critical line.  NOT the Speiser wall; not a step")
    A("    toward RH.  conjecture1_proved = False. -/")
    A("theorem speiser_box_probe :")
    A("    ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 8 → 6 ≤ s.im → s.im ≤ 10 →")
    A("      deriv riemannZeta s ≠ 0 := by")
    A("  intro s h1 h2 h3 h4")
    for cl in cells[:-1]:
        i, tc = cl["i"], cl["tc"]
        A("  by_cases g%d : s.im ≤ %s" % (i, frl(tc + Fr(1, 4))))
        A("  · exact disc%d s (dist_le_of_row s %s h1 h2 (by linarith) (by linarith))" % (i, frl(tc)))
        A("  rw [not_le] at g%d" % i)
    last = cells[-1]
    A("  exact disc%d s (dist_le_of_row s %s h1 h2 (by linarith) (by linarith))" % (last["i"], frl(last["tc"])))
    A("")
    return "\n".join(L) + "\n"


def main():
    cells, Qr, ER, Bmax, accbad = build()
    for cl in cells:
        print("disc %d tc=%s budget=%.3e margin=%.4f" % (cl["i"], cl["tc"], float(cl["budget"]), cl["margin"]))
    print("Qr=%s ER=%s (%.3e)" % (Qr, ER, float(ER)))
    text = emit(cells, Qr, ER, Bmax, accbad)
    if "--check" in sys.argv:
        cur = open(OUT).read() if os.path.exists(OUT) else ""
        if cur != text:
            print("DRIFT: %s differs from the generator output" % OUT)
            return 1
        print("no drift")
        return 0
    with open(OUT, "w") as f:
        f.write(text)
    print("wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
