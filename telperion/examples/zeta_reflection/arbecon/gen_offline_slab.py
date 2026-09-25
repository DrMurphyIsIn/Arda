"""Generate a kernel-checked zero-free SLAB certificate (lane offline, lean/EMZetaOfflineSlabClear.lean).

usage: gen_offline_slab.py TAG --a A --b B [--cells 3] [--N 300] [--K 6] [--p 5]
  a, b: the slab heights as exact decimals or fractions ("1000", "1000+5773/100000").
Writes ../lean/EMZetaOfflineSlab_<TAG>.lean proving
  EdgeClearGlue.SlabClear a b
from J cells covering [1/2, 1] x [a, b] (reflection covers (0, 1/2)): per cell one run of the off-line
evaluator (p + 1 accumulators) at the dyadic center, one `decide +kernel` cell check
`ArbEcon.Off.checkCell ... = true`, and `ArbEcon.Off.cell_zeta_ne_zero`.  The scalar side conditions
(log bracket, r L <= 1, U, remainder certificate, error budget) are closed by `norm_num`.
The Python side mirrors `checkCell` exactly and refuses to emit a failing certificate.
conjecture1_proved = False.
"""
import json
import math
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import arbecon_model as M  # noqa: E402
import offline_model as O  # noqa: E402
import gen_offline as G  # noqa: E402


def w_data(BreN, BimN, BD, x1, x2):
    a1 = x1.reP - x1.reN
    b1 = x1.imP - x1.imN
    za = (x2.reP - x2.reN) - a1
    zb = (x2.imP - x2.imN) - b1
    zra = x2.reR + x1.reR
    zrb = x2.imR + x1.imR
    return (a1 * BD + za * BreN - zb * BimN, b1 * BD + za * BimN + zb * BreN,
            x1.reR * BD + zra * abs(BreN) + zrb * abs(BimN), x1.imR * BD + zra * abs(BimN) + zrb * abs(BreN))


def w_upper(d):
    return abs(d[0]) + d[2] + abs(d[1]) + d[3]


def sum_m(BreN, BimN, BD, rn, rd, p, k, ys1, ys2):
    s = 0
    for j, (x1, x2) in enumerate(zip(ys1, ys2)):
        kk = k + j
        s += w_upper(w_data(BreN, BimN, BD, x1, x2)) * rn ** kk * rd ** (p - kk) * (math.factorial(p) // math.factorial(kk))
    return s


def check_cell(c, o, K, N, p, xs1, xs2, rn, rd, FN, FD):
    x1, ys1 = xs1[0], xs1[1:]
    x2, ys2 = xs2[0], xs2[1:]
    BreN, BimN, BD = G.corr_data_g(K, o.a - o.b, o.q, 2 ** c.tq, c.tn, N)
    d0 = w_data(BreN, BimN, BD, x1, x2)
    T = rd ** p * math.factorial(p) * FD
    RHS = (d0[2] + d0[3]) * T + sum_m(BreN, BimN, BD, rn, rd, p, 1, ys1, ys2) * FD \
        + FN * 2 ** c.P * BD * rd ** p * math.factorial(p)
    LHS = (d0[0] ** 2 + d0[1] ** 2) * T ** 2
    ok = (1 <= K <= 6 and 2 <= N and 1 <= rd and 1 <= FD and 1 <= o.q and 1 <= c.tn
          and len(ys1) == p and len(ys2) == p and 0 <= RHS and RHS * RHS < LHS)
    scale = T * 2 ** c.P * BD
    margin = float(Fraction(math.isqrt(LHS), scale) - Fraction(RHS, scale)) if LHS > 0 else None
    return ok, margin


def frac_lean(x):
    x = Fraction(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)


def generate(tag, a, b, J=3, N=300, K=6, p=5, Lnum=Fraction(571, 100), FN=1, FD=50, U=1001, write=True):
    a, b = Fraction(a), Fraction(b)
    # dyadic center height
    tq = 14
    tmid = (a + b) / 2
    tn = round(tmid * 2 ** tq)
    tc = Fraction(tn, 2 ** tq)
    hh = max(tc - a, b - tc)
    w = Fraction(1, 4 * J)
    r2 = w * w + hh * hh
    rd = 10000
    rn = math.isqrt(int(r2 * rd * rd)) + 1
    while Fraction(rn, rd) ** 2 < r2:
        rn += 1
    r = Fraction(rn, rd)
    assert r * Lnum <= 1, "r L > 1"
    c = M.make_cfg(64, tn, tq, lnbig=256, sqbig=256)
    cells = []
    t0 = time.time()
    for j in range(J):
        sig = Fraction(1, 2) + (2 * j + 1) * w
        qa, qq = sig.numerator, sig.denominator
        o = O.make_ocfg(c, qa, 0, qq)
        s = O.init_state(c, p)
        fails = 0
        for _ in range(N - 2):
            if not O.ampl_ok(c, o, s.n + 1, s.g):
                fails += 1
            s = O.step(c, o, s)
        s1 = s
        if not O.ampl_ok(c, o, s1.n + 1, s1.g):
            fails += 1
        sN = O.step(c, o, s1)
        assert fails == 0 and s1.n == N - 1 and sN.n == N
        assert Fraction(sN.lhi, 2 ** c.P) <= Lnum, "log bracket above L"
        ok, margin = check_cell(c, o, K, N, p, s1.acc, sN.acc, rn, rd, FN, FD)
        assert ok, "cell %d check fails" % j
        # negative control: F = 10 must fail
        bad, _ = check_cell(c, o, K, N, p, s1.acc, sN.acc, rn, rd, 10, 1)
        assert not bad
        xl, xr = Fraction(1, 2) + 2 * j * w, Fraction(1, 2) + (2 * j + 2) * w
        cells.append(dict(j=j, sig=sig, o=o, s1=s1, sN=sN, xl=xl, xr=xr, margin=margin))
        # U check
        assert (sig + 2 * K - 1) ** 2 + tc ** 2 <= U ** 2
    pyt = time.time() - t0
    # remainder certificate: Qr^2 >= prod_{j <= 2K} ((1 + j)^2 + b^2), r0^2 <= N
    prod = Fraction(1)
    for jj in range(2 * K + 1):
        prod *= (1 + jj) ** 2 + b * b
    Qr = Fraction(math.isqrt(math.ceil(prod)) + 1)
    Qr = Fraction(math.ceil(Qr / 10 ** 34) * 10 ** 34)  # round up to a short literal
    assert Qr * Qr >= prod
    r0 = math.isqrt(N)
    # the budget (floats for the report; the Lean side proves it with norm_num)
    import mpmath as mp
    mp.mp.dps = 40
    Cp = mp.mpf(p + 2) / (mp.factorial(p + 1) * (p + 1))
    bern = [abs(mp.bernoulli(i + 2)) / mp.factorial(i + 2) for i in range(2 * K - 1)]
    aM = mp.mpf(a.numerator) / a.denominator
    emcB = mp.mpf(N) / aM + mp.mpf(1) / 2 + sum(bern[i] * mp.mpf(U) ** (i + 1) / mp.mpf(N) ** (i + 1)
                                                      for i in range(2 * K - 1))
    rr = mp.mpf(rn) / rd
    corrVar = mp.mpf(N) * rr / aM ** 2 + sum(
        bern[i] * ((U + rr) ** (i + 1) - mp.mpf(U) ** (i + 1)) / mp.mpf(N) ** (i + 1) for i in range(2 * K - 1))
    CK = 2 * (1 + (mp.pi ** 2 / 6 - 1) / 2 ** (2 * K - 1)) / (2 * mp.pi) ** (2 * K + 1)
    E = CK * mp.mpf(Qr.numerator) / (mp.mpf(N) ** (2 * K) * r0) / (2 * K + mp.mpf(1) / 2)
    T1 = Cp * (rr * mp.mpf(Lnum.numerator) / Lnum.denominator) ** (p + 1) * ((N - 1) + emcB)
    budget = T1 + 3 * corrVar + E
    assert budget < mp.mpf(FN) / FD
    info = dict(tag=tag, a=str(a), b=str(b), tc=str(tc), r=str(r), J=J, N=N, K=K, p=p,
                margins=[float(cl["margin"]) for cl in cells], budget=float(budget), T1=float(T1),
                corrVar=float(corrVar), E=float(E), emcB=float(emcB), F=FN / FD, py_s=round(pyt, 3))
    if not write:
        return info
    cfgt = "(ArbEcon.OrderK.cfg64 %d %d)" % (tn, tq)
    tcr = frac_lean(tc)
    ar, br = frac_lean(a), "(%s + %s)" % (frac_lean(math.floor(b)), frac_lean(b - math.floor(b))) if b.denominator != 1 else frac_lean(b)
    ns = "ArbEcon.Off.Slab_%s" % tag
    L = []
    L.append("/-  EMZetaOfflineSlab_%s.lean -- a KERNEL-CHECKED zero-free edge slab `SlabClear a b`, a = %s, b = %s" % (tag, a, b))
    L.append("    (GENERATED by arbecon/gen_offline_slab.py; do not edit).")
    L.append("")
    L.append("    %d cells cover [1/2, 1] x [a, b] (the reflection covers (0, 1/2)).  Cell j: center" % J)
    L.append("    sigma_j + i tc, tc = %d / 2^%d; radius r = %d/%d; per cell ONE off-line evaluator run" % (tn, tq, rn, rd))
    L.append("    (N = %d, %d accumulators, 2 `decide +kernel` chunks) and ONE `decide +kernel` cell check" % (N, p + 1))
    L.append("    (`ArbEcon.Off.checkCell`), assembled by `ArbEcon.Off.cell_zeta_ne_zero`.  Scalar side")
    L.append("    conditions (log bracket, r L <= 1, U, the order-%d remainder certificate, the error budget" % (2 * K + 1))
    L.append("    F = %d/%d) are closed by `norm_num`.  mpmath design margins: %s." % (FN, FD, ", ".join("%.3f" % m for m in info["margins"])))
    L.append("    conjecture1_proved = False.  A finite zero-free slab; nothing about RH.")
    L.append("-/")
    L.append("import EMZetaOfflineSlabClear")
    L.append("")
    L.append("open Complex ZetaReflection ZetaReflection.EMHigh")
    L.append("")
    L.append("namespace %s" % ns)
    L.append("")
    L.append("noncomputable section")
    L.append("")
    for cl in cells:
        j, o = cl["j"], cl["o"]
        L.append("def oc%d : ArbEcon.Off.OCfg := ⟨%d, %d, %d, %d, %d⟩" % (j, o.a, o.b, o.q, o.oneQ, o.nfuel))
        L.append("def s%d_1 : ArbEcon.Off.StO := %s" % (j, O.st_lean(cl["s1"])))
        L.append("def s%d_N : ArbEcon.Off.StO := %s" % (j, O.st_lean(cl["sN"])))
    L.append("")
    L.append("end")
    L.append("")
    for cl in cells:
        j = cl["j"]
        L.append("theorem chunk%d_1 : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d %d (ArbEcon.Off.StO.init %s %d)) s%d_1 = true := by" % (j, cfgt, j, N - 2, cfgt, p, j))
        L.append("  decide +kernel")
        L.append("theorem chunk%d_N : ArbEcon.Off.StO.beq (ArbEcon.Off.runO %s oc%d 1 s%d_1) s%d_N = true := by" % (j, cfgt, j, j, j))
        L.append("  decide +kernel")
        L.append("theorem check%d : ArbEcon.Off.checkCell %s oc%d %d %d %d s%d_1.acc s%d_N.acc %d %d %d %d = true := by" % (j, cfgt, j, K, N, p, j, j, rn, rd, FN, FD))
        L.append("  decide +kernel")
        L.append("/-- Negative control: an error budget F = 10 cannot be certified. -/")
        L.append("theorem check%d_neg : ArbEcon.Off.checkCell %s oc%d %d %d %d s%d_1.acc s%d_N.acc %d %d 10 1 = false := by" % (j, cfgt, j, K, N, p, j, j, rn, rd))
        L.append("  decide +kernel")
    L.append("")
    L.append("theorem ht : %s = ((%d : ℕ) : ℝ) / 2 ^ (%d : ℕ) := by norm_num" % (tcr, tn, tq))
    L.append("theorem valid : ArbEcon.Valid %s %s 9 := ArbEcon.OrderK.valid64 %d %d _ ht" % (cfgt, tcr, tn, tq))
    L.append("")
    # budget lemma (uniform)
    Qrl = "(%d : ℝ)" % Qr.numerator
    L.append("theorem abs_bern (i : ℕ) (hi : i ≤ 10) :")
    L.append("    |(bernoulli (i + 2) : ℝ)| / ((i + 2).factorial : ℝ) = |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) := by")
    L.append("  have hF : (0 : ℝ) < ((i + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _")
    L.append("  have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]")
    L.append("  rw [← abs_of_pos hF, ← abs_div, ArbEcon.OrderK.betaN_spec i hi, abs_div, abs_of_pos hL]")
    L.append("")
    L.append("theorem budget : ArbEcon.Off.Cp %d * (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) * %s) ^ (%d + 1)" % (p, rn, rd, frac_lean(Lnum), p))
    L.append("      * ((((%d : ℕ) : ℝ) - 1) + ArbEcon.Off.emcB %d %d %s %s)" % (N, K, N, ar, frac_lean(U)))
    L.append("    + 3 * ArbEcon.Off.corrVar %d %d (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ)) %s %s" % (K, N, rn, rd, ar, frac_lean(U)))
    L.append("    + ArbEcon.Off.CK %d * %s / ((((%d : ℕ) : ℝ)) ^ (2 * %d) * ((%d : ℕ) : ℝ)) / ((((2 * %d : ℕ)) : ℝ) + 1 / 2)" % (K, Qrl, N, K, r0, K))
    L.append("      ≤ ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ) := by" % (FN, FD))
    L.append("  have hCK := ArbEcon.Off.CK_le %d" % K)
    L.append("  have hsum1 : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.range (2 * %d - 1), |(bernoulli (i + 2) : ℝ)| / ((i + 2).factorial : ℝ) * f i" % K)
    L.append("      = ∑ i ∈ Finset.range (2 * %d - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) * f i := by" % K)
    L.append("    intro f; apply Finset.sum_congr rfl; intro i hi")
    L.append("    rw [abs_bern i (by have := Finset.mem_range.mp hi; omega)]")
    L.append("  have hemc : ArbEcon.Off.emcB %d %d %s %s = ((%d : ℕ) : ℝ) / %s + 1 / 2" % (K, N, ar, frac_lean(U), N, ar))
    L.append("      + ∑ i ∈ Finset.range (2 * %d - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ)" % K)
    L.append("          * (%s ^ (i + 1) / ((%d : ℕ) : ℝ) ^ (i + 1)) := by" % (frac_lean(U), N))
    L.append("    rw [ArbEcon.Off.emcB, ← hsum1]")
    L.append("    congr 1; apply Finset.sum_congr rfl; intro i _; ring")
    L.append("  have hcv : ArbEcon.Off.corrVar %d %d (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ)) %s %s" % (K, N, rn, rd, ar, frac_lean(U)))
    L.append("      = ((%d : ℕ) : ℝ) * (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ)) / %s ^ 2" % (N, rn, rd, ar))
    L.append("        + ∑ i ∈ Finset.range (2 * %d - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ)" % K)
    L.append("          * (((%s + ((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ)) ^ (i + 1) - %s ^ (i + 1)) / ((%d : ℕ) : ℝ) ^ (i + 1)) := by" % (frac_lean(U), rn, rd, frac_lean(U), N))
    L.append("    rw [ArbEcon.Off.corrVar, ← hsum1]")
    L.append("    congr 1; apply Finset.sum_congr rfl; intro i _; ring")
    L.append("  rw [hemc, hcv]")
    L.append("  have hC0 := ArbEcon.Off.CK_nonneg %d" % K)
    L.append("  have hmono : ArbEcon.Off.CK %d * %s / ((((%d : ℕ) : ℝ)) ^ (2 * %d) * ((%d : ℕ) : ℝ)) / ((((2 * %d : ℕ)) : ℝ) + 1 / 2)" % (K, Qrl, N, K, r0, K))
    L.append("      ≤ (2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * %d - 1))" % K)
    L.append("          / ((6283184 : ℝ) ^ (2 * %d + 1) / 1000000 ^ (2 * %d + 1))) * %s" % (K, K, Qrl))
    L.append("        / ((((%d : ℕ) : ℝ)) ^ (2 * %d) * ((%d : ℕ) : ℝ)) / ((((2 * %d : ℕ)) : ℝ) + 1 / 2) := by" % (N, K, r0, K))
    L.append("    gcongr")
    L.append("  refine le_trans (add_le_add (le_refl _) hmono) ?_")
    L.append("  unfold ArbEcon.Off.Cp")
    L.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ArbEcon.OrderK.betaN, ArbEcon.OrderK.Lbeta]")
    L.append("  norm_num [Nat.factorial]")
    L.append("")
    L.append("theorem hQ : pochNormSq 1 %s (2 * %d + 1) ≤ %s ^ 2 := by" % (br, K, Qrl))
    L.append("  simp only [pochNormSq]")
    L.append("  norm_num")
    L.append("")
    # cells
    for cl in cells:
        j, sig = cl["j"], cl["sig"]
        sigr = frac_lean(sig)
        L.append("theorem hσ%d : %s = (((%d : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) / ((%d : ℕ) : ℝ) := by norm_num" % (j, sigr, sig.numerator, sig.denominator))
        L.append("theorem ovalid%d : ArbEcon.Off.OValid %s oc%d %s := ⟨by decide +kernel, by decide, hσ%d⟩" % (j, cfgt, j, sigr, j))
        L.append("theorem inv%d_1 : ArbEcon.Off.InvO %s %s %s (%d - 1) s%d_1 :=" % (j, cfgt, sigr, tcr, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid ovalid%d %d 1 (ArbEcon.Off.StO.init %s %d) s%d_1" % (j, j, N - 2, cfgt, p, j))
        L.append("    (ArbEcon.Off.initO_sound _ _ _ %d valid.one_eq) chunk%d_1" % (p, j))
        L.append("theorem inv%d_N : ArbEcon.Off.InvO %s %s %s %d s%d_N :=" % (j, cfgt, sigr, tcr, N, j))
        L.append("  ArbEcon.Off.chunkO_sound _ oc%d _ _ 9 valid ovalid%d 1 %d s%d_1 s%d_N inv%d_1 chunk%d_N" % (j, j, N - 1, j, j, j, j))
        L.append("")
        L.append("/-- Cell %d: no zero with %s ≤ Re s ≤ %s (and Re s ≤ 1), %s ≤ Im s ≤ %s. -/" % (j, cl["xl"], cl["xr"], a, b))
        L.append("theorem cell%d : ∀ x y : ℝ, %s ≤ x → x ≤ %s → x ≤ 1 → %s ≤ y → y ≤ %s →" % (j, frac_lean(max(cl["xl"], Fraction(1, 2))), frac_lean(cl["xr"]), ar, br))
        L.append("    riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by")
        L.append("  intro x y hx0 hx1 hx1' hy0 hy1")
        L.append("  have hlhi : (s%d_N.lhi : ℝ) ≤ %s * 2 ^ (%s).P := by" % (j, frac_lean(Lnum), cfgt))
        L.append("    show ((%d : ℕ) : ℝ) ≤ %s * 2 ^ (64 : ℕ)" % (cl["sN"].lhi, frac_lean(Lnum)))
        L.append("    norm_num")
        L.append("  have hcell := ArbEcon.Off.cell_zeta_ne_zero %s oc%d %s %s hσ%d ht %d %d %d (by norm_num) (by norm_num)" % (cfgt, j, sigr, tcr, j, K, N, p))
        L.append("    s%d_1 s%d_N inv%d_1 inv%d_N %d %d %d %d check%d %s %s %s %s %s %d hlhi (by norm_num) (by norm_num) (by norm_num)" % (
            j, j, j, j, rn, rd, FN, FD, j, frac_lean(Lnum), ar, frac_lean(U), br, Qrl, r0))
        L.append("    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hQ (by norm_num) (by norm_num) budget")
        L.append("  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp")
        L.append("  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp")
        L.append("  apply hcell")
        L.append("  · apply ArbEcon.Off.dist_le_of_box x y %s %s %s %s (((%d : ℕ) : ℝ) / ((%d : ℕ) : ℝ))" % (sigr, tcr, frac_lean(w), frac_lean(hh), rn, rd))
        L.append("    · rw [abs_le]; constructor <;> linarith")
        L.append("    · rw [abs_le]; constructor <;> linarith")
        L.append("    · norm_num")
        L.append("    · norm_num")
        L.append("  · rw [him]; exact hy0")
        L.append("  · rw [him]; exact hy1")
        L.append("  · rw [hre]; linarith")
        L.append("  · rw [hre]; exact hx1'")
        L.append("")
    # region + slab
    L.append("/-- The right half of the slab. -/")
    L.append("theorem right_half : ∀ x y : ℝ, 1 / 2 ≤ x → x < 1 → %s ≤ y → y ≤ %s →" % (ar, br))
    L.append("    riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by")
    L.append("  intro x y hx0 hx1 hy0 hy1")
    for cl in cells[:-1]:
        L.append("  by_cases h%d : x ≤ %s" % (cl["j"], frac_lean(cl["xr"])))
        if cl["j"] == 0:
            L.append("  · exact cell0 x y (by linarith) h0 (by linarith) hy0 hy1")
        else:
            L.append("  · exact cell%d x y (by linarith) h%d (by linarith) hy0 hy1" % (cl["j"], cl["j"]))
    last = cells[-1]["j"]
    L.append("  exact cell%d x y (by linarith) (by linarith) (by linarith) hy0 hy1" % last)
    L.append("")
    L.append("/-- **The edge-clearance slab `SlabClear %s %s`, hypothesis-free.** -/" % (a, b))
    L.append("theorem slabClear : EdgeClearGlue.SlabClear %s %s :=" % (ar, br))
    L.append("  ArbEcon.Off.slabClear_of_right_half _ _ right_half")
    L.append("")
    L.append("end %s" % ns)
    L.append("")
    fname = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "EMZetaOfflineSlab_%s.lean" % tag)
    with open(fname, "w") as f:
        f.write("\n".join(L))
    info["file"] = fname
    return info


def main():
    argv = sys.argv[1:]
    opts, args, i = {}, [], 0
    while i < len(argv):
        if argv[i].startswith("--"):
            opts[argv[i][2:]] = argv[i + 1]
            i += 2
        else:
            args.append(argv[i])
            i += 1
    tag = args[0]

    def parse(sv):
        return sum(Fraction(x) for x in sv.split("+"))
    info = generate(tag, parse(opts["a"]), parse(opts["b"]), J=int(opts.get("cells", 3)),
                    N=int(opts.get("N", 300)), K=int(opts.get("K", 6)), p=int(opts.get("p", 5)))
    print(json.dumps(info, indent=1))


if __name__ == "__main__":
    main()
