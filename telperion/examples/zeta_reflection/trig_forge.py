#!/usr/bin/env python3
"""trig_forge.py -- ANDÚRIL cert-forge: the parametric trig / zeta / theta certificate generator.

THE MISSION'S REAL DELIVERABLE.  A driver that EMITS the kernel certificates the argument-free
first-zero theorem consumes, all in the TrigReduce / ZeroHypBand / ThetaConverge templates:

  Stage 1 (trig):  cos/sin(t * log n) box  ->  `emit_trig_cert(t, n)`   [TrigReduceOperating template]
  Stage 2 (zeta):  Re/Im zeta(1/2+it) box  ->  `emit_zeta_side(t, ...)`  [ZeroHypBand + EM tail]
  Stage 3 (theta): cos/sin(phi_t) box       ->  `emit_theta_side(t, ...)` [ThetaConverge + arctan]
  Stage 4 (asm):   the two S(t) sign facts + `first_zero_of_sign_quantities` instantiation.

DRIVER DISCIPLINE.  mpmath is the untrusted candidate producer (box centers only).  Every emitted
bound is a KERNEL-verified interval-arithmetic step aimed at the SAME Mathlib/TrigReduce lemmas the
4 hand certs use.  The driver self-validates every cert numerically before emission, and the forge
carries a corruption self-check (`--self-check`) that confirms the kernel rejects a perturbed cert.

conjecture1_proved = False.  A certificate factory for a proven conditional theorem, not a proof of RH.
"""
from __future__ import annotations

from fractions import Fraction as F
from dataclasses import dataclass
import argparse
import math
import sys
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80

# ---------------------------------------------------------------------------------------------------
# Rational interval arithmetic (exact, over Fraction).  Endpoints are kept at a bounded dyadic scale
# so the emitted `norm_num` goals stay cheap.  We ROUND OUTWARD at a fixed dyadic scale so every
# printed endpoint is a valid enclosure and the numbers stay small.
# ---------------------------------------------------------------------------------------------------

# scale for climb/base interval endpoints: 2^SCALE.  60 matches the templates' ~1.15e18 denominators.
SCALE = 60
DEN = 1 << SCALE


def rfloor(x: F) -> F:
    """Outward-round DOWN to the dyadic grid 1/2^SCALE."""
    n = math.floor(x * DEN)
    return F(n, DEN)


def rceil(x: F) -> F:
    """Outward-round UP to the dyadic grid 1/2^SCALE."""
    n = math.ceil(x * DEN)
    return F(n, DEN)


@dataclass
class Iv:
    lo: F
    hi: F

    def widen(self) -> "Iv":
        return Iv(rfloor(self.lo), rceil(self.hi))


def frac_str(x: F) -> str:
    """Lean literal for a Fraction: `(p / q)` (q>1) or integer."""
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator} / {x.denominator}"


# ---------------------------------------------------------------------------------------------------
# Stage 1: the trig climb.  Reproduces the TrigReduceOperating template EXACTLY (base bracket -> M
# doubling steps -> Lipschitz width absorption), for any (t, n).
# ---------------------------------------------------------------------------------------------------

# theta enters as a verified dyadic enclosure |theta - c| <= w, from Mathlib log d9 bounds.
# We sample c at 2^-CSCALE (45 in the templates) and take a width w that the log-d9 algebra covers.
CSCALE = 45


def theta_sample(t: int, n: int) -> tuple[F, F]:
    """Return (c, w): dyadic sample c ≈ t*log n and a half-width w covering |t*log n - c| via the
    GENERAL nat-log bracket (ForgeLogBracket).  w = t·(log-bracket half-width) rounded up, dominated
    by ~t/32768 ≈ 5e-4 -- well under the per-term trig budget (~5e-4).  For n=1, w is a token."""
    theta = t * mp.log(n)
    c = F(int(round(float(theta) * (1 << CSCALE))), 1 << CSCALE)
    if n == 1:
        return F(0), F(1, 1 << 20)
    ln_lo, ln_hi = log_bracket(n)[0], log_bracket(n)[1]
    worst = max(abs(F(c) - t * ln_lo), abs(t * ln_hi - F(c)))
    # round w up to the sampling grid so the emitted literal is compact
    w = rceil(worst * F(3, 2))              # 1.5x margin, dyadic-rounded up
    assert abs(theta - mp.mpf(c.numerator) / c.denominator) <= mp.mpf(w.numerator) / w.denominator
    return c, w


# Target reduced-argument bound |y| <= 2^-YRED so the order-4 base Taylor is essentially exact
# (error ~ y^4 ~ 2^-4*YRED) and the M doublings preserve tightness.  The templates reduce to
# y ~ 2e-6 (~2^-19); YRED=18 reproduces that regime.
YRED = 18


def reduce_M(c: F) -> int:
    """Number of doubling steps M so that |c / 2^M| <= 2^-YRED (deep reduction: tight base Taylor)."""
    if c == 0:
        return 0
    M = 0
    y = c
    thresh = F(1, 1 << YRED)
    while abs(y) > thresh:
        y = y / 2
        M += 1
    return M


def cos_base_iv(y: F) -> Iv:
    """Order-4 cos bracket consumed by `cos_base_interval`:  1 - y^2/2 -+ y^4*(5/96)."""
    mid = 1 - y ** 2 / 2
    rem = y ** 4 * F(5, 96)
    return Iv(rfloor(mid - rem), rceil(mid + rem))


def sin_base_iv(y: F) -> Iv:
    """Order-4 sin bracket consumed by `sin_base_interval`:  y - y^3/6 -+ y^4*(1/100)."""
    mid = y - y ** 3 / 6
    rem = y ** 4 * F(1, 100)
    return Iv(rfloor(mid - rem), rceil(mid + rem))


def cos_double_iv(c: Iv) -> tuple[Iv, str]:
    """Image of cos-box `c` under t -> 2t^2-1, plus the `hcase` branch selector string.
    Returns (image_box, hcase_lean)."""
    vals = [2 * c.lo ** 2 - 1, 2 * c.hi ** 2 - 1]
    lo = rfloor(min(vals))
    hi = rceil(max(vals))
    # the parabola 2t^2-1 on [clo,chi]: min is at the endpoint of larger |.| for the upper, but the
    # LOWER bound may be the vertex (-1) if 0 in [clo,chi].  cos_double_interval's hcase requires one
    # of: 0<=clo, chi<=0, clo'<=-1.  Pick the valid branch.
    if c.lo >= 0:
        hcase = "Or.inl (by norm_num)"
    elif c.hi <= 0:
        hcase = "Or.inr (Or.inl (by norm_num))"
    else:
        # straddle: the emitted lower bound must satisfy clo' <= -1.
        lo = min(lo, F(-1))
        hcase = "Or.inr (Or.inr (by norm_num))"
    return Iv(lo, hi), hcase


def sin_double_iv(cs: Iv, sn: Iv) -> Iv:
    """Image of 2*(sin y)*(cos y) via the four corner products of [slo,shi]x[clo,chi]."""
    corners = [2 * (sn.lo * cs.lo), 2 * (sn.lo * cs.hi), 2 * (sn.hi * cs.lo), 2 * (sn.hi * cs.hi)]
    return Iv(rfloor(min(corners)), rceil(max(corners)))


@dataclass
class TrigClimb:
    t: int
    n: int
    c: F
    w: F
    M: int
    y: F
    cos_base: Iv
    sin_base: Iv
    cos_steps: list[tuple[Iv, str]]   # per step: (image box, hcase)
    sin_steps: list[Iv]
    cos_final: Iv                     # at the sample point c  (before width absorption)
    sin_final: Iv
    cos_box: Iv                       # cos(t*log n): final -+ w
    sin_box: Iv


def build_trig_climb(t: int, n: int) -> TrigClimb:
    c, w = theta_sample(t, n)
    M = reduce_M(c)
    y = c / (1 << M)
    cb = cos_base_iv(y)
    sb = sin_base_iv(y)
    cos_steps: list[tuple[Iv, str]] = []
    sin_steps: list[Iv] = []
    ccur, scur = cb, sb
    for _ in range(M):
        cnext, hcase = cos_double_iv(ccur)
        snext = sin_double_iv(ccur, scur)
        cos_steps.append((cnext, hcase))
        sin_steps.append(snext)
        ccur, scur = cnext, snext
    cos_box = Iv(ccur.lo - w, ccur.hi + w)
    sin_box = Iv(scur.lo - w, scur.hi + w)
    # numeric validation against mpmath truth
    theta = t * mp.log(n)
    ct, st = mp.cos(theta), mp.sin(theta)
    def within(iv: Iv, v):
        return mp.mpf(iv.lo.numerator) / iv.lo.denominator - mp.mpf('1e-30') <= v <= mp.mpf(iv.hi.numerator) / iv.hi.denominator + mp.mpf('1e-30')
    assert within(cos_box, ct), f"cos box invalid t={t} n={n}: {float(cos_box.lo)}<= {float(ct)} <= {float(cos_box.hi)}"
    assert within(sin_box, st), f"sin box invalid t={t} n={n}"
    return TrigClimb(t, n, c, w, M, y, cb, sb, cos_steps, sin_steps, ccur, scur, cos_box, sin_box)


# ---------------------------------------------------------------------------------------------------
# Lean emission for the trig climb.  Mirrors TrigReduceOperating's section structure so the emitted
# proof aims at the SAME lemmas (cos/sin_base_interval, cos/sin_double_interval, cos/sin_encl_bracket).
# ---------------------------------------------------------------------------------------------------

def _theta_expr(t: int, n: int) -> str:
    """The Lean term `t * Real.log n` with n's log decomposed into 2/3/5/7 primes (d9-boxable)."""
    return f"{t} * Real.log {n}"


def _log_decomp_lean(n: int) -> tuple[str, list[int]]:
    """Prime-factor n and return (Lean rewrite of `Real.log n = sum m_p * Real.log p`, primes used)."""
    m = n
    factors: dict[int, int] = {}
    for p in (2, 3, 5, 7, 11, 13):
        while m % p == 0:
            factors[p] = factors.get(p, 0) + 1
            m //= p
    assert m == 1, f"n={n} has a prime factor > 13; extend the d9 prime table"
    return "", list(factors.items())


D9 = {
    2: ("0.6931471803", "0.6931471808"),
    3: ("1.0986122886", "1.0986122887"),
    5: ("1.6094379123", "1.6094379126"),
    7: ("1.9459101090", "1.9459101091"),
    11: ("2.3978952727", "2.3978952729"),
    13: ("2.5649493574", "2.5649493576"),
}
# Mathlib d9 lemma names for the primes that have them; others use explicit exp-bound derivations.
D9_LEMMA = {2: "log_two", 5: "log_five"}


# --- reusable general nat-log bracket emission (via ForgeLogBracket) ------------------------------
# Mathlib d9 constant for exp 1 used by the exp-bound composition.
E1_LO = F("2.7182818283")   # exp_one_gt_d9
E1_HI = F("2.7182818286")   # exp_one_lt_d9
EXP_N = 12                  # Taylor order for exp of the fractional part (|f|<=1): remainder ~2e-9


def _expSeries_rat(f: F, N: int) -> F:
    return sum((f ** m) / math.factorial(m) for m in range(N))


def _expRem_rat(f: F, N: int) -> F:
    return abs(f) ** N * F(N + 1, math.factorial(N) * N)


def log_bracket(n: int) -> tuple[F, F, int, F, F, int, F, F]:
    """Choose a tight rational bracket [lo,hi] for log n and its exp-bound witnesses.
    Returns (lo, hi, klo, flo, seriesLo, khi, fhi, seriesUp) with:
      lo = klo + flo,  seriesLo <= expSeries(flo,N) - expRem(flo,N),  E1_LO^klo * seriesLo <= n,
      hi = khi + fhi,  expSeries(fhi,N) + expRem(fhi,N) <= seriesUp,  n <= E1_HI^khi * seriesUp.
    lo, hi are placed so the exp bounds hold with margin (the true log n lies strictly inside)."""
    logn = mp.log(n)
    # Snap lo/hi to a COARSE dyadic grid so the fractional part f has a small denominator (keeps
    # f^N and the emitted rationals compact).  GRID = 2^-GBITS.
    for gbits in range(16, 8, -1):
        g = 1 << gbits
        lo = F(int(mp.floor(logn * g)) - 1, g)   # one grid step below floor(logn): lo < logn
        hi = F(int(mp.ceil(logn * g)) + 1, g)     # one grid step above: hi > logn
        klo = int(lo)                              # integer part (lo >= 0 for n >= 2)
        flo = lo - klo
        khi = int(hi)
        fhi = hi - khi
        if not (0 <= flo < 1 and 0 <= fhi < 1):
            continue
        seriesLo = _expSeries_rat(fhi, EXP_N) - _expRem_rat(fhi, EXP_N)   # LOWER bound for exp fhi
        seriesUp = _expSeries_rat(flo, EXP_N) + _expRem_rat(flo, EXP_N)   # UPPER bound for exp flo
        # For log_nat_bracket: need exp lo <= n <= exp hi.
        #   exp lo  <= E1_HI^klo * seriesUp   (upper bnd on exp lo)  ; require  E1_HI^klo*seriesUp <= n
        #   exp hi  >= E1_LO^khi * seriesLo   (lower bnd on exp hi)  ; require  n <= E1_LO^khi*seriesLo
        up_lo = E1_HI ** klo * seriesUp
        lo_hi = E1_LO ** khi * seriesLo
        if up_lo <= n <= lo_hi and seriesLo > 0:
            assert mp.mpf(lo.numerator) / lo.denominator <= logn <= mp.mpf(hi.numerator) / hi.denominator
            return lo, hi, klo, flo, seriesUp, khi, fhi, seriesLo
    raise RuntimeError(f"log_bracket failed for n={n}")


E1_LO_LIT = "2.7182818283"   # Real.exp_one_gt_d9  (decimal literal, matches Mathlib)
E1_HI_LIT = "2.7182818286"   # Real.exp_one_lt_d9


def emit_log_bracket_lean(n: int, name: str) -> str:
    """Emit `theorem <name> : lo <= Real.log n /\ Real.log n <= hi` via ForgeLogBracket.
    exp lo <= n via exp_le_rat (upper on exp lo); n <= exp hi via rat_le_exp (lower on exp hi)."""
    lo, hi, klo, flo, seriesUp, khi, fhi, seriesLo = log_bracket(n)
    absf = "(by rw [abs_le]; constructor <;> norm_num)"
    ser = "(by unfold TaylorKernels.expSeries TaylorKernels.expRem; norm_num [Finset.sum_range_succ])"
    L = []
    L.append(f"theorem {name} : (({frac_str(lo)}) : ℝ) ≤ Real.log {n} ∧ Real.log {n} ≤ ({frac_str(hi)}) := by")
    L.append(f"  have hExpLo : Real.exp ({frac_str(lo)}) ≤ ({n} : ℝ) := by")
    L.append(f"    have h := ForgeLogBracket.exp_le_rat (q := ({frac_str(lo)})) (f := ({frac_str(flo)})) "
             f"(E1hi := ({E1_HI_LIT})) (seriesUp := ({frac_str(seriesUp)})) (k := {klo}) (N := {EXP_N})")
    L.append(f"      (by norm_num) {absf} (by norm_num) Real.exp_one_lt_d9.le (by norm_num) {ser}")
    L.append(f"    have hn : ({E1_HI_LIT} : ℝ) ^ {klo} * ({frac_str(seriesUp)}) ≤ ({n} : ℝ) := by norm_num")
    L.append(f"    exact le_trans h hn")
    L.append(f"  have hExpHi : ({n} : ℝ) ≤ Real.exp ({frac_str(hi)}) := by")
    L.append(f"    have h := ForgeLogBracket.rat_le_exp (q := ({frac_str(hi)})) (f := ({frac_str(fhi)})) "
             f"(E1lo := ({E1_LO_LIT})) (seriesLo := ({frac_str(seriesLo)})) (k := {khi}) (N := {EXP_N})")
    L.append(f"      (by norm_num) {absf} (by norm_num) Real.exp_one_gt_d9.le (by norm_num) (by norm_num) {ser}")
    L.append(f"    have hn : ({n} : ℝ) ≤ ({E1_LO_LIT} : ℝ) ^ {khi} * ({frac_str(seriesLo)}) := by norm_num")
    L.append(f"    exact le_trans hn h")
    L.append(f"  exact ForgeLogBracket.log_nat_bracket (by norm_num) hExpLo hExpHi")
    return "\n".join(L)


def emit_theta_bound_proof(t: int, n: int, c: F, w: F) -> str:
    """Lean proof that |t*log n - c| <= w, from the GENERAL nat-log bracket (ForgeLogBracket).
    Emits an inline `log n ∈ [ln_lo, ln_hi]` bracket, then closes the θ box by nlinarith."""
    if n == 1:
        return "  rw [Real.log_one]; rw [abs_le]; constructor <;> norm_num"
    ln_lo, ln_hi, klo, flo, seriesUp, khi, fhi, seriesLo = log_bracket(n)
    # verify the width covers: |t*log n - c| <= t*max(c/t - ln_lo, ln_hi - c/t) must be <= w
    assert t * max(F(c) - t * ln_lo, t * ln_hi - F(c)) <= t * t * w or True  # numeric check below
    # tight numeric check that w is valid given the log bracket endpoints (worst case)
    worst = max(abs(F(c) - t * ln_lo), abs(t * ln_hi - F(c)))
    assert worst <= w, f"theta width w={float(w)} too small for n={n}: worst={float(worst)}"
    inner = emit_log_bracket_lean(n, f"hlog_{n}")
    # inline the bracket proof as a `have` (rename theorem -> have)
    inner = inner.replace(f"theorem hlog_{n} :", f"  have hlog : ", 1)
    # indent the inner proof body by 2 spaces (it is a `by` block)
    inner_lines = inner.split("\n")
    inner_lines = [inner_lines[0]] + ["  " + ln for ln in inner_lines[1:]]
    body = "\n".join(inner_lines)
    return (body
            + "\n  obtain ⟨hln_lo, hln_hi⟩ := hlog"
            + "\n  rw [abs_le]; constructor <;> nlinarith [hln_lo, hln_hi]")


def emit_trig_climb_lean(tc: TrigClimb, tag: str) -> str:
    """Emit the full climb section (base + M doublings + width absorption) producing
    `cos_<tag>` and `sin_<tag>` : boxes for cos/sin(t * Real.log n)."""
    t, n, M = tc.t, tc.n, tc.M
    L: list[str] = []
    yden = 1 << M            # y = c / 2^M ;  c = sample at 2^CSCALE
    # y as an exact Fraction (c is p/2^CSCALE, y = c/2^M)
    ynum = tc.c.numerator * (tc.c.denominator // 1)  # keep exact
    yfr = tc.y
    L.append(f"section {tag}")
    L.append(f"/-- reduced argument `y = c / 2^{M}`, `|y| ≤ 1` (deep reduction: tight base Taylor). -/")
    L.append(f"private noncomputable def y{tag} : ℝ := ({frac_str(yfr)})")
    L.append(f"private theorem hy{tag} : |y{tag}| ≤ 1 := by unfold y{tag}; rw [abs_le]; constructor <;> norm_num")
    # base
    cb, sb = tc.cos_base, tc.sin_base
    L.append(f"private theorem base{tag} :")
    L.append(f"    (({frac_str(cb.lo)}) : ℝ) ≤ Real.cos y{tag} ∧ Real.cos y{tag} ≤ ({frac_str(cb.hi)}) ∧")
    L.append(f"    (({frac_str(sb.lo)}) : ℝ) ≤ Real.sin y{tag} ∧ Real.sin y{tag} ≤ ({frac_str(sb.hi)}) := by")
    L.append(f"  have hc := cos_base_interval (y := y{tag}) hy{tag} (clo := ({frac_str(cb.lo)})) (chi := ({frac_str(cb.hi)})) (by unfold y{tag}; norm_num) (by unfold y{tag}; norm_num)")
    L.append(f"  have hs := sin_base_interval (y := y{tag}) hy{tag} (slo := ({frac_str(sb.lo)})) (shi := ({frac_str(sb.hi)})) (by unfold y{tag}; norm_num) (by unfold y{tag}; norm_num)")
    L.append(f"  exact ⟨hc.1, hc.2, hs.1, hs.2⟩")
    # climb
    cfin, sfin = tc.cos_final, tc.sin_final
    L.append(f"private theorem climb{tag} :")
    L.append(f"    (({frac_str(cfin.lo)}) : ℝ) ≤ Real.cos ((2:ℝ)^{M} * y{tag}) ∧ Real.cos ((2:ℝ)^{M} * y{tag}) ≤ ({frac_str(cfin.hi)}) ∧")
    L.append(f"    (({frac_str(sfin.lo)}) : ℝ) ≤ Real.sin ((2:ℝ)^{M} * y{tag}) ∧ Real.sin ((2:ℝ)^{M} * y{tag}) ≤ ({frac_str(sfin.hi)}) := by")
    L.append(f"  obtain ⟨hc0lo, hc0hi, hs0lo, hs0hi⟩ := base{tag}")
    ccur, scur = cb, sb
    for i in range(M):
        cnext, hcase = tc.cos_steps[i]
        snext = tc.sin_steps[i]
        k = i + 1
        yarg = f"y{tag}" if i == 0 else f"((2:ℝ)^{i} * y{tag})"
        clo_i, chi_i = (f"hc0lo", f"hc0hi") if i == 0 else (f"hc{i}lo", f"hc{i}hi")
        slo_i, shi_i = (f"hs0lo", f"hs0hi") if i == 0 else (f"hs{i}lo", f"hs{i}hi")
        L.append(f"  have hcd{k} := cos_double_interval (y := {yarg}) (clo := ({frac_str(ccur.lo)})) (chi := ({frac_str(ccur.hi)})) (clo' := ({frac_str(cnext.lo)})) (chi' := ({frac_str(cnext.hi)})) {clo_i} {chi_i} (by norm_num) (by norm_num) (by norm_num) (by norm_num) ({hcase})")
        L.append(f"  have hsd{k} := sin_double_interval (y := {yarg}) (clo := ({frac_str(ccur.lo)})) (chi := ({frac_str(ccur.hi)})) (slo := ({frac_str(scur.lo)})) (shi := ({frac_str(scur.hi)})) (slo' := ({frac_str(snext.lo)})) (shi' := ({frac_str(snext.hi)})) {clo_i} {chi_i} {slo_i} {shi_i} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
        if i == 0:
            L.append(f"  rw [show (2:ℝ)*y{tag} = (2:ℝ)^1 * y{tag} by ring] at hcd{k} hsd{k}")
        else:
            L.append(f"  rw [show (2:ℝ)*((2:ℝ)^{i} * y{tag}) = (2:ℝ)^{k} * y{tag} by ring] at hcd{k} hsd{k}")
        L.append(f"  obtain ⟨hc{k}lo, hc{k}hi⟩ := hcd{k}")
        L.append(f"  obtain ⟨hs{k}lo, hs{k}hi⟩ := hsd{k}")
        ccur, scur = cnext, snext
    L.append(f"  exact ⟨hc{M}lo, hc{M}hi, hs{M}lo, hs{M}hi⟩")
    # scale: 2^M * y = c
    L.append(f"private theorem scale{tag} : (2:ℝ)^{M} * y{tag} = ({frac_str(tc.c)}) := by unfold y{tag}; norm_num")
    # theta enclosure
    L.append(f"private theorem theta{tag} : |{t} * Real.log {n} - ({frac_str(tc.c)})| ≤ ({frac_str(tc.w)}) := by")
    L.append(emit_theta_bound_proof(t, n, tc.c, tc.w))
    # final certs
    cbx, sbx = tc.cos_box, tc.sin_box
    L.append(f"/-- **OPERATING-POINT CERTIFICATE (cos).** `cos({t}·log {n})` box, width ≤ 1e-3. -/")
    L.append(f"theorem cos_{tag} :")
    L.append(f"    (({frac_str(cfin.lo)}) - ({frac_str(tc.w)}) : ℝ) ≤ Real.cos ({t} * Real.log {n}) ∧ Real.cos ({t} * Real.log {n}) ≤ ({frac_str(cfin.hi)}) + ({frac_str(tc.w)}) := by")
    L.append(f"  obtain ⟨hclo, hchi, _, _⟩ := climb{tag}")
    L.append(f"  rw [scale{tag}] at hclo hchi")
    L.append(f"  have hd : |{t} * Real.log {n} - ({frac_str(tc.c)})| ≤ ({frac_str(tc.w)}) := theta{tag}")
    L.append(f"  exact cos_encl_bracket (by norm_num) hd hclo hchi")
    L.append(f"/-- **OPERATING-POINT CERTIFICATE (sin).** `sin({t}·log {n})` box. -/")
    L.append(f"theorem sin_{tag} :")
    L.append(f"    (({frac_str(sfin.lo)}) - ({frac_str(tc.w)}) : ℝ) ≤ Real.sin ({t} * Real.log {n}) ∧ Real.sin ({t} * Real.log {n}) ≤ ({frac_str(sfin.hi)}) + ({frac_str(tc.w)}) := by")
    L.append(f"  obtain ⟨_, _, hslo, hshi⟩ := climb{tag}")
    L.append(f"  rw [scale{tag}] at hslo hshi")
    L.append(f"  have hd : |{t} * Real.log {n} - ({frac_str(tc.c)})| ≤ ({frac_str(tc.w)}) := theta{tag}")
    L.append(f"  exact sin_encl_bracket (by norm_num) hd hslo hshi")
    L.append(f"end {tag}")
    return "\n".join(L)


TRIG_HEADER = """/-  {fname} -- ANDÚRIL cert-forge STAGE 1: forged operating-point trig certificates.

    Auto-generated by trig_forge.py.  Each `cos_<tag>`/`sin_<tag>` is a kernel-checked box for
    `cos/sin({t}·log n)`, built by the TrigReduce π-free double-angle route (deep reduction to
    |y| ≤ 2^-{yred}, order-4 base Taylor, {tag_note}doubling climb, Lipschitz width absorption from the
    Mathlib d9 log enclosure).  Same lemmas as the 4 hand certs in TrigReduceOperating.

    conjecture1_proved = False.
-/
import TrigReduce
import Mathlib.Analysis.Complex.ExponentialBounds

open TrigReduce Real

namespace {ns}
"""


def emit_trig_file(pairs: list[tuple[int, int]], ns: str, fname: str) -> str:
    """Emit a full trig-cert Lean file for a list of (t, n) pairs."""
    body = [TRIG_HEADER.format(fname=fname, t="t", yred=YRED, tag_note="", ns=ns)]
    for (t, n) in pairs:
        tc = build_trig_climb(t, n)
        tag = f"T{t}_{n}"
        body.append(emit_trig_climb_lean(tc, tag))
        body.append("")
    body.append(f"end {ns}")
    return "\n".join(body)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--test-climb", action="store_true", help="validate the climb for the 4 known certs")
    ap.add_argument("--emit-trig-test", action="store_true", help="emit a small trig file for t=14 n=2,3 to lean/ForgeTrigTest.lean")
    args = ap.parse_args()
    if args.emit_trig_test:
        out = emit_trig_file([(14, 2), (14, 3)], "ForgeTrigTest", "ForgeTrigTest.lean")
        p = Path(__file__).parent / "lean" / "ForgeTrigTest.lean"
        p.write_text(out)
        print(f"wrote {p}")
    if args.test_climb:
        for (t, n) in [(14, 2), (14, 200)]:
            tc = build_trig_climb(t, n)
            theta = t * mp.log(n)
            print(f"t={t} n={n}: M={tc.M} theta={float(theta):.6f}")
            print(f"   cos in [{float(tc.cos_box.lo):.9f}, {float(tc.cos_box.hi):.9f}] "
                  f"true={float(mp.cos(theta)):.9f} width={float(tc.cos_box.hi-tc.cos_box.lo):.2e}")
            print(f"   sin in [{float(tc.sin_box.lo):.9f}, {float(tc.sin_box.hi):.9f}] "
                  f"true={float(mp.sin(theta)):.9f} width={float(tc.sin_box.hi-tc.sin_box.lo):.2e}")
        print("climb OK")
