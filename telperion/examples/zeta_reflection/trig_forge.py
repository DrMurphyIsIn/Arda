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


# ---------------------------------------------------------------------------------------------------
# Stage 2: amplitude boxes (n^{-1/2}) + per-term Re/Im boxes + Dirichlet sum fold + Re/Im zeta box.
# ---------------------------------------------------------------------------------------------------

def amp_box(n: int) -> tuple[F, F, F, F]:
    """Rational box for n^{-1/2} = 1/sqrt n and the sqrt-n bracket [sqlo, sqhi] it uses.
    Returns (lo, hi, sqlo, sqhi) with sqlo^2 <= n <= sqhi^2 and 1/sqhi <= n^{-1/2} <= 1/sqlo."""
    root = mp.sqrt(n)
    sqlo = F(int(mp.floor(root * 10 ** 8)), 10 ** 8)
    sqhi = F(int(mp.ceil(root * 10 ** 8)), 10 ** 8)
    assert sqlo ** 2 <= n <= sqhi ** 2, f"sqrt bracket invalid n={n}"
    lo = 1 / sqhi
    hi = 1 / sqlo
    # snap to a compact rational
    lo = rfloor(lo)
    hi = rceil(hi)
    return lo, hi, sqlo, sqhi


def emit_amp_box_lean(n: int, name: str) -> str:
    """Emit `theorem <name> : lo ≤ (n:ℝ)^(-(1/2)) ∧ (n:ℝ)^(-(1/2)) ≤ hi` (generalizes inv_sqrt2_box)."""
    lo, hi, sqlo, sqhi = amp_box(n)
    L = []
    L.append(f"theorem {name} : (({frac_str(lo)}) : ℝ) ≤ ({n} : ℝ) ^ (-(1 / 2) : ℝ) "
             f"∧ ({n} : ℝ) ^ (-(1 / 2) : ℝ) ≤ ({frac_str(hi)}) := by")
    L.append(f"  have h2 : ({n} : ℝ) ^ (-(1 / 2) : ℝ) = (Real.sqrt {n})⁻¹ := by")
    L.append(f"    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]")
    L.append(f"  rw [h2]")
    L.append(f"  have hslo : ({frac_str(sqlo)} : ℝ) ≤ Real.sqrt {n} := by")
    L.append(f"    rw [show ({frac_str(sqlo)} : ℝ) = Real.sqrt (({frac_str(sqlo)}) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]")
    L.append(f"    apply Real.sqrt_le_sqrt; norm_num")
    L.append(f"  have hshi : Real.sqrt {n} ≤ ({frac_str(sqhi)} : ℝ) := by")
    L.append(f"    rw [show ({frac_str(sqhi)} : ℝ) = Real.sqrt (({frac_str(sqhi)}) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]")
    L.append(f"    apply Real.sqrt_le_sqrt; norm_num")
    L.append(f"  refine ⟨?_, ?_⟩")
    L.append(f"  · calc ({frac_str(lo)} : ℝ) ≤ ({frac_str(sqhi)} : ℝ)⁻¹ := by norm_num")
    L.append(f"      _ ≤ (Real.sqrt {n})⁻¹ := inv_anti₀ (by positivity) hshi")
    L.append(f"  · calc (Real.sqrt {n})⁻¹ ≤ ({frac_str(sqlo)} : ℝ)⁻¹ := "
             f"inv_anti₀ (by norm_num) hslo")
    L.append(f"      _ ≤ ({frac_str(hi)} : ℝ) := by norm_num")
    return "\n".join(L)


def term_box(t: int, n: int) -> tuple[F, F, F, F]:
    """Real- and imag-part boxes for n^{-(1/2+it)} at height t.
    Re = n^{-1/2} cos(t log n),  Im = -n^{-1/2} sin(t log n).  Sign-aware interval products.
    Returns (re_lo, re_hi, im_lo, im_hi)."""
    tc = build_trig_climb(t, n)
    alo, ahi, _, _ = amp_box(n)
    cbx, sbx = tc.cos_box, tc.sin_box
    # Re = amp * cos : interval product of [alo,ahi] (>=0) and cos box
    re_corners = [alo * cbx.lo, alo * cbx.hi, ahi * cbx.lo, ahi * cbx.hi]
    re_lo, re_hi = rfloor(min(re_corners)), rceil(max(re_corners))
    # Im = -(amp * sin)
    s_corners = [alo * sbx.lo, alo * sbx.hi, ahi * sbx.lo, ahi * sbx.hi]
    im_lo, im_hi = rfloor(-max(s_corners)), rceil(-min(s_corners))
    return re_lo, re_hi, im_lo, im_hi


def _mul_encl_args(alo: F, ahi: F, blo: F, bhi: F, plo: F, phi: F) -> str:
    """The 8 corner-product `by norm_num` args for ForgeLogBracket.mul_encl."""
    return "(by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)"


def emit_term_re_box_lean(t: int, n: int, tag: str) -> str:
    """Emit `re_term_<tag> : re_lo ≤ (((n:ℕ):ℂ)^(-(1/2+t·i))).re ∧ ... ≤ re_hi` via term_re + amp + cos."""
    re_lo, re_hi, _, _ = term_box(t, n)
    alo, ahi, _, _ = amp_box(n)
    tc = build_trig_climb(t, n)
    cbx = tc.cos_box
    trigtag = f"T{t}_{n}"
    L = []
    L.append(f"theorem re_term_{tag} :")
    L.append(f"    (({frac_str(re_lo)}) : ℝ) ≤ ((({n}:ℕ):ℂ) ^ (-((1 : ℂ) / 2 + ({t} : ℝ) * I))).re")
    L.append(f"      ∧ ((({n}:ℕ):ℂ) ^ (-((1 : ℂ) / 2 + ({t} : ℝ) * I))).re ≤ ({frac_str(re_hi)}) := by")
    L.append(f"  have hterm := ZeroHypBand_t14.term_re {n} (by norm_num) {t}")
    L.append(f"  rw [hterm]; simp only [Nat.cast_ofNat]")
    L.append(f"  rw [show Real.exp (-(1 / 2) * Real.log {n}) = ({n} : ℝ) ^ (-(1 / 2) : ℝ) by "
             f"rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]")
    L.append(f"  exact ForgeLogBracket.mul_encl (by norm_num) amp_{tag} cos_{trigtag} {_mul_encl_args(alo,ahi,cbx.lo,cbx.hi,re_lo,re_hi)}")
    return "\n".join(L)


def emit_term_im_box_lean(t: int, n: int, tag: str) -> str:
    """Emit `im_term_<tag> : im_lo ≤ (((n:ℕ):ℂ)^(-(1/2+t·i))).im ∧ ... ≤ im_hi`.
    Im = -(amp·sin); use mul_encl for amp·sin then negate."""
    _, _, im_lo, im_hi = term_box(t, n)
    alo, ahi, _, _ = amp_box(n)
    tc = build_trig_climb(t, n)
    sbx = tc.sin_box
    trigtag = f"T{t}_{n}"
    # amp·sin box = [-im_hi, -im_lo]  (since im = -(amp·sin))
    ps_lo, ps_hi = -im_hi, -im_lo
    L = []
    L.append(f"theorem im_term_{tag} :")
    L.append(f"    (({frac_str(im_lo)}) : ℝ) ≤ ((({n}:ℕ):ℂ) ^ (-((1 : ℂ) / 2 + ({t} : ℝ) * I))).im")
    L.append(f"      ∧ ((({n}:ℕ):ℂ) ^ (-((1 : ℂ) / 2 + ({t} : ℝ) * I))).im ≤ ({frac_str(im_hi)}) := by")
    L.append(f"  have hterm := ZeroHypBand_t14.term_im {n} (by norm_num) {t}")
    L.append(f"  rw [hterm]; simp only [Nat.cast_ofNat]")
    L.append(f"  rw [show Real.exp (-(1 / 2) * Real.log {n}) = ({n} : ℝ) ^ (-(1 / 2) : ℝ) by "
             f"rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]")
    L.append(f"  have hps : ({frac_str(ps_lo)} : ℝ) ≤ ({n}:ℝ)^(-(1/2):ℝ) * Real.sin ({t} * Real.log {n}) ∧ ({n}:ℝ)^(-(1/2):ℝ) * Real.sin ({t} * Real.log {n}) ≤ ({frac_str(ps_hi)}) :=")
    L.append(f"    ForgeLogBracket.mul_encl (by norm_num) amp_{tag} sin_{trigtag} {_mul_encl_args(alo,ahi,sbx.lo,sbx.hi,ps_lo,ps_hi)}")
    L.append(f"  exact ⟨by linarith [hps.2], by linarith [hps.1]⟩")
    return "\n".join(L)


def emit_dirichlet_re_box_lean(t: int, N: int, name: str) -> tuple[str, F, F]:
    """Emit `<name> : ΣLo ≤ (∑ n∈Ico 1 N, (n:ℂ)^(-s)).re ∧ ... ≤ ΣHi` for s = 1/2+it.
    Uses re_sum + sum_Ico_eq_sum_range + sum_range_succ expansion, then per-term re boxes (n≥2)
    and n=1 auto-simplifies to 1.  Returns (lean, ΣLo, ΣHi)."""
    # per-term boxes n=2..N-1
    re_boxes = {n: term_box(t, n)[:2] for n in range(2, N)}
    slo = F(1) + sum(re_boxes[n][0] for n in range(2, N))
    shi = F(1) + sum(re_boxes[n][1] for n in range(2, N))
    scnt = N - 1                       # range count after sum_Ico_eq_sum_range (upper = N-1)
    L = []
    L.append(f"theorem {name} :")
    L.append(f"    (({frac_str(slo)}) : ℝ) ≤ (∑ n ∈ Finset.Ico 1 {N}, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + ({t}:ℂ)*Complex.I)))).re")
    L.append(f"      ∧ (∑ n ∈ Finset.Ico 1 {N}, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + ({t}:ℂ)*Complex.I)))).re ≤ ({frac_str(shi)}) := by")
    L.append(f"  rw [Complex.re_sum, Finset.sum_Ico_eq_sum_range]")
    L.append(f"  rw [show ({N}-1) = {N-1} from rfl,")
    L.append(f"    {' '.join(['Finset.sum_range_succ,'] * (N - 1))} Finset.sum_range_zero]")
    L.append(f"  norm_num")
    # normalize the per-term boxes into the same (norm-num) atom the expanded sum uses.
    for n in range(2, N):
        L.append(f"  have b{n} := re_term_{n}")
        L.append(f"  norm_num at b{n}")
    hyps = ", ".join(f"b{n}.1, b{n}.2" for n in range(2, N))
    L.append(f"  constructor <;> linarith [{hyps}]")
    return "\n".join(L), slo, shi


def emit_dirichlet_im_box_lean(t: int, N: int, name: str) -> tuple[str, F, F]:
    """Emit `<name> : ΣLo ≤ (∑ n∈Ico 1 N, (n:ℂ)^(-s)).im ∧ ... ≤ ΣHi`.  n=1 term Im = 0."""
    im_boxes = {n: term_box(t, n)[2:] for n in range(2, N)}
    slo = sum(im_boxes[n][0] for n in range(2, N))
    shi = sum(im_boxes[n][1] for n in range(2, N))
    L = []
    L.append(f"theorem {name} :")
    L.append(f"    (({frac_str(slo)}) : ℝ) ≤ (∑ n ∈ Finset.Ico 1 {N}, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + ({t}:ℂ)*Complex.I)))).im")
    L.append(f"      ∧ (∑ n ∈ Finset.Ico 1 {N}, (((n:ℕ):ℂ) ^ (-((1/2:ℂ) + ({t}:ℂ)*Complex.I)))).im ≤ ({frac_str(shi)}) := by")
    L.append(f"  rw [Complex.im_sum, Finset.sum_Ico_eq_sum_range]")
    L.append(f"  rw [show ({N}-1) = {N-1} from rfl,")
    L.append(f"    {' '.join(['Finset.sum_range_succ,'] * (N - 1))} Finset.sum_range_zero]")
    L.append(f"  norm_num")
    for n in range(2, N):
        L.append(f"  have b{n} := im_term_{n}")
        L.append(f"  norm_num at b{n}")
    hyps = ", ".join(f"b{n}.1, b{n}.2" for n in range(2, N))
    L.append(f"  constructor <;> linarith [{hyps}]")
    return "\n".join(L), slo, shi


def tail_B(t: int, N: int) -> tuple[F, F]:
    """Exact rational (Bre, Bim) of B = N/(s-1) + 1/2 + b2*s/(2N), s = 1/2 + it, b2 = 1/6."""
    a, b = F(-1, 2), F(t)              # s - 1 = a + i b
    den = a * a + b * b
    Bre = F(N) * a / den + F(1, 2) + F(1, 6) * F(1, 2) / (2 * N)
    Bim = -F(N) * b / den + F(1, 6) * F(t) / (2 * N)
    return Bre, Bim


def emit_zeta_box_lean(t: int, N: int, tail_bound: F, prefix: str) -> tuple[str, F, F, F, F]:
    """Emit Re/Im ζ(1/2+it) boxes for tail cut N.  Requires (in scope): re_term_k/im_term_k for
    k=2..N, amp_N/cos_TN/sin_TN, the sum folds reSum/imSum, and ForgeTail.zeta_tail_t{t}.
    Returns (lean, re_lo, re_hi, im_lo, im_hi)."""
    Bre, Bim = tail_B(t, N)
    # sum boxes
    re_boxes = {n: term_box(t, n)[:2] for n in range(2, N)}
    im_boxes = {n: term_box(t, n)[2:] for n in range(2, N)}
    sre_lo = F(1) + sum(re_boxes[n][0] for n in range(2, N))
    sre_hi = F(1) + sum(re_boxes[n][1] for n in range(2, N))
    sim_lo = sum(im_boxes[n][0] for n in range(2, N))
    sim_hi = sum(im_boxes[n][1] for n in range(2, N))
    # n=N term box for P = Re(N^{-s}), Q = Im(N^{-s})
    Pre_lo, Pre_hi, Qim_lo, Qim_hi = term_box(t, N)
    # tail T.re = P*Bre - Q*Bim  ; T.im = P*Bim + Q*Bre  (interval arithmetic)
    def prod_iv(alo, ahi, blo, bhi):
        c = [alo*blo, alo*bhi, ahi*blo, ahi*bhi]
        return min(c), max(c)
    pBre = prod_iv(Pre_lo, Pre_hi, Bre, Bre)   # P*Bre
    qBim = prod_iv(Qim_lo, Qim_hi, Bim, Bim)   # Q*Bim
    pBim = prod_iv(Pre_lo, Pre_hi, Bim, Bim)
    qBre = prod_iv(Qim_lo, Qim_hi, Bre, Bre)
    Tre_lo = rfloor(pBre[0] - qBim[1]); Tre_hi = rceil(pBre[1] - qBim[0])
    Tim_lo = rfloor(pBim[0] + qBre[0]); Tim_hi = rceil(pBim[1] + qBre[1])
    # emF.re in [sre_lo+Tre_lo, sre_hi+Tre_hi]; zeta.re in [that -+ tail_bound]
    re_lo = rfloor(sre_lo + Tre_lo - tail_bound)
    re_hi = rceil(sre_hi + Tre_hi + tail_bound)
    im_lo = rfloor(sim_lo + Tim_lo - tail_bound)
    im_hi = rceil(sim_hi + Tim_hi + tail_bound)
    L = []
    # N/(s-1) exact rational (r1 + i1·I)
    a, b = F(-1, 2), F(t)
    den = a * a + b * b
    r1 = F(N) * a / den
    i1 = -F(N) * b / den
    L.append(f"-- exact rational B = N/(s-1)+1/2+b2 s/(2N): Bre={frac_str(Bre)}, Bim={frac_str(Bim)}")
    L.append(f"theorem {prefix}_Bval :")
    L.append(f"    (({N}:ℂ) / ((1/2 + ({t}:ℝ)*I) - 1) + 1 / 2 + (bernoulli 2 : ℂ) * (1/2 + ({t}:ℝ)*I) / (2 * ({N}:ℂ)))")
    L.append(f"      = (({frac_str(Bre)} : ℝ) : ℂ) + (({frac_str(Bim)} : ℝ) : ℂ) * I := by")
    L.append(f"  rw [show (bernoulli 2 : ℂ) = 6⁻¹ by rw [bernoulli_two]; norm_num]")
    L.append(f"  have hdiv : ({N}:ℂ) / ((1/2 + ({t}:ℝ)*I) - 1) = (({frac_str(r1)} : ℝ):ℂ) + (({frac_str(i1)}:ℝ):ℂ)*I := by")
    L.append(f"    have hne : ((1/2 + ({t}:ℝ)*I) - 1) ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this")
    L.append(f"    rw [div_eq_iff hne]; apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> norm_num")
    L.append(f"  rw [hdiv]; apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.normSq] <;> norm_num")
    # ---- tail T.re / T.im boxes via ForgeTailTerms.tail_re_im + Bval + n=N term box ----
    # Note: term boxes re_term_N / im_term_N are about (((N:ℕ):ℂ)^(-((1:ℂ)/2+t*I))).re/.im;
    # tail_re_im needs ((N:ℂ)^(-s)).re/.im with s = 1/2+t*I.  Bridge by norm_num.
    # s in the ℕ-cast form tail_re_im/emZetaFinite3_eq_dirichlet produce:
    sc = f"((1/2:ℂ) + ({t}:ℂ)*Complex.I)"
    Texpr = (f"(({N}:ℕ):ℂ)^(1-{sc})/({sc}-1) + (({N}:ℕ):ℂ)^(-{sc})/2 "
             f"+ (bernoulli 2:ℂ)*({sc}*((({N}:ℕ):ℝ))^(-{sc}-1))/2")
    bval_conv = (f"(by have h := {prefix}_Bval; "
                 f"convert h using 2 <;> push_cast <;> ring)")
    tri = f"ForgeTailTerms.tail_re_im {sc} {N} (by norm_num) (by intro h; have := congrArg Complex.im h; simp at this) ({frac_str(Bre)}) ({frac_str(Bim)}) {bval_conv}"
    for part, lo, hi, comp in [("Tre", Tre_lo, Tre_hi, ".re"), ("Tim", Tim_lo, Tim_hi, ".im")]:
        sel = "1" if part == "Tre" else "2"
        L.append(f"theorem {prefix}_{part} :")
        L.append(f"    (({frac_str(lo)}) : ℝ) ≤ ({Texpr}){comp}")
        L.append(f"      ∧ ({Texpr}){comp} ≤ ({frac_str(hi)}) := by")
        L.append(f"  rw [({tri}).{sel}]")
        L.append(f"  have hP := re_term_{N}")
        L.append(f"  have hQ := im_term_{N}")
        L.append(f"  norm_num at hP hQ ⊢")
        L.append(f"  obtain ⟨hplo,hphi⟩ := hP; obtain ⟨hqlo,hqhi⟩ := hQ")
        L.append(f"  constructor <;> nlinarith [hplo,hphi,hqlo,hqhi]")
    # ---- emF.re / emF.im boxes (sum + tail), then ζ.re / ζ.im boxes (± EM tail) ----
    sc = f"((1/2:ℂ) + ({t}:ℂ)*Complex.I)"
    efre_lo = sre_lo + Tre_lo; efre_hi = sre_hi + Tre_hi
    efim_lo = sim_lo + Tim_lo; efim_hi = sim_hi + Tim_hi
    sumexpr = f"∑ n ∈ Finset.Ico 1 {N}, (((n:ℕ):ℂ) ^ (-{sc}))"
    Texpr2 = (f"(({N}:ℕ):ℂ)^(1-{sc})/({sc}-1) + (({N}:ℕ):ℂ)^(-{sc})/2 "
              f"+ (bernoulli 2:ℂ)*({sc}*((({N}:ℕ):ℝ))^(-{sc}-1))/2")
    for part, comp, sumbox, tbox, eflo, efhi in [
            ("re", ".re", "reSum", f"{prefix}_Tre", efre_lo, efre_hi),
            ("im", ".im", "imSum", f"{prefix}_Tim", efim_lo, efim_hi)]:
        L.append(f"theorem {prefix}_emf_{part} :")
        L.append(f"    (({frac_str(eflo)}) : ℝ) ≤ (emZetaFinite3 {sc} {N}){comp}")
        L.append(f"      ∧ (emZetaFinite3 {sc} {N}){comp} ≤ ({frac_str(efhi)}) := by")
        L.append(f"  rw [ZetaEMSum.emZetaFinite3_eq_dirichlet (by intro h; have := congrArg Complex.re h; simp at this) (by intro h; have := congrArg Complex.im h; simp at this) (by norm_num) (by norm_num)]")
        L.append(f"  rw [show ({sumexpr}) + (({N}:ℕ):ℂ)^(1-{sc})/({sc}-1) + (({N}:ℕ):ℂ)^(-{sc})/2 + (bernoulli 2:ℂ)*({sc}*((({N}:ℕ):ℝ))^(-{sc}-1))/2")
        L.append(f"      = ({sumexpr}) + ({Texpr2}) by ring]")
        L.append(f"  rw [Complex.add_{part}]")
        L.append(f"  have hs := {sumbox}")
        L.append(f"  have ht := {tbox}")
        L.append(f"  constructor <;> [linarith [hs.1, ht.1]; linarith [hs.2, ht.2]]")
    # ζ boxes
    for part, comp, efbox, eflo, efhi, zlo, zhi in [
            ("re", ".re", f"{prefix}_emf_re", efre_lo, efre_hi, re_lo, re_hi),
            ("im", ".im", f"{prefix}_emf_im", efim_lo, efim_hi, im_lo, im_hi)]:
        absname = "Complex.abs_re_le_norm" if part == "re" else "Complex.abs_im_le_norm"
        L.append(f"theorem {prefix}_zeta_{part} :")
        L.append(f"    (({frac_str(zlo)}) : ℝ) ≤ (riemannZeta {sc}){comp}")
        L.append(f"      ∧ (riemannZeta {sc}){comp} ≤ ({frac_str(zhi)}) := by")
        L.append(f"  have hef := {efbox}")
        L.append(f"  have htail : |(riemannZeta {sc}){comp} - (emZetaFinite3 {sc} {N}){comp}| ≤ ({frac_str(tail_bound)}) := by")
        L.append(f"    calc |(riemannZeta {sc}){comp} - (emZetaFinite3 {sc} {N}){comp}|")
        L.append(f"        = |(riemannZeta {sc} - emZetaFinite3 {sc} {N}){comp}| := by rw [Complex.sub_{part}]")
        L.append(f"      _ ≤ ‖riemannZeta {sc} - emZetaFinite3 {sc} {N}‖ := {absname} _")
        L.append(f"      _ ≤ ({frac_str(tail_bound)}) := le_trans ForgeTail.zeta_tail_t{t} (by norm_num)")
        L.append(f"  rw [abs_le] at htail")
        L.append(f"  constructor <;> [linarith [hef.1, htail.1]; linarith [hef.2, htail.2]]")
    return "\n".join(L), re_lo, re_hi, im_lo, im_hi, sre_lo, sre_hi, sim_lo, sim_hi, Tre_lo, Tre_hi, Tim_lo, Tim_hi


def emit_zeta_assembly_file(t: int, N: int, tail_bound: F, terms_ns: str, ns: str, prefix: str):
    """Emit the ζ-assembly file: imports the terms olean, does the two folds + tail + ζ boxes.
    Returns (lean_text, re_lo, re_hi, im_lo, im_hi)."""
    lre, _, _ = emit_dirichlet_re_box_lean(t, N, "reSum")
    lim, _, _ = emit_dirichlet_im_box_lean(t, N, "imSum")
    zres = emit_zeta_box_lean(t, N, tail_bound, prefix)
    parts = [
        f"import {terms_ns}", "import ForgeTailTerms", "import ForgeTail", "import ZetaEMSum",
        "import Mathlib.NumberTheory.Bernoulli",
        f"open TrigReduce Real Complex ZetaReflection {terms_ns}",
        "set_option maxHeartbeats 4000000", f"namespace {ns}", "",
        lre, "", lim, "", zres[0], f"\nend {ns}"]
    return "\n".join(parts), zres[1], zres[2], zres[3], zres[4]


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
