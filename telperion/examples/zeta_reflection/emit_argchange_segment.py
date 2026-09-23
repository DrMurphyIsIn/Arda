#!/usr/bin/env python3
"""emit_argchange_segment.py -- K6 (argument-change bricks) instantiation of one ladder segment.

Bricks K6a / K6b of the ANDURIL Arb discharge (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md,
section 1.3; Lean: ArgZetaTwo.lean, ArgGammaR.lean, ArgChangeGlue.lean).  Input: a K0/K1 band-glue
module `BandGlue_<seg>.lean` (emitted by emit_band_glue.py: the segment's bands as
`BandGlue.BandData`, parameters verbatim from the band modules) and the band modules themselves
(for the Blaschke ball constants).  Output: a Lean module that

  * boxes the transcendental ingredients of the closed-form Gamma_R brackets `ArgGammaR.S2`,
    `ArgGammaR.Sm1` at every edge height (logs by the Mathlib Taylor bound of log(1 - x) after a
    power-of-two split, arctans by the cubic bracket or the `ArctanTaylor` series, log pi and log 2
    from RSTheta's kernel boxes) -- every bound re-checked by `norm_num`/`linarith`;
  * re-parametrises every band (`segK i`): `[L1, H1] = [-249/250, 249/250]` (K6a, generic),
    `[L4, H4]`, `[L5, H5]` = rational enclosures of the K6b brackets, `L2 H2 L3 H3` (the two
    horizontal enclosures) UNCHANGED from the Arb band;
  * proves each band's `Valid` side conditions (pins by `norm_num`, the ball by
    `ArgChangeGlue.ball_of_sq`) and `K6Side`, and composes the segment's `BandHyp` and the height-H
    statement from `ArgChangeGlue.K6Inputs` (on-line zeros, two zero-free slabs, the two horizontal
    enclosures) with the height floor `HeightFloor.height_floor` discharging `hγ`.

Every pin is pre-checked here in exact rational arithmetic; the Lean side re-checks everything.
The numbers chosen here are untrusted: a wrong one makes the Lean file fail to compile, never a
wrong theorem.

Usage:  emit_argchange_segment.py <bandglue.lean> <zzl_lean_dir> <out.lean> <Module> <H>
conjecture1_proved = False.
"""
import math
import re
import sys
from fractions import Fraction as F
from pathlib import Path

LOG2_LO = F(3465735902799708427977, 5000000000000000000000)   # RSDesignTheta.log2_box
LOG2_HI = F(6931471805599487910229, 10000000000000000000000)
LOGPI_LO = F(11447298858493313056567, 10000000000000000000000)  # RSDesignTheta.logpi_box
LOGPI_HI = F(5723649429247365361409, 5000000000000000000000)
PI_LO = F(314159265358979323846, 10**20)                          # Real.pi_gt_d20
PI_HI = F(314159265358979323847, 10**20)                          # Real.pi_lt_d20
K6A = F(249, 250)


def rdown(q, D):
    return F(math.floor(q * D), D)


def rup(q, D):
    return F(math.ceil(q * D), D)


def lit(q):
    """A Lean real literal for a rational."""
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


def tlit(q):
    """The height as a bare real term (matching `(41)` / `((965 / 4))` of the band table)."""
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} / {q.denominator} : ℝ)"


def tag(q):
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}d{q.denominator}"


def parse_frac(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        s = s[1:-1].strip()
    if '/' in s:
        a, b = s.split('/')
        return F(int(a.strip()), int(b.strip()))
    return F(int(s))


def split_top(s):
    """Split on top-level commas."""
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def series(x, n):
    S = sum(x ** (i + 1) / (i + 1) for i in range(n))
    eps = x ** (n + 1) / (1 - x)
    return -S - eps, -S + eps


def log_plan(v):
    """v = 2^k * (1 - x)  (form 'A') or 2^k / (1 - x)  (form 'B'), k >= 0, x <= 0.2929."""
    if v == F(1, 2):
        return ('half', None, None)
    k = max(0, round(math.log2(float(v))))
    r = v / F(2) ** k
    if r <= 1:
        return ('A', k, 1 - r)
    return ('B', k, 1 - 1 / r)


def log_bounds(v, n_for):
    form, k, x = log_plan(v)
    if form == 'half':
        return (-LOG2_HI, -LOG2_LO, form, k, x, 0, None)
    n = n_for(x)
    slo, shi = series(x, n)
    if form == 'A':
        lo, hi = k * LOG2_LO + slo, k * LOG2_HI + shi
    else:
        lo, hi = k * LOG2_LO - shi, k * LOG2_HI - slo
    return (lo, hi, form, k, x, n, (slo, shi))


def n_for(x):
    if x == 0:
        return 1
    n = 1
    while x ** (n + 1) / (1 - x) > F(1, 10**13):
        n += 1
    return n


def emit_log(name, vexpr, v, D):
    lo, hi, form, k, x, n, ser = log_bounds(v, n_for)
    LO, HI = rdown(lo, D), rup(hi, D)
    L = []
    L.append(f"theorem {name} : {lit(LO)} ≤ Real.log ({vexpr}) ∧ Real.log ({vexpr}) ≤ {lit(HI)} := by")
    if form == 'half':
        L.append(f"  rw [show ({vexpr} : ℝ) = 2⁻¹ by norm_num, Real.log_inv]")
        L.append("  obtain ⟨h2l, h2h⟩ := RSDesignTheta.log2_box")
        L.append("  constructor <;> linarith")
        return L, LO, HI
    xs = f"({x.numerator} / {x.denominator} : ℝ)"
    if form == 'A':
        L.append(f"  have hs : Real.log ({vexpr}) = {k} * Real.log 2 + Real.log (1 - {xs}) := by")
        L.append(f"    rw [show ({vexpr} : ℝ) = 2 ^ {k} * (1 - {xs}) by norm_num,")
        L.append("      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]")
        L.append("    push_cast; ring")
    else:
        L.append(f"  have hs : Real.log ({vexpr}) = {k} * Real.log 2 - Real.log (1 - {xs}) := by")
        L.append(f"    rw [show ({vexpr} : ℝ) = 2 ^ {k} * (1 - {xs})⁻¹ by norm_num,")
        L.append("      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_inv]")
        L.append("    push_cast; ring")
    L.append(f"  have h := ArgGammaR.log_one_sub_mem (x := {xs}) (by norm_num) (by norm_num) {n}")
    L.append("  norm_num [Finset.sum_range_succ] at h")
    L.append("  obtain ⟨h2l, h2h⟩ := RSDesignTheta.log2_box")
    L.append("  rw [hs]")
    L.append("  constructor <;> linarith [h.1, h.2]")
    return L, LO, HI


def emit_log_corr(name, vexpr, T_, x, halfname, lhlo, lhhi, D):
    """log v = 2 log (T/2) - log (1 - x), with v = (T/2)^2 (1 - x)^(-1) and x small."""
    n = n_for(x)
    slo, shi = series(x, n)
    lo, hi = 2 * lhlo - shi, 2 * lhhi - slo
    LO, HI = rdown(lo, D), rup(hi, D)
    xs = f"({x.numerator} / {x.denominator} : ℝ)"
    L = []
    L.append(f"theorem {name} : {lit(LO)} ≤ Real.log ({vexpr}) ∧ Real.log ({vexpr}) ≤ {lit(HI)} := by")
    L.append(f"  have hs : Real.log ({vexpr}) = 2 * Real.log ({T_} / 2) - Real.log (1 - {xs}) := by")
    L.append(f"    rw [show ({vexpr} : ℝ) = ({T_} / 2) ^ 2 * (1 - {xs})⁻¹ by norm_num,")
    L.append("      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_inv]")
    L.append("    push_cast; ring")
    L.append(f"  have hT := {halfname}")
    L.append(f"  have h := ArgGammaR.log_one_sub_mem (x := {xs}) (by norm_num) (by norm_num) {n}")
    L.append("  norm_num [Finset.sum_range_succ] at h")
    L.append("  rw [hs]")
    L.append("  constructor <;> linarith [h.1, h.2, hT.1, hT.2]")
    return L, LO, HI


def atan_small_bounds(u, N):
    """atanPS u N and the remainder u^(2N+1)/(2N+1)."""
    ps = sum(F((-1) ** j) * u ** (2 * j + 1) / (2 * j + 1) for j in range(N))
    rem = u ** (2 * N + 1) / (2 * N + 1)
    return ps - rem, ps + rem


def emit_atan(name, yexpr, y, D):
    """Bounds on `Real.arctan yexpr` for rational y > 0."""
    L = []
    if y >= 1:
        if y == 1:
            lo, hi = PI_LO / 4, PI_HI / 4
            LO, HI = rdown(lo, D), rup(hi, D)
            L.append(f"theorem {name} : {lit(LO)} ≤ Real.arctan ({yexpr}) ∧ Real.arctan ({yexpr}) ≤ {lit(HI)} := by")
            L.append(f"  rw [show ({yexpr} : ℝ) = 1 by norm_num, Real.arctan_one]")
            L.append("  have hpl := Real.pi_gt_d20")
            L.append("  have hph := Real.pi_lt_d20")
            L.append("  constructor <;> linarith")
            return L, LO, HI
        u = 1 / y
        lo = PI_LO / 2 - u
        hi = PI_HI / 2 - u + u ** 3 / 3
        LO, HI = rdown(lo, D), rup(hi, D)
        L.append(f"theorem {name} : {lit(LO)} ≤ Real.arctan ({yexpr}) ∧ Real.arctan ({yexpr}) ≤ {lit(HI)} := by")
        L.append(f"  have h := ArgGammaR.arctan_mem_large (y := ({yexpr} : ℝ)) (pl := {lit(PI_LO)})")
        L.append(f"    (ph := {lit(PI_HI)}) (by norm_num) (by linarith [Real.pi_gt_d20])")
        L.append("    (by linarith [Real.pi_lt_d20])")
        L.append("  norm_num at h")
        L.append("  constructor <;> linarith [h.1, h.2]")
        return L, LO, HI
    N = 1
    while y ** (2 * N + 1) / (2 * N + 1) > F(1, 10**12):
        N += 1
    lo, hi = atan_small_bounds(y, N)
    LO, HI = rdown(lo, D), rup(hi, D)
    L.append(f"theorem {name} : {lit(LO)} ≤ Real.arctan ({yexpr}) ∧ Real.arctan ({yexpr}) ≤ {lit(HI)} := by")
    L.append(f"  have h := ArctanTaylor.arctan_bracket ({yexpr}) (by norm_num) {N}")
    L.append("  rw [abs_le] at h")
    L.append("  norm_num [ArctanTaylor.atanPS, Finset.sum_range_succ] at h")
    L.append("  constructor <;> linarith [h.1, h.2]")
    return L, LO, HI


def main():
    if len(sys.argv) != 6:
        print(__doc__)
        sys.exit(2)
    glue, zzl, out, modname, H = sys.argv[1:]
    src = Path(glue).read_text()
    glue_mod = Path(glue).stem
    rows = re.findall(r"\| (\d+) => ⟨(.*?),\n\s+(RHInBoxT_\S+?)\.cPB, \S+\.RPB, \S+\.hs1PB⟩", src)
    bands = []
    for idx, body, mod in rows:
        toks = split_top(body)
        assert len(toks) == 13, (idx, toks)
        T0, T1 = parse_frac(toks[0]), parse_frac(toks[1])
        n = int(toks[2])
        Ls = [parse_frac(t) for t in toks[3:13]]
        msrc = (Path(zzl) / f"{mod}.lean").read_text()
        mc = re.search(r"def cPB : ℂ := ⟨(.*?)⟩", msrc).group(1)
        cre, cim = [parse_frac(t) for t in split_top(mc)]
        q = parse_frac(re.search(r"def RPB : ℝ := Real.sqrt (.*)", msrc).group(1))
        bands.append(dict(i=int(idx), T0=T0, T1=T1, n=n, L=Ls, mod=mod, cre=cre, cim=cim, q=q,
                          toks=toks))
    bands.sort(key=lambda b: b['i'])
    count = len(bands)
    heights = sorted({b['T0'] for b in bands} | {b['T1'] for b in bands})
    D = 10**15
    out_lines = []
    P = out_lines.append
    P(f"/-  {modname}.lean -- bricks K6a + K6b instantiated on a REAL ladder segment: `{glue_mod}`")
    P(f"    ({count} Turing bands up to height {H}).")
    P("    GENERATED by telperion/examples/zeta_reflection/emit_argchange_segment.py; DO NOT EDIT BY HAND.")
    P("")
    P("    For every band of the segment, `segK i` is the band re-parametrised for the K6 bricks:")
    P("      * `[L1, H1] = [-249/250, 249/250]`: K6a (`ArgZetaTwo.hAV2_generic`), the same for every band;")
    P("      * `[L4, H4]`, `[L5, H5]`: rational enclosures of the K6b closed-form Gamma_R brackets")
    P("        (`ArgGammaR.hAG1_closed`, `hAG2_closed`), from the height boxes below;")
    P("      * `L2 H2 L3 H3`: the band's two horizontal (Arb) enclosures, UNCHANGED.")
    P("    The kernel checks each band's side conditions (`segK_valid_i`: pins, ball, strip; `segK_side_i`:")
    P("    the K6 comparisons) and composes:")
    P("      * `bandHyp_of_K6`: the segment's `BandHyp` from `ArgChangeGlue.K6Inputs` per band -- the")
    P("        on-line zeros, the two zero-free edge slabs (K1), and the two horizontal enclosures;")
    P(f"      * `all_nontrivial_zeros_up_to_height_{H}_of_K6`: the height-{H} statement from the same")
    P("        inputs, with the height floor `hγ` discharged by `HeightFloor.height_floor`.")
    P("    Of the nine `hArbT` conjuncts per band, four are gone (`hnzl` by K1, `hAV2` by K6a, `hAG1`")
    P("    and `hAG2` by K6b); `hnzb`/`hnzt`/`hins` are the two slabs (K1); `hAHt`/`hAHb` remain (K6c,")
    P("    `ArgHoriz`, reduces them to octant certificates plus endpoint enclosures).")
    P("")
    P("    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,")
    P("    Quot.sound].  No `sorry`.  conjecture1_proved = False. -/")
    P("import Mathlib")
    P(f"import {glue_mod}")
    P("import ArgChangeGlue")
    P("import HeightFloor")
    P("")
    P("open Complex BandGlue BandGlue.BandData")
    P("")
    P(f"namespace {modname}")
    P("")
    P("/-! ## Transcendental boxes at the edge heights -/")
    P("")
    boxes = {}
    for T in heights:
        tg = tag(T)
        T_ = tlit(T)
        v2 = 1 + T * T / 4
        vm = F(1, 4) + T * T / 4
        if T < 2:
            L, lv2lo, lv2hi = emit_log(f"log_v2_{tg}", f"1 + {T_} ^ 2 / 4", v2, D)
            out_lines.extend(L); P("")
            L, lvmlo, lvmhi = emit_log(f"log_vm_{tg}", f"1 / 4 + {T_} ^ 2 / 4", vm, D)
            out_lines.extend(L); P("")
        else:
            # one expensive log per height: log (T/2); the two edge logs differ from 2 log (T/2) by
            # log (1 + 4/T²) and log (1 + 1/T²), a few Taylor terms each
            L, lhlo, lhhi = emit_log(f"log_half_{tg}", f"{T_} / 2", T / 2, D)
            out_lines.extend(L); P("")
            L, lv2lo, lv2hi = emit_log_corr(f"log_v2_{tg}", f"1 + {T_} ^ 2 / 4", T_, F(4) / (T * T + 4),
                                            f"log_half_{tg}", lhlo, lhhi, D)
            out_lines.extend(L); P("")
            L, lvmlo, lvmhi = emit_log_corr(f"log_vm_{tg}", f"1 / 4 + {T_} ^ 2 / 4", T_, F(1) / (T * T + 1),
                                            f"log_half_{tg}", lhlo, lhhi, D)
            out_lines.extend(L); P("")
        L, a2lo, a2hi = emit_atan(f"atan_half_{tg}", f"{T_} / 2", T / 2, D)
        out_lines.extend(L); P("")
        L, a1lo, a1hi = emit_atan(f"atan_{tg}", f"{T_}", T, D)
        out_lines.extend(L); P("")
        # S2 and Sm1 from the helpers
        s2lo = F(1, 2) * a2lo + T / 4 * lv2lo - T / 2 - T / 2 * LOGPI_HI
        s2hi = F(1, 2) * a2hi + T / 4 * lv2hi - T / 2 - T / 2 * LOGPI_LO
        smlo = T / 4 * lvmlo + a1lo - T / 2 - T / 2 * LOGPI_HI
        smhi = T / 4 * lvmhi + a1hi - T / 2 - T / 2 * LOGPI_LO
        S2LO, S2HI = rdown(s2lo, D), rup(s2hi, D)
        SMLO, SMHI = rdown(smlo, D), rup(smhi, D)
        P(f"theorem S2_box_{tg} : {lit(S2LO)} ≤ ArgGammaR.S2 {T_} ∧ ArgGammaR.S2 {T_} ≤ {lit(S2HI)} := by")
        P(f"  have h := ArgGammaR.S2_mem_of (T := {T_}) (by norm_num) log_v2_{tg} atan_half_{tg}")
        P("    RSDesignTheta.logpi_box")
        P("  constructor <;> linarith [h.1, h.2]")
        P("")
        P(f"theorem Sm1_box_{tg} : {lit(SMLO)} ≤ ArgGammaR.Sm1 {T_} ∧ ArgGammaR.Sm1 {T_} ≤ {lit(SMHI)} := by")
        P(f"  have h := ArgGammaR.Sm1_mem_of (T := {T_}) (by norm_num) log_vm_{tg} atan_{tg}")
        P("    RSDesignTheta.logpi_box")
        P("  constructor <;> linarith [h.1, h.2]")
        P("")
        boxes[T] = dict(S2=(S2LO, S2HI), Sm1=(SMLO, SMHI))
    # band enclosures
    D6 = 10**6
    tabs = {k: [] for k in ('L4', 'H4', 'L5', 'H5')}
    for b in bands:
        T0, T1 = b['T0'], b['T1']
        e2 = lambda T: T / (2 * (4 + T * T))
        em1 = lambda T: T / (2 * (1 + T * T))
        L5 = rdown(boxes[T1]['S2'][0] - boxes[T0]['S2'][1] - e2(T1), D6)
        H5 = rup(boxes[T1]['S2'][1] - boxes[T0]['S2'][0] + e2(T0), D6)
        L4 = rdown(boxes[T1]['Sm1'][0] - boxes[T0]['Sm1'][1] - em1(T1), D6)
        H4 = rup(boxes[T1]['Sm1'][1] - boxes[T0]['Sm1'][0] + em1(T0), D6)
        b.update(L4=L4, H4=H4, L5=L5, H5=H5, e2_0=e2(T0), e2_1=e2(T1), em1_0=em1(T0), em1_1=em1(T1))
        _, _, L2, H2, L3, H3, _, _, _, _ = b['L']
        n = b['n']
        pinL = 2 * F(31416, 10000) * (n - 1) < 2 * (-K6A) + L2 - H3 + L4 + L5
        pinH = 2 * K6A + H2 - L3 + H4 + H5 < 2 * F(314, 100) * (n + 1)
        assert pinL and pinH, ('pin fails', b['i'])
        # ball
        m, q = b['cim'], b['q']
        assert b['cre'] == F(1, 2)
        assert F(9, 4) + (T1 - m) ** 2 < q and F(9, 4) + (m - T0) ** 2 < q, ('ball', b['i'])
        for k in tabs:
            tabs[k].append(b[k])
    P("/-! ## The K6 re-parametrised band table -/")
    P("")
    for k in ('L4', 'H4', 'L5', 'H5'):
        P(f"/-- `{k}` of the re-parametrised bands (a rational enclosure of the K6b bracket). -/")
        P(f"noncomputable def {k}t : ℕ → ℝ := fun i => match i with")
        for b in bands:
            P(f"  | {b['i']} => {lit(b[k])}")
        P("  | _ => 0")
        P("")
    P("/-- Band `i` re-parametrised for K6: `[L1, H1] = [-249/250, 249/250]`, `[L4, H4]`, `[L5, H5]` from")
    P("    the K6b brackets, everything else (edges, count, horizontal enclosures, ball) from the Arb band. -/")
    P(f"noncomputable def segK (i : ℕ) : BandData :=")
    P(f"  ⟨({glue_mod}.seg i).T0, ({glue_mod}.seg i).T1, ({glue_mod}.seg i).n, -(249 / 250), 249 / 250,")
    P(f"    ({glue_mod}.seg i).L2, ({glue_mod}.seg i).H2, ({glue_mod}.seg i).L3, ({glue_mod}.seg i).H3,")
    P(f"    L4t i, H4t i, L5t i, H5t i, ({glue_mod}.seg i).c, ({glue_mod}.seg i).R, ({glue_mod}.seg i).hs1⟩")
    P("")
    P("/-! ## Per-band side conditions -/")
    P("")
    for b in bands:
        i = b['i']
        toks = b['toks']
        T0l, T1l = toks[0], toks[1]
        _, _, L2, H2, L3, H3, _, _, _, _ = b['L']
        t0, t1 = tag(b['T0']), tag(b['T1'])
        mod = b['mod']
        P(f"theorem segK_valid_{i} : (segK {i}).Valid (1 / 4000000) (3999999 / 4000000) where")
        P(f"  hT0 := show (0 : ℝ) < {T0l} by norm_num")
        P(f"  hT := show ({T0l} : ℝ) ≤ {T1l} by norm_num")
        P("  hs0 := by norm_num")
        P("  hs2 := by norm_num")
        P("  hre_lo := by norm_num")
        P("  hre_hi := by norm_num")
        P(f"  hRpos := {mod}.RPB_pos")
        P(f"  hN1 := show 1 ≤ {b['n']} by norm_num")
        P(f"  hbox_ball := ArgChangeGlue.ball_of_sq (T0 := {T0l}) (T1 := {T1l}) (m := {lit(b['cim'])})")
        P(f"    (q := {lit(b['q'])}) rfl rfl rfl (by norm_num) (by norm_num)")
        P(f"  hpinL := show 2 * 3.1416 * (({b['n']} : ℕ) - 1 : ℝ) < 2 * (-(249 / 250) : ℝ) + {toks[5]} - {toks[8]}")
        P(f"      + {lit(b['L4'])} + {lit(b['L5'])} by norm_num")
        P(f"  hpinH := show 2 * (249 / 250 : ℝ) + {toks[6]} - {toks[7]} + {lit(b['H4'])} + {lit(b['H5'])}")
        P(f"      < 2 * 3.14 * (({b['n']} : ℕ) + 1 : ℝ) by norm_num")
        P("")
        P(f"theorem segK_side_{i} : ArgChangeGlue.K6Side (segK {i}) where")
        P(f"  hT0 := show (0 : ℝ) ≤ {T0l} by norm_num")
        P(f"  hT1 := show (0 : ℝ) ≤ {T1l} by norm_num")
        P("  hL1 := show (-(249 / 250) : ℝ) ≤ -(249 / 250) from le_refl _")
        P("  hH1 := show (249 / 250 : ℝ) ≤ 249 / 250 from le_refl _")
        P(f"  hL4 := show {lit(b['L4'])} ≤ ArgGammaR.Sm1 {T1l} - ArgGammaR.Sm1 {T0l} - ArgGammaR.em1 {T1l} by")
        P(f"    have h1 := Sm1_box_{t1}; have h0 := Sm1_box_{t0}")
        P(f"    have he : ArgGammaR.em1 {T1l} = {lit(b['em1_1'])} := by unfold ArgGammaR.em1; norm_num")
        P("    rw [he]; linarith [h1.1, h1.2, h0.1, h0.2]")
        P(f"  hH4 := show ArgGammaR.Sm1 {T1l} - ArgGammaR.Sm1 {T0l} + ArgGammaR.em1 {T0l} ≤ {lit(b['H4'])} by")
        P(f"    have h1 := Sm1_box_{t1}; have h0 := Sm1_box_{t0}")
        P(f"    have he : ArgGammaR.em1 {T0l} = {lit(b['em1_0'])} := by unfold ArgGammaR.em1; norm_num")
        P("    rw [he]; linarith [h1.1, h1.2, h0.1, h0.2]")
        P(f"  hL5 := show {lit(b['L5'])} ≤ ArgGammaR.S2 {T1l} - ArgGammaR.S2 {T0l} - ArgGammaR.e2 {T1l} by")
        P(f"    have h1 := S2_box_{t1}; have h0 := S2_box_{t0}")
        P(f"    have he : ArgGammaR.e2 {T1l} = {lit(b['e2_1'])} := by unfold ArgGammaR.e2; norm_num")
        P("    rw [he]; linarith [h1.1, h1.2, h0.1, h0.2]")
        P(f"  hH5 := show ArgGammaR.S2 {T1l} - ArgGammaR.S2 {T0l} + ArgGammaR.e2 {T0l} ≤ {lit(b['H5'])} by")
        P(f"    have h1 := S2_box_{t1}; have h0 := S2_box_{t0}")
        P(f"    have he : ArgGammaR.e2 {T0l} = {lit(b['e2_0'])} := by unfold ArgGammaR.e2; norm_num")
        P("    rw [he]; linarith [h1.1, h1.2, h0.1, h0.2]")
        P("")
    P("/-! ## Composition -/")
    P("")
    P(f"theorem segK_edge : ∀ i, i < {count} → (segK i).T0 ≤ AllZeros_h{H}.bLo i ∧ AllZeros_h{H}.bHi i ≤ (segK i).T1 :=")
    P(f"  {glue_mod}.seg_edge")
    P("")
    P(f"theorem segK_geom : ∀ i, i < {count} → (segK i).CapGeom ({glue_mod}.capLo i) ({glue_mod}.capHi i) :=")
    P(f"  fun i hi => ArgChangeGlue.capGeom_transfer (d := {glue_mod}.seg i) rfl rfl rfl rfl")
    P(f"    ({glue_mod}.seg_geom i hi)")
    P("")
    P(f"theorem segK_stmt : ∀ i, i < {count} → (segK i).Stmt (1 / 4000000) (3999999 / 4000000) := by")
    P("  intro i hi")
    P("  interval_cases i")
    for b in bands:
        P(f"  · exact stmt_of_valid segK_valid_{b['i']}")
    P("")
    P(f"theorem segK_side : ∀ i, i < {count} → ArgChangeGlue.K6Side (segK i) := by")
    P("  intro i hi")
    P("  interval_cases i")
    for b in bands:
        P(f"  · exact segK_side_{b['i']}")
    P("")
    P(f"/-- **K0 + K1 + K6 on `AllZeros_h{H}`**: the segment's band hypothesis from the K6-reduced")
    P("    per-band inputs (on-line zeros, two zero-free edge slabs, the two horizontal enclosures). -/")
    P(f"theorem bandHyp_of_K6 (hin : ∀ i, i < {count} →")
    P(f"    ArgChangeGlue.K6Inputs ({glue_mod}.capLo i) ({glue_mod}.capHi i) (segK i)) :")
    P(f"    AllZeros_h{H}.BandHyp :=")
    P("  ArgChangeGlue.segBandHyp_of_K6 segK segK_edge segK_stmt segK_geom segK_side hin")
    P("")
    P(f"/-- **The height-{H} statement from the K6-reduced inputs alone** (the height floor `hγ` is")
    P("    discharged by `HeightFloor.height_floor`). -/")
    P(f"theorem all_nontrivial_zeros_up_to_height_{H}_of_K6 (hin : ∀ i, i < {count} →")
    P(f"    ArgChangeGlue.K6Inputs ({glue_mod}.capLo i) ({glue_mod}.capHi i) (segK i)) :")
    P(f"    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ {H} → ρ.re = 1 / 2 :=")
    P(f"  AllZeros_h{H}.all_nontrivial_zeros_up_to_height_{H}_of_bands (bandHyp_of_K6 hin)")
    P(f"    (HeightFloor.height_floor {H})")
    P("")
    P(f"/-- The K1-reduced inputs of the Arb bands (`{glue_mod}`) imply the K6-reduced inputs: K6 only")
    P("    DROPS conjuncts (the horizontal enclosures are the Arb band's own). -/")
    P(f"theorem k6Inputs_of_reduced (i : ℕ) (h : ({glue_mod}.seg i).ReducedInputs ({glue_mod}.capLo i)")
    P(f"    ({glue_mod}.capHi i)) : ArgChangeGlue.K6Inputs ({glue_mod}.capLo i) ({glue_mod}.capHi i) (segK i) :=")
    P("  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩")
    P("")
    P(f"end {modname}")
    Path(out).write_text("\n".join(out_lines) + "\n")
    print(f"wrote {out}: {count} bands, {len(heights)} heights")


if __name__ == '__main__':
    main()
