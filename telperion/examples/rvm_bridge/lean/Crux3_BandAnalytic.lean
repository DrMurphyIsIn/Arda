/-
  Crux3_BandAnalytic -- the frequency-side LOWER BOUND of the registry's Weil functional for a
  continuous (not necessarily smooth) even real test (rvm_bridge island, 2026-09-24, crux lane 3).

  conjecture1_proved = False.  Nothing here proves, reduces, or is equivalent to RH.  The statement
  is an inequality about the ARITHMETIC side of the explicit formula (archSide - primeSide) for one
  explicit class of test functions; no zeros are used or claimed.

  STATEMENT (`FreqData.weil_re_ge`).  Let `v : R -> R` be continuous, even, supported in `[-L, L]`,
  with transform decay `|h_v(r)| <= K/(1 + r^2)` (`FreqData v L K`), and let
  `g = acR v`, `g(y) = int v(x) v(x - y) dx`.  Then for every `N`,
      Re W(v * v~) >= (-gamma + H_N - log pi) g(0) - sum_{j <= N} int g(y) e^{-2 (j + 1/4)|y|} dy
                      - sum_{n < e^{2L}} [log n < 2L] 2 Lambda(n)/sqrt n g(log n),
  where `W = WeilForm.weilForm = archSide - primeSide` (ZhuSymbol's mirror of the registry vocabulary).

  ROUTE (the smooth-test proof of ZhuSymbol, re-done for continuous tests):
    * the two pole terms equal `|F(i/2)|^2 >= 0` (Zeta23's `EF.paperFT_weilTest`, which needs only
      continuity and compact support) and are DROPPED;
    * on the line `h_{v*v~}(r) = |h_v(r)|^2 =: Fsq r`; `Fsq` is integrable by the decay hypothesis,
      `Fsq * psiR` by Zeta23's digamma growth in the strip;
    * the digamma floor `psiR r >= -gamma + H_N - sum_{j<=N} lz(j + 1/4, r)` (RvMBridge30's
      series bound with `M = 0`: the tail of the vertical-line series is `>= 0` and is dropped);
    * the LORENTZIAN PARSEVAL identity `int Fsq(r) lz(b, r) dr = 2 pi int g(y) e^{-2b|y|} dy`
      (`integral_mul_lz`): `lz(b, .)` is the cosine transform of `e^{-2b|y|}`
      (`integral_exp_abs_mul_cos`, from Mathlib's `integral_exp_mul_complex_Ioi`), then Fubini and
      Zeta23's cosine-form Fourier inversion `Taper.integral_mul_cos_of_paperFT_eq`;
    * Plancherel `int Fsq = 2 pi g(0)` is the same inversion at `0`;
    * the prime side is the finite sum over `n < e^{2L}` (support of `g` in `[-2L, 2L]`).
  No `sorry`.
-/
import ZhuSymbol
import E6Bridge30
import Zeta23.Taper.Decay

open MeasureTheory Complex Zeta23 Set Filter
open scoped ComplexConjugate

noncomputable section

namespace Crux3




/-- The Lorentzian `b / (b^2 + (r/2)^2)` of the vertical-line digamma series. -/
def lz (b r : ℝ) : ℝ := b / (b ^ 2 + (r / 2) ^ 2)

lemma integral_Ioi_exp_mul_cos {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-2 * b * t) * Real.cos (r * t) = 2 * b / (4 * b ^ 2 + r ^ 2) := by
  have ha : ((-2 * b : ℝ) + r * I : ℂ).re < 0 := by simp; linarith
  have h := integral_exp_mul_complex_Ioi ha 0
  have hint := integrableOn_exp_mul_complex_Ioi ha 0
  have e1 : ∀ t : ℝ, Real.exp (-2 * b * t) * Real.cos (r * t)
      = (Complex.exp ((((-2 * b : ℝ) : ℂ) + r * I) * t)).re := by
    intro t
    rw [Complex.exp_re]
    congr 2 <;> simp
  simp_rw [e1]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre, h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hden : (4 * b ^ 2 + r ^ 2) ≠ 0 := by positivity
  have hz : ((-2 * b : ℝ) : ℂ) + r * I ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp
  ring

/-- The Lorentzian is the cosine transform of `e^{-2b|y|}`. -/
theorem integral_exp_abs_mul_cos {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ∫ y : ℝ, Real.exp (-2 * b * |y|) * Real.cos (r * y) = lz b r := by
  have h := integral_comp_abs (f := fun t => Real.exp (-2 * b * t) * Real.cos (r * t))
  have e : (fun y : ℝ => Real.exp (-2 * b * |y|) * Real.cos (r * y))
      = fun y => Real.exp (-2 * b * |y|) * Real.cos (r * |y|) := by
    funext y
    rcases abs_choice y with hy | hy <;> rw [hy]
    simp [Real.cos_neg]
  rw [e, h, integral_Ioi_exp_mul_cos hb]
  unfold lz
  have hden : (4 * b ^ 2 + r ^ 2) ≠ 0 := by positivity
  have hden2 : (b ^ 2 + (r / 2) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

lemma integrable_exp_abs {b : ℝ} (hb : 0 < b) : Integrable (fun y : ℝ => Real.exp (-2 * b * |y|)) := by
  have h1 : IntegrableOn (fun y : ℝ => Real.exp (-2 * b * y)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h2 : IntegrableOn (fun y : ℝ => Real.exp ((2 * b) * y)) (Iic 0) :=
    integrableOn_exp_mul_Iic (by linarith) 0
  have hI : IntegrableOn (fun y : ℝ => Real.exp (-2 * b * |y|)) (Ioi 0) := by
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [abs_of_pos (show (0:ℝ) < y from hy)]
  have hJ : IntegrableOn (fun y : ℝ => Real.exp (-2 * b * |y|)) (Iic 0) := by
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Iic
    simp only [mem_Iic] at hy
    rw [abs_of_nonpos hy]
    ring_nf
  have := hJ.union hI
  rw [Iic_union_Ioi] at this
  exact integrableOn_univ.mp this

/-- **Lorentzian Parseval**: if `A` is continuous, integrable and real with real integrable
transform `F` (`h_A = F` on the line), then `∫ F(r) lz b r dr = 2π ∫ A(y) e^{-2b|y|} dy`. -/
theorem integral_mul_lz {A F : ℝ → ℝ} (hA : Continuous A) (hAi : Integrable A) (hF : Integrable F)
    (hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (F r : ℂ)) {b : ℝ} (hb : 0 < b) :
    ∫ r, F r * lz b r = 2 * Real.pi * ∫ y, A y * Real.exp (-2 * b * |y|) := by
  have hcos := Taper.integral_mul_cos_of_paperFT_eq hA hAi hF hFT
  have e1 : (fun r => F r * lz b r)
      = fun r => ∫ y, F r * (Real.exp (-2 * b * |y|) * Real.cos (r * y)) := by
    funext r
    rw [integral_const_mul, integral_exp_abs_mul_cos hb]
  have hE := integrable_exp_abs hb
  have hprod : Integrable (Function.uncurry fun r y => F r * (Real.exp (-2 * b * |y|) * Real.cos (r * y)))
      (volume.prod volume) := by
    have hm := hF.norm.mul_prod hE
    refine hm.mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine (hF.aestronglyMeasurable.comp_fst).mul ?_
      exact (Continuous.aestronglyMeasurable (by fun_prop))
    · show ‖F z.1 * (Real.exp (-2 * b * |z.2|) * Real.cos (z.1 * z.2))‖ ≤ ‖F z.1‖ * Real.exp (-2 * b * |z.2|)
      simp only [norm_mul, Real.norm_eq_abs]
      rw [abs_of_pos (Real.exp_pos _)]
      have := Real.abs_cos_le_one (z.1 * z.2)
      have h0 : 0 ≤ |F z.1| * Real.exp (-2 * b * |z.2|) := by positivity
      calc |F z.1| * (Real.exp (-2 * b * |z.2|) * |Real.cos (z.1 * z.2)|)
          = |F z.1| * Real.exp (-2 * b * |z.2|) * |Real.cos (z.1 * z.2)| := by ring
        _ ≤ |F z.1| * Real.exp (-2 * b * |z.2|) * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
  rw [e1, integral_integral_swap hprod]
  have e2 : ∀ y : ℝ, ∫ r, F r * (Real.exp (-2 * b * |y|) * Real.cos (r * y))
      = Real.exp (-2 * b * |y|) * (2 * Real.pi * A y) := by
    intro y
    rw [← hcos y, ← integral_const_mul]
    congr 1
    funext r
    ring
  simp_rw [e2]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring




/-- The digamma floor in Lorentzian form (the series tail, which is `>= 0`, is dropped):
`psiR r >= -gamma + H_N - sum_{j <= N} lz (j + 1/4) r`. -/
theorem psiR_ge_lz (r : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
      - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r ≤ RvMBridge11.psiR r := by
  have h := RvMBridge30.psiR_ge_series r N 0
  have e1 : RvMBridge30.serG (r / 2) (N : ℝ) - RvMBridge30.serG (r / 2) ((N : ℝ) + ((0 : ℕ) : ℝ)) = 0 := by
    simp
  have e2 : ∑ n ∈ Finset.range N, RvMBridge30.serF (r / 2) n
      = ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)
        - ∑ n ∈ Finset.range N, lz ((n : ℝ) + 1 + 1 / 4) r := by
    rw [← Finset.sum_sub_distrib]
    rfl
  have e3 : ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r
      = ∑ n ∈ Finset.range N, lz ((n : ℝ) + 1 + 1 / 4) r + lz (0 + 1 / 4) r := by
    rw [Finset.sum_range_succ']
    push_cast
    simp only [zero_add]
  have e4 : lz (0 + 1 / 4) r = (1 / 4) / ((1 / 4) ^ 2 + (r / 2) ^ 2) := by
    unfold lz; norm_num
  rw [e1, e2] at h
  rw [e3, e4]
  linarith


open WeilExplicit RvMBridge4 RvMBridge5 RvMBridgeZhu

/-- The real autocorrelation `∫ v x v(x - y) dx`. -/
def acR (v : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x, v x * v (x - y)

lemma lz_nonneg {b : ℝ} (hb : 0 ≤ b) (r : ℝ) : 0 ≤ lz b r := by
  unfold lz; positivity

lemma lz_le {b : ℝ} (hb : 0 < b) (r : ℝ) : lz b r ≤ 1 / b := by
  unfold lz
  rw [div_le_div_iff₀ (by positivity) hb]
  nlinarith [sq_nonneg (r / 2)]

lemma continuous_lz (b : ℝ) (hb : 0 < b) : Continuous (lz b) := by
  unfold lz
  refine continuous_const.div (by fun_prop) (fun r => by positivity)

/-- The `j`-th Lorentzian term of the archimedean floor, in physical space:
`int g(y) e^{-2 (j + 1/4) |y|} dy` with `g = acR v`. -/
def lorTerm (v : ℝ → ℝ) (j : ℕ) : ℝ := ∫ y, acR v y * Real.exp (-2 * ((j : ℝ) + 1 / 4) * |y|)

/-- Every ingredient of the frequency side of a continuous even real compactly supported test
with `C/(1+r^2)` transform decay. -/
structure FreqData (v : ℝ → ℝ) (L K : ℝ) : Prop where
  cont : Continuous v
  even : ∀ u, v (-u) = v u
  supp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L
  K0 : 0 ≤ K
  decay : ∀ r : ℝ, ‖paperFT (fun u => (v u : ℂ)) r‖ ≤ K / (1 + r ^ 2)

section
variable {v : ℝ → ℝ} {L K : ℝ} (hv : FreqData v L K)
include hv

lemma FreqData.hcs : HasCompactSupport (fun u => (v u : ℂ)) :=
  (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hv.supp

lemma FreqData.hcont : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hv.cont

lemma FreqData.hcsR : HasCompactSupport v := by
  have h := hv.hcs
  rw [HasCompactSupport] at h ⊢
  have e : tsupport v = tsupport (fun u => (v u : ℂ)) := by
    unfold tsupport
    congr 1
    ext u
    simp [Function.mem_support]
  rwa [e]

/-- The squared transform on the line. -/
def Fsq (v : ℝ → ℝ) (r : ℝ) : ℝ := ‖paperFT (fun u => (v u : ℂ)) r‖ ^ 2

omit hv in
lemma Fsq_nonneg (v : ℝ → ℝ) (r : ℝ) : 0 ≤ Fsq v r := by unfold Fsq; positivity

lemma FreqData.line (r : ℝ) :
    paperFT (WeilExplicit.autocorr (fun u => (v u : ℂ))) r = (Fsq v r : ℂ) := by
  rw [autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs, Complex.conj_ofReal,
    Complex.mul_conj']
  unfold Fsq
  push_cast
  ring

lemma FreqData.Fsq_le_sq (r : ℝ) : Fsq v r ≤ K ^ 2 / (1 + r ^ 2) ^ 2 := by
  unfold Fsq
  have h1 := hv.decay r
  have h0 : 0 ≤ ‖paperFT (fun u => (v u : ℂ)) r‖ := norm_nonneg _
  have h2 : ‖paperFT (fun u => (v u : ℂ)) r‖ ^ 2 ≤ (K / (1 + r ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  rwa [div_pow] at h2

lemma FreqData.Fsq_le (r : ℝ) : Fsq v r ≤ K ^ 2 / (1 + r ^ 2) := by
  unfold Fsq
  have h1 := hv.decay r
  have h0 : 0 ≤ ‖paperFT (fun u => (v u : ℂ)) r‖ := norm_nonneg _
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h2 : ‖paperFT (fun u => (v u : ℂ)) r‖ ^ 2 ≤ (K / (1 + r ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (K / (1 + r ^ 2)) ^ 2 ≤ K ^ 2 / (1 + r ^ 2) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hpos]
    have : (1 + r ^ 2) ≤ (1 + r ^ 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg K]
  linarith

lemma FreqData.continuous_Fsq : Continuous (Fsq v) := by
  have h := Taper.continuous_paperFT_ofReal (hv.hcont.integrable_of_hasCompactSupport hv.hcs)
  unfold Fsq
  exact h.norm.pow 2

lemma FreqData.integrable_Fsq : Integrable (Fsq v) := by
  have hmaj : Integrable (fun r : ℝ => K ^ 2 * (1 + r ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  refine hmaj.mono' hv.continuous_Fsq.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Fsq_nonneg v r)]
  have := hv.Fsq_le r
  rwa [div_eq_mul_inv] at this

omit hv in
lemma FreqData.acR_eq : WeilExplicit.autocorr (fun u => (v u : ℂ)) = fun y => (acR v y : ℂ) := by
  rw [autocorr_ofReal_eq]
  rfl

lemma FreqData.continuous_acR : Continuous (acR v) := by
  have h := Taper.autocorr_continuous_of_even hv.even hv.cont hv.hcsR
  have e : acR v = fun y => Params.autocorr v (-y) := by
    funext y
    unfold acR Params.autocorr
    simp [sub_eq_add_neg]
  rw [e]
  exact h.comp continuous_neg

lemma FreqData.acR_eq_zero {y : ℝ} (hy : 2 * L ≤ |y|) : acR v y = 0 := by
  have h := autocorr_eq_zero_of_two_mul_le hv.supp hy
  rw [FreqData.acR_eq (v := v)] at h
  simp only at h
  exact_mod_cast h

lemma FreqData.acR_neg (y : ℝ) : acR v (-y) = acR v y := by
  have hev' : ∀ u, v (-u) = 1 * v u := fun u => by rw [one_mul]; exact hv.even u
  have h := autocorr_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev' y
  rw [FreqData.acR_eq (v := v)] at h
  simp only at h
  exact_mod_cast h

lemma FreqData.integrable_acR : Integrable (acR v) := by
  refine hv.continuous_acR.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * L)) (b := 2 * L)) (fun y hy => ?_)
  apply hv.acR_eq_zero
  simp only [mem_Icc, not_and_or, not_le] at hy
  rcases hy with h | h
  · exact le_trans (by linarith) (neg_le_abs y)
  · linarith [le_abs_self y]

lemma FreqData.hFT (r : ℝ) : paperFT (fun u => (acR v u : ℂ)) r = (Fsq v r : ℂ) := by
  rw [← FreqData.acR_eq (v := v)]
  exact hv.line r

/-- Plancherel through inversion at 0: `∫ Fsq = 2π acR v 0`. -/
lemma FreqData.integral_Fsq : ∫ r, Fsq v r = 2 * Real.pi * acR v 0 := by
  have h := Taper.integral_mul_cos_of_paperFT_eq hv.continuous_acR hv.integrable_acR hv.integrable_Fsq
    hv.hFT 0
  simpa using h


omit hv in
/-- `psiR` grows at most linearly (Zeta23's digamma growth in the strip `1/4 <= Re s <= 1`). -/
lemma psiR_growth : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, |RvMBridge11.psiR r| ≤ C * (1 + |r| / 2) := by
  obtain ⟨C, hC0, hC⟩ := Zeta23.WeilEF.digamma_growth_strip
  refine ⟨C, hC0, fun r => ?_⟩
  have hre : (1 / 4 + ((r : ℂ) / 2) * I).re = 1 / 4 := by simp
  have him : (1 / 4 + ((r : ℂ) / 2) * I).im = r / 2 := by simp
  have hs := hC (1 / 4 + ((r : ℂ) / 2) * I) (by rw [hre]) (by rw [hre]; norm_num)
  rw [him] at hs
  have hlog : Real.log (2 + |r / 2|) ≤ 1 + |r| / 2 := by
    rw [abs_div, abs_two]
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 + |r| / 2)
    linarith
  calc |RvMBridge11.psiR r| ≤ ‖Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.log (2 + |r / 2|) := hs
    _ ≤ C * (1 + |r| / 2) := mul_le_mul_of_nonneg_left hlog hC0.le

lemma FreqData.integrable_Fsq_psiR : Integrable (fun r => Fsq v r * RvMBridge11.psiR r) := by
  obtain ⟨C, hC0, hC⟩ := psiR_growth
  have hmaj : Integrable (fun r : ℝ => (K ^ 2 * C * (17 / 16)) * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hpsi : Continuous RvMBridge11.psiR := RvMBridge11.continuous_psiR
  refine hmaj.mono' (hv.continuous_Fsq.mul hpsi).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Fsq_nonneg v r)]
  have h1 := hv.Fsq_le_sq r
  have h2 := hC r
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have h3 : 1 + |r| / 2 ≤ (17 / 16) * (1 + r ^ 2) := by
    have := sq_nonneg (|r| - 1 / 4)
    rw [sub_sq, sq_abs] at this
    nlinarith [abs_nonneg r]
  have hF0 := Fsq_nonneg v r
  calc Fsq v r * |RvMBridge11.psiR r| ≤ (K ^ 2 / (1 + r ^ 2) ^ 2) * (C * ((17 / 16) * (1 + r ^ 2))) := by
        apply mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hC0.le)) (abs_nonneg _)
        positivity
    _ = (K ^ 2 * C * (17 / 16)) * (1 + r ^ 2)⁻¹ := by
        field_simp

lemma FreqData.integrable_Fsq_lz {b : ℝ} (hb : 0 < b) : Integrable (fun r => Fsq v r * lz b r) := by
  refine (hv.integrable_Fsq.mul_const (1 / b)).mono' (hv.continuous_Fsq.mul (continuous_lz b hb)).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Fsq_nonneg v r), abs_of_nonneg (lz_nonneg hb.le r)]
  exact mul_le_mul_of_nonneg_left (lz_le hb r) (Fsq_nonneg v r)

/-- **The frequency-side lower bound** for a continuous even real test with `C/(1+r^2)`
transform decay supported in `[-L, L]`: with the pole terms (`= 2 F(i/2)^2 >= 0`) dropped and the
digamma series tail (`>= 0`) dropped after `N` terms,
`Re W(v * v~) >= (-gamma + H_N - log pi) g(0) - sum_{j <= N} int g(y) e^{-2 (j + 1/4)|y|} dy
   - sum_{n < e^{2L}} 2 Lambda(n)/sqrt n g(log n)`,  `g = acR v` the real autocorrelation. -/
theorem FreqData.weil_re_ge (N : ℕ) :
    (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) - Real.log Real.pi)
        * acR v 0
      - ∑ j ∈ Finset.range (N + 1), lorTerm v j
      - ∑ n ∈ Finset.range (⌈Real.exp (2 * L)⌉₊ + 1),
          (if Real.log n < 2 * L then
            2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR v (Real.log n) else 0)
    ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  /- pole terms -/
  have hcI : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hcI' : (starRingEnd ℂ) (-Complex.I / 2) = Complex.I / 2 := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hev1 : ∀ u, v (-u) = 1 * v u := fun u => by rw [one_mul]; exact hv.even u
  have hpole0 : weilKernel g 0 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_zero, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI, hfC, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, map_mul, Complex.conj_ofReal,
      mul_left_comm, Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hpole1 : weilKernel g 1 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_one, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI', hfC, neg_div, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, mul_assoc,
      Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hg0 : g 0 = (acR v 0 : ℂ) := by rw [hgA]
  /- the archimedean integrand -/
  have harch_pt : ∀ r : ℝ, archIntegrand g r = ((Fsq v r * RvMBridge11.psiR r : ℝ) : ℂ) := by
    intro r
    unfold archIntegrand
    rw [weilKernel_line, hgdef, hv.line r]
    unfold RvMBridge11.psiR
    push_cast
    ring
  have harch : ∫ r : ℝ, archIntegrand g r = ((∫ r, Fsq v r * RvMBridge11.psiR r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    exact harch_pt r
  /- the prime side is a finite sum -/
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  set term : ℕ → ℝ := fun n => if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR v (Real.log n) else 0 with hterm
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hprime_pt : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))
        = (term n : ℂ) := by
    intro n
    rw [hterm]
    simp only
    split_ifs with hn
    · rw [hgA]
      simp only
      rw [hv.acR_neg]
      push_cast
      ring
    · have h1 : acR v (Real.log n) = 0 := hv.acR_eq_zero ((not_lt.mp hn).trans (le_abs_self _))
      have h2 : acR v (-Real.log n) = 0 :=
        hv.acR_eq_zero (by rw [abs_neg]; exact (not_lt.mp hn).trans (le_abs_self _))
      rw [hgA]
      simp only
      rw [h1, h2]
      simp
  have hprime : primeSide g = ((∑ n ∈ Finset.range N0, term n : ℝ) : ℂ) := by
    unfold primeSide
    have hvan : ∀ n ∉ Finset.range N0, term n = 0 := fun n hn => by
      rw [hterm]; simp only; rw [if_neg (hbig n hn)]
    rw [tsum_congr hprime_pt, ← Complex.ofReal_tsum, tsum_eq_sum (s := Finset.range N0) hvan]
  /- the archimedean lower bound -/
  set c : ℝ := -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) with hc
  have hbpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 / 4 := fun j => by positivity
  have hIlz : ∀ j ∈ Finset.range (N + 1), Integrable (fun r => Fsq v r * lz ((j : ℝ) + 1 / 4) r) :=
    fun j _ => hv.integrable_Fsq_lz (hbpos j)
  have hImin : Integrable (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)) := by
    have e : (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
        = fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + 1 / 4) r := by
      funext r
      rw [mul_sub, Finset.mul_sum]
    rw [e]
    exact (hv.integrable_Fsq.mul_const c).sub (integrable_finsetSum _ hIlz)
  have hmin : ∀ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)
      ≤ Fsq v r * RvMBridge11.psiR r := fun r =>
    mul_le_mul_of_nonneg_left (psiR_ge_lz r N) (Fsq_nonneg v r)
  have hmono := integral_mono hImin hv.integrable_Fsq_psiR hmin
  have hsplit : ∫ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)
      = c * (2 * Real.pi * acR v 0)
        - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTerm v j := by
    have e : (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
        = fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + 1 / 4) r := by
      funext r
      rw [mul_sub, Finset.mul_sum]
    rw [e, integral_sub (hv.integrable_Fsq.mul_const c) (integrable_finsetSum _ hIlz),
      integral_finsetSum _ hIlz, integral_mul_const, hv.integral_Fsq]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold lorTerm
      exact integral_mul_lz hv.continuous_acR hv.integrable_acR hv.integrable_Fsq hv.hFT (hbpos j)
  /- assembly -/
  have hcomplex : archSide g - primeSide g
      = ((2 * ‖weilKernel fC 0‖ ^ 2 - acR v 0 * Real.log Real.pi
          + (1 / (2 * Real.pi)) * (∫ r, Fsq v r * RvMBridge11.psiR r)
          - ∑ n ∈ Finset.range N0, term n : ℝ) : ℂ) := by
    unfold archSide
    rw [hpole0, hpole1, hg0, harch, hprime]
    push_cast
    ring
  rw [weilForm_autocorr_eq, WeilExplicit.weilForm, ← hgdef, hcomplex, Complex.ofReal_re]
  have hpos2 : (0 : ℝ) ≤ 2 * ‖weilKernel fC 0‖ ^ 2 := by positivity
  have hk : (1 / (2 * Real.pi)) * (c * (2 * Real.pi * acR v 0)
        - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTerm v j)
      = c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTerm v j := by
    rw [← Finset.mul_sum]
    generalize (∑ j ∈ Finset.range (N + 1), lorTerm v j) = S
    field_simp
  have hmono' : (1 / (2 * Real.pi)) * (∫ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
      ≤ (1 / (2 * Real.pi)) * (∫ r, Fsq v r * RvMBridge11.psiR r) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  rw [hsplit, hk] at hmono'
  have hN0' : ∑ n ∈ Finset.range (⌈Real.exp (2 * L)⌉₊ + 1),
      (if Real.log n < 2 * L then 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR v (Real.log n) else 0)
      = ∑ n ∈ Finset.range N0, term n := rfl
  rw [hN0']
  have hlin : (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) - Real.log Real.pi)
      * acR v 0 = c * acR v 0 - acR v 0 * Real.log Real.pi := by rw [hc]; ring
  rw [hlin]
  linarith [hmono', hpos2]

/-- **The archimedean half alone**: `Re archSide(v * v~) >= (-gamma + H_N - log pi) g(0) - sum_{j<=N}
lorTerm v j` (pole terms `>= 0` dropped, digamma series tail `>= 0` dropped). -/
theorem FreqData.arch_re_ge (N : ℕ) :
    (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) - Real.log Real.pi)
        * acR v 0
      - ∑ j ∈ Finset.range (N + 1), lorTerm v j
    ≤ (WeilExplicit.archSide (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  /- pole terms -/
  have hcI : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hcI' : (starRingEnd ℂ) (-Complex.I / 2) = Complex.I / 2 := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hev1 : ∀ u, v (-u) = 1 * v u := fun u => by rw [one_mul]; exact hv.even u
  have hpole0 : weilKernel g 0 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_zero, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI, hfC, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, map_mul, Complex.conj_ofReal,
      mul_left_comm, Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hpole1 : weilKernel g 1 = ((1 * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_one, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hv.hcont hv.hcont hv.hcs hv.hcs,
      hcI', hfC, neg_div, paperFT_neg_of_parity (by norm_num : (1 : ℝ) * 1 = 1) hev1, mul_assoc,
      Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hg0 : g 0 = (acR v 0 : ℂ) := by rw [hgA]
  /- the archimedean integrand -/
  have harch_pt : ∀ r : ℝ, archIntegrand g r = ((Fsq v r * RvMBridge11.psiR r : ℝ) : ℂ) := by
    intro r
    unfold archIntegrand
    rw [weilKernel_line, hgdef, hv.line r]
    unfold RvMBridge11.psiR
    push_cast
    ring
  have harch : ∫ r : ℝ, archIntegrand g r = ((∫ r, Fsq v r * RvMBridge11.psiR r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    exact harch_pt r
  /- the archimedean lower bound -/
  set c : ℝ := -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) with hc
  have hbpos : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 / 4 := fun j => by positivity
  have hIlz : ∀ j ∈ Finset.range (N + 1), Integrable (fun r => Fsq v r * lz ((j : ℝ) + 1 / 4) r) :=
    fun j _ => hv.integrable_Fsq_lz (hbpos j)
  have hImin : Integrable (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)) := by
    have e : (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
        = fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + 1 / 4) r := by
      funext r
      rw [mul_sub, Finset.mul_sum]
    rw [e]
    exact (hv.integrable_Fsq.mul_const c).sub (integrable_finsetSum _ hIlz)
  have hmin : ∀ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)
      ≤ Fsq v r * RvMBridge11.psiR r := fun r =>
    mul_le_mul_of_nonneg_left (psiR_ge_lz r N) (Fsq_nonneg v r)
  have hmono := integral_mono hImin hv.integrable_Fsq_psiR hmin
  have hsplit : ∫ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r)
      = c * (2 * Real.pi * acR v 0)
        - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTerm v j := by
    have e : (fun r => Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
        = fun r => Fsq v r * c - ∑ j ∈ Finset.range (N + 1), Fsq v r * lz ((j : ℝ) + 1 / 4) r := by
      funext r
      rw [mul_sub, Finset.mul_sum]
    rw [e, integral_sub (hv.integrable_Fsq.mul_const c) (integrable_finsetSum _ hIlz),
      integral_finsetSum _ hIlz, integral_mul_const, hv.integral_Fsq]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      unfold lorTerm
      exact integral_mul_lz hv.continuous_acR hv.integrable_acR hv.integrable_Fsq hv.hFT (hbpos j)
  /- assembly -/
  have hcomplex : archSide g
      = ((2 * ‖weilKernel fC 0‖ ^ 2 - acR v 0 * Real.log Real.pi
          + (1 / (2 * Real.pi)) * (∫ r, Fsq v r * RvMBridge11.psiR r) : ℝ) : ℂ) := by
    unfold archSide
    rw [hpole0, hpole1, hg0, harch]
    push_cast
    ring
  rw [show WeilForm.autocorr (fun u => (v u : ℂ)) = g from rfl, hcomplex, Complex.ofReal_re]
  have hpos2 : (0 : ℝ) ≤ 2 * ‖weilKernel fC 0‖ ^ 2 := by positivity
  have hk : (1 / (2 * Real.pi)) * (c * (2 * Real.pi * acR v 0)
        - ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * lorTerm v j)
      = c * acR v 0 - ∑ j ∈ Finset.range (N + 1), lorTerm v j := by
    rw [← Finset.mul_sum]
    generalize (∑ j ∈ Finset.range (N + 1), lorTerm v j) = S
    field_simp
  have hmono' : (1 / (2 * Real.pi)) * (∫ r, Fsq v r * (c - ∑ j ∈ Finset.range (N + 1), lz ((j : ℝ) + 1 / 4) r))
      ≤ (1 / (2 * Real.pi)) * (∫ r, Fsq v r * RvMBridge11.psiR r) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  rw [hsplit, hk] at hmono'
  have hlin : (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) - Real.log Real.pi)
      * acR v 0 = c * acR v 0 - acR v 0 * Real.log Real.pi := by rw [hc]; ring
  rw [hlin]
  linarith [hmono', hpos2]

/-- **The prime half alone**: `primeSide(v * v~)` is the finite real comb sum. -/
theorem FreqData.prime_eq :
    WeilExplicit.primeSide (WeilForm.autocorr (fun u => (v u : ℂ)))
      = ((∑ n ∈ Finset.range (⌈Real.exp (2 * L)⌉₊ + 1),
          (if Real.log n < 2 * L then
            2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR v (Real.log n) else 0) : ℝ) : ℂ) := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hgA : g = fun y => (acR v y : ℂ) := FreqData.acR_eq
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  /- the prime side is a finite sum -/
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  set term : ℕ → ℝ := fun n => if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR v (Real.log n) else 0 with hterm
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hprime_pt : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))
        = (term n : ℂ) := by
    intro n
    rw [hterm]
    simp only
    split_ifs with hn
    · rw [hgA]
      simp only
      rw [hv.acR_neg]
      push_cast
      ring
    · have h1 : acR v (Real.log n) = 0 := hv.acR_eq_zero ((not_lt.mp hn).trans (le_abs_self _))
      have h2 : acR v (-Real.log n) = 0 :=
        hv.acR_eq_zero (by rw [abs_neg]; exact (not_lt.mp hn).trans (le_abs_self _))
      rw [hgA]
      simp only
      rw [h1, h2]
      simp
  have hprime : primeSide g = ((∑ n ∈ Finset.range N0, term n : ℝ) : ℂ) := by
    unfold primeSide
    have hvan : ∀ n ∉ Finset.range N0, term n = 0 := fun n hn => by
      rw [hterm]; simp only; rw [if_neg (hbig n hn)]
    rw [tsum_congr hprime_pt, ← Complex.ofReal_tsum, tsum_eq_sum (s := Finset.range N0) hvan]
  exact hprime

end

end Crux3
