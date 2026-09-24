/-
  Crux3_BandCert -- THE ZETA-SIDE HEIGHT-LOCAL BAND CERTIFICATE (rvm_bridge island, 2026-09-24,
  crux lane 3; round-2 RH crux section 4.3, "the first window certificate that DH FAILS").

  conjecture1_proved = False.  This is NOT RH, not a reduction of RH, and not a zero-free region.  It
  is a positivity statement on a TWO-dimensional space of test functions at ONE window.

  MAIN THEOREM (`band_floor`, hypothesis-free, axioms [propext, Classical.choice, Quot.sound]):
  for all real `c1, c2`, with `v(u) = c1 cos(763 u/9) + c2 cos(259 u/3)` on `[-9 pi/14, 9 pi/14]`
  and `v = 0` outside (window `x = e^{9 pi/7} = 56.78`; `k1 A = 109 pi/2`, `k2 A = 111 pi/2`),
      (1/2) int |v|^2  <=  Re WeilForm.weilForm (WeilForm.autocorr v)      (= archSide - primeSide).
  The spectral mass of `v` sits at `|t|` in [83.2, 87.9] (height r = 85.6, band B ~ 2.3).
  The true least Rayleigh quotient on this span is 0.6989 (computed; the zero side
  sum_gamma F(gamma)^2 over 2000 zeros + tail reproduces it to 5e-9).

  THE DAVENPORT-HEILBRONN FAILURE (not in this file; Arb-certified in the lane's arb_cert.py):
  D's own explicit-formula functional (Gamma_R(s+1), conductor 5, no pole, prime side weighted by
  the Dirichlet coefficients c_D(n) of -D'/D, which are signed and not supported on prime powers)
  takes the value -0.6545762050(+-3e-11) ||v||^2 on the SAME window at c = (-3, 2).  The zero side of
  D explains it: the off-line quadruple 0.8085 +- 85.699 i contributes -1.046 against +0.390 from all
  on-line zeros.  So this is a window certificate whose conclusion FAILS for D: its validity depends on
  zeta's arithmetic weights Lambda(n), n <= 56, not only on the functional equation shape.

  HONEST LIMITS.  (i) The certificate uses only Lambda(n) for n <= 56 and Gamma_R(s): every
  one-prime surgery zeta(s)(1 + c p^{-s} + p p^{-2s}) at a prime p > 57 passes it verbatim (its window
  form is Q_zeta + 2 log p Id) while having off-line zeros; no fixed-window certificate can do
  otherwise (Crux2_unified_barrier.semilocal_barrier_full).  (ii) In zero language the theorem is a
  weighted statement about zeta's zeros near height 85.6, all of which are verified on the line
  (to 3e12); its content is that the ARITHMETIC data alone certifies it, which D's data cannot.
  (iii) Tests are continuous, not smooth (outside the registry's IsWeilTest class); the explicit
  formula for them follows from the smooth case by approximation (paper-level; not used here).

  PROOF.  `FreqData.weil_re_ge` (Crux3_BandAnalytic) with `N = 100` Lorentzians; the closed forms of
  Crux3_BandTest; the prime side by the kernel-checked table (Crux3_BandTable); gamma <= 0.58112
  (RvMBridge30), log pi <= 1.1448 (proved here from pi < 3.1416 <= e^{1.1448}), pi to 20 digits;
  the Lorentzian sums by exact rational arithmetic (`decide +kernel`); the 2 x 2 form
  `[[a, b], [b, d]]` with `a >= 7.598`, `d >= 0.3699`, `|b| <= 1.0942` is positive (`quad_nonneg`).
  No `sorry`.
-/
import Crux3_BandTest
import Crux3_BandTable

open MeasureTheory Complex Zeta23 Set Filter
open scoped ComplexConjugate

noncomputable section

namespace Crux3
/-! ## Part H: the instance `A = 9π/14`, `k1 = 763/9`, `k2 = 259/3` and the final certificate. -/

/-- The window half-width `A = 9π/14` (`x = e^{2A} = e^{9π/7} ≈ 56.78`). -/
def bandA : ℝ := (9 / 14 : ℝ) * Real.pi
/-- The two Dirichlet frequencies: `k1 A = 109π/2`, `k2 A = 111π/2`. -/
def bk1 : ℝ := 763 / 9
def bk2 : ℝ := 259 / 3

/-- The concrete band test `v_c(u) = c1 cos(763u/9) + c2 cos(259u/3)` on `[-9π/14, 9π/14]`. -/
def bandTest (c1 c2 : ℝ) : ℝ → ℝ := bandV bandA bk1 bk2 c1 c2

theorem pairHyp0 : PairHyp bandA bk1 bk2 1 (-1) where
  A0 := by unfold bandA; positivity
  k10 := by unfold bk1; norm_num
  k20 := by unfold bk2; norm_num
  k12 := by unfold bk1 bk2; norm_num
  k1one := by unfold bk1; norm_num
  cos1 := by
    unfold bk1 bandA
    rw [show (763 / 9 : ℝ) * ((9 / 14 : ℝ) * Real.pi) = Real.pi / 2 + ((27 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, Real.cos_add_int_mul_two_pi, Real.cos_pi_div_two]
  cos2 := by
    unfold bk2 bandA
    rw [show (259 / 3 : ℝ) * ((9 / 14 : ℝ) * Real.pi) = Real.pi / 2 + Real.pi + ((27 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, Real.cos_add_int_mul_two_pi, Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  sin1 := by
    unfold bk1 bandA
    rw [show (763 / 9 : ℝ) * ((9 / 14 : ℝ) * Real.pi) = Real.pi / 2 + ((27 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
  sin2 := by
    unfold bk2 bandA
    rw [show (259 / 3 : ℝ) * ((9 / 14 : ℝ) * Real.pi) = Real.pi / 2 + Real.pi + ((27 : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, Real.sin_add_int_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two]

/-- `log π <= 1.1448` (from `π < 3.1416 <= e^{1.1448}`). -/
lemma log_pi_le' : Real.log Real.pi ≤ 11448 / 10000 := by
  have hq : |((11448 / 10000 : ℚ)) / 8| ≤ 1 := by norm_num
  have h := exp_near KX (by unfold KX; norm_num) hq
  have hpos : (0 : ℚ) ≤ expSQ KX ((11448 / 10000 : ℚ) / 8) - expRQ KX ((11448 / 10000 : ℚ) / 8) := by
    unfold KX; decide +kernel
  have hc : PHIq ≤ (expSQ KX ((11448 / 10000 : ℚ) / 8) - expRQ KX ((11448 / 10000 : ℚ) / 8)) ^ 8 := by
    unfold KX PHIq; decide +kernel
  have hlo : ((expSQ KX ((11448 / 10000 : ℚ) / 8) - expRQ KX ((11448 / 10000 : ℚ) / 8) : ℚ) : ℝ)
      ≤ Real.exp (((11448 / 10000 : ℚ) / 8 : ℚ) : ℝ) := by
    have := neg_abs_le (Real.exp (((11448 / 10000 : ℚ) / 8 : ℚ) : ℝ) - (expSQ KX ((11448 / 10000 : ℚ) / 8) : ℝ))
    rw [Rat.cast_sub]
    linarith
  have h8 : Real.exp ((11448 / 10000 : ℚ) : ℝ) = Real.exp ((((11448 / 10000 : ℚ) / 8 : ℚ)) : ℝ) ^ 8 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hposR : (0 : ℝ) ≤ ((expSQ KX ((11448 / 10000 : ℚ) / 8) - expRQ KX ((11448 / 10000 : ℚ) / 8) : ℚ) : ℝ) := by
    exact_mod_cast hpos
  have hpow := pow_le_pow_left₀ hposR hlo 8
  have hcR : ((PHIq : ℚ) : ℝ) ≤ ((expSQ KX ((11448 / 10000 : ℚ) / 8) - expRQ KX ((11448 / 10000 : ℚ) / 8) : ℚ) : ℝ) ^ 8 := by
    exact_mod_cast hc
  have hpi : Real.pi < ((PHIq : ℚ) : ℝ) := by have := Real.pi_lt_d20; unfold PHIq; push_cast; linarith
  have : Real.pi ≤ Real.exp ((11448 / 10000 : ℚ) : ℝ) := by rw [h8]; linarith
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have e : ((11448 / 10000 : ℚ) : ℝ) = 11448 / 10000 := by push_cast; ring
  rw [← e]
  exact this

/-- The quadratic-form lemma: `a x^2 + 2 b x y + d y^2 >= 0` from `α <= a`, `δ <= d`, `|b| <= β`,
`α, δ > 0`, `β^2 <= α δ`. -/
lemma quad_nonneg {a b d α β δ : ℝ} (ha : α ≤ a) (hd : δ ≤ d) (hb : |b| ≤ β) (hα : 0 < α) (_hδ : 0 < δ)
    (hβ : β ^ 2 ≤ α * δ) (x y : ℝ) : 0 ≤ a * x ^ 2 + 2 * b * x * y + d * y ^ 2 := by
  have h1 : α * x ^ 2 + δ * y ^ 2 - 2 * β * |x| * |y| ≥ 0 := by
    have hβ0 : 0 ≤ β := le_trans (abs_nonneg _) hb
    have key : 0 ≤ (α * |x| - β * |y|) ^ 2 + (α * δ - β ^ 2) * y ^ 2 := by positivity
    have e : (α * |x| - β * |y|) ^ 2 + (α * δ - β ^ 2) * y ^ 2
        = α * (α * x ^ 2 + δ * y ^ 2 - 2 * β * |x| * |y|) := by
      rw [show (α * |x| - β * |y|) ^ 2 = α ^ 2 * |x| ^ 2 - 2 * α * β * |x| * |y| + β ^ 2 * |y| ^ 2 by ring,
        sq_abs, sq_abs]
      ring
    rw [e] at key
    have := (mul_nonneg_iff_of_pos_left hα).mp key
    linarith
  have h2 : |2 * b * x * y| ≤ 2 * β * |x| * |y| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg x) (abs_nonneg y))
    nlinarith [abs_nonneg x, abs_nonneg y]
  have h3 : a * x ^ 2 ≥ α * x ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg x)
  have h4 : d * y ^ 2 ≥ δ * y ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg y)
  linarith [neg_abs_le (2 * b * x * y)]


/-! ## Part I: the final certificate. -/

lemma Jd_le {A k b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    Jd A k b ≤ A * (4 * b / (4 * b ^ 2 + k ^ 2)) + 4 * k ^ 2 / (4 * b ^ 2 + k ^ 2) ^ 2 := by
  unfold Jd
  have hE : Real.exp (-(2 * b) * (2 * A)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hD : 0 ≤ 4 * b ^ 2 + k ^ 2 := by positivity
  have h1 : 2 * A * (2 * b) / (4 * b ^ 2 + k ^ 2) = A * (4 * b / (4 * b ^ 2 + k ^ 2)) := by ring
  have h2 : 2 * k ^ 2 * (1 + Real.exp (-(2 * b) * (2 * A))) / (4 * b ^ 2 + k ^ 2) ^ 2
      ≤ 4 * k ^ 2 / (4 * b ^ 2 + k ^ 2) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg k]
  linarith

lemma Jx_bounds {A k1 k2 b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hk1 : 0 < k1) (hk2 : 0 < k2) :
    -(4 * k1 * k2 / ((4 * b ^ 2 + k1 ^ 2) * (4 * b ^ 2 + k2 ^ 2))) ≤ Jx A k1 k2 1 (-1) b
      ∧ Jx A k1 k2 1 (-1) b ≤ -(2 * k1 * k2 / ((4 * b ^ 2 + k1 ^ 2) * (4 * b ^ 2 + k2 ^ 2))) := by
  unfold Jx
  have hE0 : 0 ≤ Real.exp (-(2 * b) * (2 * A)) := (Real.exp_pos _).le
  have hE : Real.exp (-(2 * b) * (2 * A)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hD : 0 < (4 * b ^ 2 + k1 ^ 2) * (4 * b ^ 2 + k2 ^ 2) := by positivity
  have hk : 0 < k1 * k2 := mul_pos hk1 hk2
  constructor
  · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hD]
    nlinarith
  · rw [le_neg, ← neg_div, div_le_div_iff_of_pos_right hD]
    nlinarith

/-- The three prime sums of the band. -/
def Pr11 : ℝ := ∑ n ∈ Finset.range 57, 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk1 (Real.log n)
def Pr22 : ℝ := ∑ n ∈ Finset.range 57, 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk2 (Real.log n)
def Pr12 : ℝ := ∑ n ∈ Finset.range 57, 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n)

lemma P0_cast : ((P0.Q : ℚ) : ℝ) * Real.pi = bandA ∧ ((P0.k1 : ℚ) : ℝ) = bk1 ∧ ((P0.k2 : ℚ) : ℝ) = bk2
    ∧ ((P0.s12 : ℚ) : ℝ) = -1 := by
  unfold P0 bandA bk1 bk2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

lemma entry_ok (n : ℕ) (hn : n < 57) : entryOK P0 n (tab n) = true := by
  have h := tab_ok
  rw [List.all_eq_true] at h
  exact h n (List.mem_range.mpr hn)

lemma entry_sound0 (n : ℕ) (hn : n < 57) :
    InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk1 (Real.log n))
        (outB P0 (tab n)).1.1 (outB P0 (tab n)).1.2
      ∧ InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk2 (Real.log n))
        (outB P0 (tab n)).2.1.1 (outB P0 (tab n)).2.1.2
      ∧ InB (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n))
        (outB P0 (tab n)).2.2.1 (outB P0 (tab n)).2.2.2
      ∧ ((tab n).mu ≠ 0 → Real.log n < 2 * bandA) := by
  have h := entry_sound P0 (by unfold P0; norm_num) n (tab n) (entry_ok n hn) (lam_tab n hn)
  obtain ⟨hQ, hk1, hk2, hs⟩ := P0_cast
  rw [hQ, hk1, hk2, hs] at h
  have e : ∀ A k y : ℝ, gDr A k y = gD A k y := fun _ _ _ => rfl
  simp only [e] at h
  exact h

theorem Pr_balls :
    InB Pr11 (∑ n ∈ Finset.range 57, (outB P0 (tab n)).1.1) (∑ n ∈ Finset.range 57, (outB P0 (tab n)).1.2)
      ∧ InB Pr22 (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.1.1) (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.1.2)
      ∧ InB Pr12 (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.1) (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact InB.sum _ _ _ _ fun n hn => (entry_sound0 n (Finset.mem_range.mp hn)).1
  · exact InB.sum _ _ _ _ fun n hn => (entry_sound0 n (Finset.mem_range.mp hn)).2.1
  · exact InB.sum _ _ _ _ fun n hn => (entry_sound0 n (Finset.mem_range.mp hn)).2.2.1

/-! The rational facts, evaluated by the kernel. -/

theorem q_P11 : (∑ n ∈ Finset.range 57, (outB P0 (tab n)).1.1) + (∑ n ∈ Finset.range 57, (outB P0 (tab n)).1.2)
    ≤ -3549021094 / 10 ^ 9 := by decide +kernel
theorem q_P22 : (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.1.1) + (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.1.2)
    ≤ 3711146728 / 10 ^ 9 := by decide +kernel
theorem q_P12hi : (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.1) + (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.2)
    ≤ 1103195930 / 10 ^ 9 := by decide +kernel
theorem q_P12lo : 1103195928 / 10 ^ 9 ≤
    (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.1) - (∑ n ∈ Finset.range 57, (outB P0 (tab n)).2.2.2) := by
  decide +kernel

theorem q_H : (51873775 / 10 ^ 7 : ℚ) ≤ ∑ n ∈ Finset.range 100, (1 : ℚ) / ((n : ℚ) + 1) := by decide +kernel
theorem q_S1a : (∑ j ∈ Finset.range 101, 4 * ((j : ℚ) + 1 / 4) / (4 * ((j : ℚ) + 1 / 4) ^ 2 + (763 / 9) ^ 2))
    ≤ 94725563 / 10 ^ 8 := by decide +kernel
theorem q_S1b : (∑ j ∈ Finset.range 101, 4 * ((j : ℚ) + 1 / 4) / (4 * ((j : ℚ) + 1 / 4) ^ 2 + (259 / 3) ^ 2))
    ≤ 93185017 / 10 ^ 8 := by decide +kernel
theorem q_S2a : (∑ j ∈ Finset.range 101, 4 * (763 / 9 : ℚ) ^ 2 / (4 * ((j : ℚ) + 1 / 4) ^ 2 + (763 / 9) ^ 2) ^ 2)
    ≤ 1818638 / 10 ^ 8 := by decide +kernel
theorem q_S2b : (∑ j ∈ Finset.range 101, 4 * (259 / 3 : ℚ) ^ 2 / (4 * ((j : ℚ) + 1 / 4) ^ 2 + (259 / 3) ^ 2) ^ 2)
    ≤ 1783309 / 10 ^ 8 := by decide +kernel
theorem q_Sx : (9004122 / 10 ^ 9 : ℚ) ≤ (∑ j ∈ Finset.range 101, 2 * (763 / 9 : ℚ) * (259 / 3)
      / ((4 * ((j : ℚ) + 1 / 4) ^ 2 + (763 / 9) ^ 2) * (4 * ((j : ℚ) + 1 / 4) ^ 2 + (259 / 3) ^ 2)))
    ∧ (∑ j ∈ Finset.range 101, 2 * (763 / 9 : ℚ) * (259 / 3)
      / ((4 * ((j : ℚ) + 1 / 4) ^ 2 + (763 / 9) ^ 2) * (4 * ((j : ℚ) + 1 / 4) ^ 2 + (259 / 3) ^ 2)))
      ≤ 9004123 / 10 ^ 9 := by decide +kernel

/-- `2A < log 57`, so `n >= 57` never enters the comb. -/
lemma twoA_lt_log57 : 2 * bandA < Real.log 57 := by
  have h := le_log_of KX (by unfold KX; norm_num) (q := 4043051267834549 / 10 ^ 15) 57 (by norm_num)
    (by norm_num) (by unfold KX; decide +kernel)
  have hpi := Real.pi_lt_d20
  unfold bandA
  have : ((4043051267834549 / 10 ^ 15 : ℚ) : ℝ) = 4043051267834549 / 10 ^ 15 := by push_cast; ring
  rw [this] at h
  push_cast at h
  linarith


/-! ## Part J: the main theorem. -/

lemma sum_range_eq_of_vanish (f : ℕ → ℝ) (a b : ℕ) (ha : ∀ n, a ≤ n → f n = 0) (hb : ∀ n, b ≤ n → f n = 0) :
    ∑ n ∈ Finset.range a, f n = ∑ n ∈ Finset.range b, f n := by
  rcases le_total a b with hab | hab
  · refine Finset.sum_subset (Finset.range_subset_range.mpr hab) (fun n hn hn' => ha n ?_)
    simp only [Finset.mem_range, not_lt] at hn'
    exact hn'
  · symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr hab) (fun n hn hn' => hb n ?_)
    simp only [Finset.mem_range, not_lt] at hn'
    exact hn'

lemma gX_eq (y : ℝ) : gX bk1 bk2 1 (-1) y = gXr bk1 bk2 (-1) y := by
  unfold gX gXr; ring

/-- The archimedean constant of the certificate: `-gamma + H_100 - log pi`. -/
def Cw : ℝ := -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range 100, (1 : ℝ) / ((n : ℝ) + 1) - Real.log Real.pi
/-- The Lorentzian sums of the band, `N = 100`. -/
def SJ1 : ℝ := ∑ j ∈ Finset.range (100 + 1), Jd bandA bk1 ((j : ℝ) + 1 / 4)
def SJ2 : ℝ := ∑ j ∈ Finset.range (100 + 1), Jd bandA bk2 ((j : ℝ) + 1 / 4)
def SJx : ℝ := ∑ j ∈ Finset.range (100 + 1), Jx bandA bk1 bk2 1 (-1) ((j : ℝ) + 1 / 4)

lemma Cw_ge : (34614575 / 10 ^ 7 : ℝ) ≤ Cw := by
  have hq := Rat.cast_le (K := ℝ) |>.mpr q_H
  push_cast at hq
  have hγ := RvMBridge30.eulerMascheroni_le
  have hlp := log_pi_le'
  unfold Cw
  norm_num at hγ hq ⊢
  linarith

lemma bandA_bounds : (9 / 14 : ℝ) * (314159265358979323846 / 10 ^ 20) ≤ bandA
    ∧ bandA ≤ (9 / 14 : ℝ) * (314159265358979323847 / 10 ^ 20) := by
  have hpil := Real.pi_gt_d20
  have hpih := Real.pi_lt_d20
  unfold bandA
  constructor <;> norm_num at hpil hpih ⊢ <;> linarith

lemma SJ1_le : SJ1 ≤ bandA * (94725563 / 10 ^ 8) + 1818638 / 10 ^ 8 := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hq1 := Rat.cast_le (K := ℝ) |>.mpr q_S1a
  have hq2 := Rat.cast_le (K := ℝ) |>.mpr q_S2a
  push_cast at hq1 hq2
  have hle : SJ1 ≤ ∑ j ∈ Finset.range 101, (bandA * (4 * ((j : ℝ) + 1 / 4) / (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2))
      + 4 * bk1 ^ 2 / (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2) ^ 2) :=
    Finset.sum_le_sum fun j _ => Jd_le hA0.le (by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  unfold bk1 at hle
  have := mul_le_mul_of_nonneg_left hq1 hA0.le
  linarith

lemma SJ2_le : SJ2 ≤ bandA * (93185017 / 10 ^ 8) + 1783309 / 10 ^ 8 := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hq1 := Rat.cast_le (K := ℝ) |>.mpr q_S1b
  have hq2 := Rat.cast_le (K := ℝ) |>.mpr q_S2b
  push_cast at hq1 hq2
  have hle : SJ2 ≤ ∑ j ∈ Finset.range 101, (bandA * (4 * ((j : ℝ) + 1 / 4) / (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2))
      + 4 * bk2 ^ 2 / (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2) ^ 2) :=
    Finset.sum_le_sum fun j _ => Jd_le hA0.le (by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
  unfold bk2 at hle
  have := mul_le_mul_of_nonneg_left hq1 hA0.le
  linarith

lemma SJx_bounds : -(2 * (9004123 / 10 ^ 9)) ≤ SJx ∧ SJx ≤ -(9004122 / 10 ^ 9) := by
  have hA0 : 0 < bandA := pairHyp0.A0
  have hk1 : (0 : ℝ) < bk1 := pairHyp0.k10
  have hk2 : (0 : ℝ) < bk2 := pairHyp0.k20
  obtain ⟨q1, q2⟩ := q_Sx
  have hx1 := Rat.cast_le (K := ℝ) |>.mpr q1
  have hx2 := Rat.cast_le (K := ℝ) |>.mpr q2
  push_cast at hx1 hx2
  have hlo : ∑ j ∈ Finset.range 101, -(4 * bk1 * bk2 / ((4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2)
        * (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2))) ≤ SJx :=
    Finset.sum_le_sum fun j _ => (Jx_bounds hA0.le (by positivity) hk1 hk2).1
  have hhi : SJx ≤ ∑ j ∈ Finset.range 101, -(2 * bk1 * bk2 / ((4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2)
        * (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2))) :=
    Finset.sum_le_sum fun j _ => (Jx_bounds hA0.le (by positivity) hk1 hk2).2
  rw [Finset.sum_neg_distrib] at hlo hhi
  have e : ∑ j ∈ Finset.range 101, 4 * bk1 * bk2 / ((4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2)
        * (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2))
      = 2 * ∑ j ∈ Finset.range 101, 2 * bk1 * bk2 / ((4 * ((j : ℝ) + 1 / 4) ^ 2 + bk1 ^ 2)
        * (4 * ((j : ℝ) + 1 / 4) ^ 2 + bk2 ^ 2)) := by
    rw [Finset.mul_sum]; congr 1; funext j; ring
  rw [e] at hlo
  unfold bk1 bk2 at hlo hhi
  constructor <;> linarith

lemma Pr_bounds : Pr11 ≤ -3549021094 / 10 ^ 9 ∧ Pr22 ≤ 3711146728 / 10 ^ 9
    ∧ 1103195928 / 10 ^ 9 ≤ Pr12 ∧ Pr12 ≤ 1103195930 / 10 ^ 9 := by
  obtain ⟨hP11, hP22, hP12⟩ := Pr_balls
  have a1 := hP11.le
  have a2 := hP22.le
  have a3 := hP12.le
  have a4 := hP12.ge
  have q1 := Rat.cast_le (K := ℝ) |>.mpr q_P11
  have q2 := Rat.cast_le (K := ℝ) |>.mpr q_P22
  have q3 := Rat.cast_le (K := ℝ) |>.mpr q_P12hi
  have q4 := Rat.cast_le (K := ℝ) |>.mpr q_P12lo
  push_cast at a1 a2 a3 a4 q1 q2 q3 q4
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The two diagonal entries and the off-diagonal entry of the certified `2 x 2` form. -/
lemma form_entries : (7598 / 1000 : ℝ) ≤ Cw * bandA - SJ1 - Pr11 - bandA / 2
    ∧ (3699 / 10000 : ℝ) ≤ Cw * bandA - SJ2 - Pr22 - bandA / 2
    ∧ |-SJx - Pr12| ≤ 10942 / 10000 := by
  have hA := bandA_bounds
  have hC := Cw_ge
  have h1 := SJ1_le
  have h2 := SJ2_le
  have hx := SJx_bounds
  have hP := Pr_bounds
  have hCA : (34614575 / 10 ^ 7 : ℝ) * ((9 / 14 : ℝ) * (314159265358979323846 / 10 ^ 20)) ≤ Cw * bandA :=
    mul_le_mul hC hA.1 (by norm_num) (le_trans (by norm_num) hC)
  refine ⟨?_, ?_, ?_⟩
  · linarith [hA.2]
  · linarith [hA.2]
  · rw [abs_le]; constructor <;> linarith

/-- The prime sum of the general lower bound, specialised to the band. -/
lemma prime_sum_band (c1 c2 : ℝ) :
    ∑ n ∈ Finset.range (⌈Real.exp (2 * bandA)⌉₊ + 1),
        (if Real.log n < 2 * bandA then
          2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR (bandV bandA bk1 bk2 c1 c2) (Real.log n) else 0)
      = c1 ^ 2 * Pr11 + 2 * c1 * c2 * Pr12 + c2 ^ 2 * Pr22 := by
  have h := pairHyp0
  set f : ℕ → ℝ := fun n => if Real.log n < 2 * bandA then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * acR (bandV bandA bk1 bk2 c1 c2) (Real.log n) else 0
    with hf
  have hfN0 : ∀ n, ⌈Real.exp (2 * bandA)⌉₊ + 1 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.exp (2 * bandA) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * bandA))
      have h2 : ((⌈Real.exp (2 * bandA)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    have h3 : 2 * bandA < Real.log n := by
      rw [← Real.log_exp (2 * bandA)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hf57 : ∀ n, 57 ≤ n → f n = 0 := by
    intro n hn
    rw [hf]; simp only
    rw [if_neg]
    intro hlt
    have h1 : Real.log 57 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith [twoA_lt_log57]
  have hterm : ∀ n ∈ Finset.range 57, f n
      = c1 ^ 2 * (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk1 (Real.log n))
        + 2 * c1 * c2 * (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gXr bk1 bk2 (-1) (Real.log n))
        + c2 ^ 2 * (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * gD bandA bk2 (Real.log n)) := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    by_cases hmu : (tab n).mu = 0
    · have hl : ArithmeticFunction.vonMangoldt n = 0 := by rw [lam_tab n hn', hmu]; simp
      rw [hf]; simp only; rw [hl]; simp
    · have hlt := (entry_sound0 n hn').2.2.2 hmu
      rw [hf]; simp only; rw [if_pos hlt]
      rw [acR_bandV h c1 c2 (Real.log_natCast_nonneg n) hlt.le, gX_eq]
      ring
  rw [sum_range_eq_of_vanish f _ _ hfN0 hf57, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- **THE ZETA-SIDE BAND CERTIFICATE (kernel-checked).**  For every `c1, c2`, the Weil functional
of the registry (`WeilForm.weilForm = archSide - primeSide`, the arithmetic side of the E8
explicit formula; NO zeros involved) evaluated on the autocorrelation of the band test
`v(u) = c1 cos(763u/9) + c2 cos(259u/3)` on `[-9π/14, 9π/14]` (zero outside) satisfies
`Re W(v * v~) >= (1/2) ||v||^2`.  (Least eigenvalue on this span: 0.699 (computed).  The same
two tests give Davenport-Heilbronn's explicit-formula functional the value -0.655 ||v||^2 at
`c = (-3, 2)` (Arb-certified, research note), and D's value there is kernel-checked to be at most
`-(1/2) ||v||^2` (`Crux3.dh_band_negative`, module `Crux3_BandDH`): the window certificate that D fails.) -/
theorem band_floor (c1 c2 : ℝ) :
    (1 / 2 : ℝ) * (∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2)
      ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re := by
  have h := pairHyp0
  have hv := bandV_freqData h c1 c2
  have hW := hv.weil_re_ge 100
  have hnorm : ∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2 = bandA * (c1 ^ 2 + c2 ^ 2) := by
    rw [← acR_bandV_zero h c1 c2]
    unfold acR bandTest
    congr 1
    funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, sq]
  rw [hnorm]
  rw [acR_bandV_zero h c1 c2, prime_sum_band c1 c2] at hW
  have hlor : ∑ j ∈ Finset.range (100 + 1), lorTerm (bandV bandA bk1 bk2 c1 c2) j
      = c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2 := by
    rw [Finset.sum_congr rfl (fun j _ => lorTerm_bandV h c1 c2 j), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [hlor] at hW
  obtain ⟨ha, hd, hb⟩ := form_entries
  have hq := quad_nonneg ha hd hb (by norm_num) (by norm_num) (by norm_num) c1 c2
  have e : Cw * (bandA * (c1 ^ 2 + c2 ^ 2)) - (c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2)
      - (c1 ^ 2 * Pr11 + 2 * c1 * c2 * Pr12 + c2 ^ 2 * Pr22) - (1 / 2 : ℝ) * (bandA * (c1 ^ 2 + c2 ^ 2))
      = (Cw * bandA - SJ1 - Pr11 - bandA / 2) * c1 ^ 2 + 2 * (-SJx - Pr12) * c1 * c2
        + (Cw * bandA - SJ2 - Pr22 - bandA / 2) * c2 ^ 2 := by ring
  have hW' : Cw * (bandA * (c1 ^ 2 + c2 ^ 2)) - (c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2)
      - (c1 ^ 2 * Pr11 + 2 * c1 * c2 * Pr12 + c2 ^ 2 * Pr22)
      ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re := hW
  linarith


/-! ## Part K: the certificate in round-2 form -- band comb constant below band archimedean floor. -/

/-- The prime side of the band test is the explicit quadratic form in `(c1, c2)`. -/
lemma band_prime_eq (c1 c2 : ℝ) :
    (WeilExplicit.primeSide (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re
      = c1 ^ 2 * Pr11 + 2 * c1 * c2 * Pr12 + c2 ^ 2 * Pr22 := by
  have hv := bandV_freqData pairHyp0 c1 c2
  have h := hv.prime_eq
  unfold bandTest
  rw [h, Complex.ofReal_re, prime_sum_band c1 c2]

/-- **Band comb constant** (round-2 `A_B(r)` at `r = 85.6`, `B ~ 2.3`, `L = 9π/14`): the twisted prime
comb on the band is at most `1.92 ||v||^2` (computed top eigenvalue 1.919; the pointwise comb mass
is 24.4). -/
theorem band_comb_le (c1 c2 : ℝ) :
    (WeilExplicit.primeSide (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re
      ≤ (192 / 100 : ℝ) * (∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2) := by
  have h := pairHyp0
  have hnorm : ∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2 = bandA * (c1 ^ 2 + c2 ^ 2) := by
    rw [← acR_bandV_zero h c1 c2]
    unfold acR bandTest
    congr 1
    funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, sq]
  rw [band_prime_eq, hnorm]
  obtain ⟨hA1, hA2⟩ := bandA_bounds
  obtain ⟨p1, p2, p3, p4⟩ := Pr_bounds
  have ha : (74266 / 10000 : ℝ) ≤ (192 / 100) * bandA - Pr11 := by linarith
  have hd : (16647 / 100000 : ℝ) ≤ (192 / 100) * bandA - Pr22 := by linarith
  have hb : |-Pr12| ≤ 110320 / 100000 := by rw [abs_le]; constructor <;> linarith
  have hq := quad_nonneg ha hd hb (by norm_num) (by norm_num) (by norm_num) c1 c2
  nlinarith [hq]

/-- **Band archimedean floor**: the archimedean side (poles and Gamma_R) on the band is at least
`2.49 ||v||^2` (computed band eigenvalues 2.596, 2.617; `Omega_zeta(85.6) = 2.611`). -/
theorem band_arch_ge (c1 c2 : ℝ) :
    (249 / 100 : ℝ) * (∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2)
      ≤ (WeilExplicit.archSide (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re := by
  have h := pairHyp0
  have hv := bandV_freqData h c1 c2
  have hA := hv.arch_re_ge 100
  have hnorm : ∫ x, ‖((bandTest c1 c2 x : ℝ) : ℂ)‖ ^ 2 = bandA * (c1 ^ 2 + c2 ^ 2) := by
    rw [← acR_bandV_zero h c1 c2]
    unfold acR bandTest
    congr 1
    funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, sq]
  rw [hnorm]
  rw [acR_bandV_zero h c1 c2] at hA
  have hlor : ∑ j ∈ Finset.range (100 + 1), lorTerm (bandV bandA bk1 bk2 c1 c2) j
      = c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2 := by
    rw [Finset.sum_congr rfl (fun j _ => lorTerm_bandV h c1 c2 j), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [hlor] at hA
  have hA' : Cw * (bandA * (c1 ^ 2 + c2 ^ 2)) - (c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2)
      ≤ (WeilExplicit.archSide (WeilForm.autocorr (fun u => ((bandTest c1 c2 u : ℝ) : ℂ)))).re := hA
  obtain ⟨hA1, hA2⟩ := bandA_bounds
  have hC := Cw_ge
  have h1 := SJ1_le
  have h2 := SJ2_le
  have hx := SJx_bounds
  have hCA : (34614575 / 10 ^ 7 : ℝ) * ((9 / 14 : ℝ) * (314159265358979323846 / 10 ^ 20)) ≤ Cw * bandA :=
    mul_le_mul hC hA1 (by norm_num) (le_trans (by norm_num) hC)
  have ha : (3 / 100 : ℝ) ≤ Cw * bandA - SJ1 - (249 / 100) * bandA := by linarith
  have hd : (6 / 100 : ℝ) ≤ Cw * bandA - SJ2 - (249 / 100) * bandA := by linarith
  have hb : |-SJx| ≤ 2 / 100 := by rw [abs_le]; constructor <;> linarith
  have hq := quad_nonneg ha hd hb (by norm_num) (by norm_num) (by norm_num) c1 c2
  have e : Cw * (bandA * (c1 ^ 2 + c2 ^ 2)) - (c1 ^ 2 * SJ1 + 2 * c1 * c2 * SJx + c2 ^ 2 * SJ2)
      - (249 / 100 : ℝ) * (bandA * (c1 ^ 2 + c2 ^ 2))
      = (Cw * bandA - SJ1 - (249 / 100) * bandA) * c1 ^ 2 + 2 * (-SJx) * c1 * c2
        + (Cw * bandA - SJ2 - (249 / 100) * bandA) * c2 ^ 2 := by ring
  linarith

end Crux3
