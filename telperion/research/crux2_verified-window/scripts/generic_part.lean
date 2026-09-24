import Mathlib
import E6Bridge5

open MeasureTheory WeilExplicit Complex Finset
open scoped ComplexConjugate

noncomputable section

namespace Crux2VerifiedWindow

/-! ## A. Finite core (ported from the idea-stage `CombSchur.lean`): discrete Schur test with
entrywise domination.  `K` = untwisted (entrywise nonnegative because `Λ ≥ 0`) discretized comb,
`M` = any twist of it (`‖M i j‖ ≤ K i j`), `w > 0` with `K w ≤ lam w`. -/

section FiniteCore

/-- AM-GM with weights: `a b ≤ (t a² + b²/t)/2` written with `t = w j / w i`. -/
lemma amgm_weighted (a b wi wj : ℝ) (hwi : 0 < wi) (hwj : 0 < wj) :
    a * b ≤ (wj / wi * a ^ 2 + wi / wj * b ^ 2) / 2 := by
  have hid : wj / wi * a ^ 2 + wi / wj * b ^ 2 - 2 * (a * b)
      = (wj * a - wi * b) ^ 2 / (wi * wj) := by
    field_simp
    ring
  have hnn : 0 ≤ (wj * a - wi * b) ^ 2 / (wi * wj) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hwi hwj))
  linarith

/-- Discrete Schur test with entrywise domination (twist invariance). -/
theorem schur_twist_bound {n : ℕ} (K : Fin n → Fin n → ℝ) (M : Fin n → Fin n → ℂ)
    (w : Fin n → ℝ) (lam : ℝ)
    (hKsymm : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j)
    (hw : ∀ i, 0 < w i) (hKw : ∀ i, ∑ j, K i j * w j ≤ lam * w i)
    (hdom : ∀ i j, ‖M i j‖ ≤ K i j) (x : Fin n → ℂ) :
    ‖∑ i, ∑ j, star (x i) * M i j * x j‖ ≤ lam * ∑ i, ‖x i‖ ^ 2 := by
  -- Step 1: triangle inequality and domination
  have h1 : ‖∑ i, ∑ j, star (x i) * M i j * x j‖ ≤ ∑ i, ∑ j, K i j * (‖x i‖ * ‖x j‖) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [norm_mul, norm_mul, norm_star]
    have hx : 0 ≤ ‖x i‖ * ‖x j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖x i‖ * ‖M i j‖ * ‖x j‖ = ‖M i j‖ * (‖x i‖ * ‖x j‖) := by ring
      _ ≤ K i j * (‖x i‖ * ‖x j‖) := mul_le_mul_of_nonneg_right (hdom i j) hx
  -- Step 2: weighted AM-GM termwise
  have h2 : ∑ i, ∑ j, K i j * (‖x i‖ * ‖x j‖)
      ≤ ∑ i, ∑ j, K i j * ((w j / w i * ‖x i‖ ^ 2 + w i / w j * ‖x j‖ ^ 2) / 2) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    exact mul_le_mul_of_nonneg_left (amgm_weighted _ _ _ _ (hw i) (hw j)) (hK0 i j)
  -- Step 3: split the double sum into the two halves
  have hsplit : ∑ i, ∑ j, K i j * ((w j / w i * ‖x i‖ ^ 2 + w i / w j * ‖x j‖ ^ 2) / 2)
      = (∑ i, (‖x i‖ ^ 2 / w i) * ∑ j, K i j * w j
          + ∑ j, (‖x j‖ ^ 2 / w j) * ∑ i, K i j * w i) / 2 := by
    have e1 : ∀ i j, K i j * ((w j / w i * ‖x i‖ ^ 2 + w i / w j * ‖x j‖ ^ 2) / 2)
        = ((‖x i‖ ^ 2 / w i) * (K i j * w j) + (‖x j‖ ^ 2 / w j) * (K i j * w i)) / 2 := by
      intro i j
      have := hw i; have := hw j
      field_simp
    simp_rw [e1, ← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_comm
  -- Step 4: bound each half by lam * ∑ ‖x‖²
  have hA : ∑ i, (‖x i‖ ^ 2 / w i) * ∑ j, K i j * w j ≤ lam * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hc : 0 ≤ ‖x i‖ ^ 2 / w i := div_nonneg (sq_nonneg _) (le_of_lt (hw i))
    calc (‖x i‖ ^ 2 / w i) * ∑ j, K i j * w j ≤ (‖x i‖ ^ 2 / w i) * (lam * w i) :=
          mul_le_mul_of_nonneg_left (hKw i) hc
      _ = lam * ‖x i‖ ^ 2 := by
          have := hw i
          field_simp
  have hB : ∑ j, (‖x j‖ ^ 2 / w j) * ∑ i, K i j * w i ≤ lam * ∑ j, ‖x j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hc : 0 ≤ ‖x j‖ ^ 2 / w j := div_nonneg (sq_nonneg _) (le_of_lt (hw j))
    have hsym : ∑ i, K i j * w i = ∑ i, K j i * w i :=
      Finset.sum_congr rfl (fun i _ => by rw [hKsymm i j])
    calc (‖x j‖ ^ 2 / w j) * ∑ i, K i j * w i = (‖x j‖ ^ 2 / w j) * ∑ i, K j i * w i := by
          rw [hsym]
      _ ≤ (‖x j‖ ^ 2 / w j) * (lam * w j) := mul_le_mul_of_nonneg_left (hKw j) hc
      _ = lam * ‖x j‖ ^ 2 := by
          have := hw j
          field_simp
  calc ‖∑ i, ∑ j, star (x i) * M i j * x j‖
      ≤ ∑ i, ∑ j, K i j * (‖x i‖ * ‖x j‖) := h1
    _ ≤ ∑ i, ∑ j, K i j * ((w j / w i * ‖x i‖ ^ 2 + w i / w j * ‖x j‖ ^ 2) / 2) := h2
    _ = (∑ i, (‖x i‖ ^ 2 / w i) * ∑ j, K i j * w j
          + ∑ j, (‖x j‖ ^ 2 / w j) * ∑ i, K i j * w i) / 2 := hsplit
    _ ≤ (lam * ∑ i, ‖x i‖ ^ 2 + lam * ∑ j, ‖x j‖ ^ 2) / 2 := by linarith
    _ = lam * ∑ i, ‖x i‖ ^ 2 := by ring

end FiniteCore

/-! ## B. The continuous Schur test for a window-compressed positive shift comb -/

open Classical in
/-- Schur ratio: `w y / w x` if both points lie in the window, else `0`. -/
def schurRatio (W : Set ℝ) (w : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x ∈ W ∧ y ∈ W then w y / w x else 0

/-- Admissible Schur weight on a window: measurable, positive and two-sided bounded on `W`. -/
structure SchurWeight (W : Set ℝ) (w : ℝ → ℝ) : Prop where
  meas_W : MeasurableSet W
  meas_w : Measurable w
  lower : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ W, m ≤ w x
  upper : ∃ M : ℝ, ∀ x ∈ W, w x ≤ M

lemma SchurWeight.pos {W : Set ℝ} {w : ℝ → ℝ} (hw : SchurWeight W w) : ∀ x ∈ W, 0 < w x := by
  obtain ⟨m, hm, hmw⟩ := hw.lower
  exact fun x hx => lt_of_lt_of_le hm (hmw x hx)

lemma schurRatio_nonneg {W : Set ℝ} {w : ℝ → ℝ} (hw : ∀ x ∈ W, 0 < w x) (x y : ℝ) :
    0 ≤ schurRatio W w x y := by
  unfold schurRatio
  split_ifs with h
  · exact div_nonneg (hw y h.2).le (hw x h.1).le
  · exact le_rfl

lemma schurRatio_le {W : Set ℝ} {w : ℝ → ℝ} (hw : SchurWeight W w) :
    ∃ C : ℝ, ∀ x y, ‖schurRatio W w x y‖ ≤ C := by
  obtain ⟨m, hm, hmw⟩ := hw.lower
  obtain ⟨M, hMw⟩ := hw.upper
  refine ⟨|M| / m, fun x y => ?_⟩
  have hpos := hw.pos
  rw [Real.norm_eq_abs, abs_of_nonneg (schurRatio_nonneg hpos x y)]
  unfold schurRatio
  split_ifs with h
  · have hx := hmw x h.1
    have hy := hMw y h.2
    have hwx := hpos x h.1
    have hwy := hpos y h.2
    rw [div_le_div_iff₀ hwx hm]
    have hMabs : M ≤ |M| := le_abs_self M
    have : w y * m ≤ M * w x := by nlinarith
    nlinarith [abs_nonneg M]
  · exact div_nonneg (abs_nonneg M) hm.le

lemma measurable_schurRatio_shift {W : Set ℝ} {w : ℝ → ℝ} (hw : SchurWeight W w) (u : ℝ) :
    Measurable (fun x => schurRatio W w x (x + u)) := by
  unfold schurRatio
  refine Measurable.ite ?_ ?_ measurable_const
  · exact hw.meas_W.inter (measurable_add_const u hw.meas_W)
  · exact (hw.meas_w.comp (measurable_add_const u)).div hw.meas_w

/-- Pointwise weighted AM-GM on the window (no cross-window terms because `g` vanishes off `W`). -/
lemma amgm_window {W : Set ℝ} {w : ℝ → ℝ} (hw : ∀ x ∈ W, 0 < w x) {g : ℝ → ℂ}
    (hg : ∀ x, x ∉ W → g x = 0) (x y : ℝ) :
    2 * (‖g x‖ * ‖g y‖) ≤ schurRatio W w x y * ‖g x‖ ^ 2 + schurRatio W w y x * ‖g y‖ ^ 2 := by
  by_cases h : x ∈ W ∧ y ∈ W
  · have hx := hw x h.1
    have hy := hw y h.2
    have e1 : schurRatio W w x y = w y / w x := by simp [schurRatio, h]
    have e2 : schurRatio W w y x = w x / w y := by simp [schurRatio, h.2, h.1]
    rw [e1, e2]
    have key : w y / w x * ‖g x‖ ^ 2 + w x / w y * ‖g y‖ ^ 2 - 2 * (‖g x‖ * ‖g y‖)
        = (w y * ‖g x‖ - w x * ‖g y‖) ^ 2 / (w x * w y) := by
      field_simp
      ring
    have : 0 ≤ (w y * ‖g x‖ - w x * ‖g y‖) ^ 2 / (w x * w y) :=
      div_nonneg (sq_nonneg _) (mul_pos hx hy).le
    linarith
  · have h0 : ‖g x‖ * ‖g y‖ = 0 := by
      rcases not_and_or.mp h with hx | hy
      · simp [hg x hx]
      · simp [hg y hy]
    rw [h0, mul_zero]
    exact add_nonneg (mul_nonneg (schurRatio_nonneg hw x y) (sq_nonneg _))
      (mul_nonneg (schurRatio_nonneg hw y x) (sq_nonneg _))

lemma schurRatio_eq_indicator {W : Set ℝ} {w : ℝ → ℝ} {x : ℝ} (hx : x ∈ W) (y : ℝ) :
    schurRatio W w x y = W.indicator w y / w x := by
  unfold schurRatio
  by_cases hy : y ∈ W
  · simp [hx, hy]
  · simp [hy]

section Integrals

variable {W : Set ℝ} {w : ℝ → ℝ} {g : ℝ → ℂ}

lemma integrable_normSq (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x => ‖g x‖ ^ 2) := by
  have hs : HasCompactSupport (fun x => ‖g x‖ ^ 2) :=
    hgs.norm.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact (hgc.norm.pow 2).integrable_of_hasCompactSupport hs

lemma integrable_normProd (hgc : Continuous g) (hgs : HasCompactSupport g) (u : ℝ) :
    Integrable (fun x => ‖g x‖ * ‖g (x + u)‖) := by
  have hs : HasCompactSupport (fun x => ‖g x‖ * ‖g (x + u)‖) := hgs.norm.mul_right
  exact (hgc.norm.mul (hgc.comp (continuous_add_const u)).norm).integrable_of_hasCompactSupport hs

lemma integrable_ratio_mul (hw : SchurWeight W w) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (u : ℝ) : Integrable (fun x => schurRatio W w x (x + u) * ‖g x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := schurRatio_le hw
  exact (integrable_normSq hgc hgs).bdd_mul (measurable_schurRatio_shift hw u).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC x (x + u))

/-- One shift: `2 ∫ |g(x)| |g(x+u)| ≤ ∫ r(x,x+u)|g|² + ∫ r(x,x-u)|g|²` (translation invariance). -/
lemma shift_amgm_integral (hw : SchurWeight W w) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ W → g x = 0) (u : ℝ) :
    2 * ∫ x, ‖g x‖ * ‖g (x + u)‖ ≤
      (∫ x, schurRatio W w x (x + u) * ‖g x‖ ^ 2) + ∫ x, schurRatio W w x (x + -u) * ‖g x‖ ^ 2 := by
  have hpos := hw.pos
  -- the translated second integral
  have htr : (∫ x, schurRatio W w (x + u) x * ‖g (x + u)‖ ^ 2)
      = ∫ x, schurRatio W w x (x + -u) * ‖g x‖ ^ 2 := by
    have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun z => schurRatio W w z (z + -u) * ‖g z‖ ^ 2) u
    simpa [add_neg_cancel_right] using this
  have hI1 := integrable_ratio_mul hw hgc hgs u
  have hI2 : Integrable (fun x => schurRatio W w (x + u) x * ‖g (x + u)‖ ^ 2) := by
    have := (integrable_ratio_mul hw hgc hgs (-u)).comp_add_right u
    simpa [add_neg_cancel_right] using this
  rw [← integral_const_mul, ← htr, ← integral_add hI1 hI2]
  refine integral_mono ((integrable_normProd hgc hgs u).const_mul 2) (hI1.add hI2) (fun x => ?_)
  have := amgm_window hpos hgW x (x + u)
  simpa using this

/-- Both shift directions together. -/
lemma two_sided_shift (hw : SchurWeight W w) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ W → g x = 0) (u : ℝ) :
    (∫ x, ‖g x‖ * ‖g (x - u)‖) + (∫ x, ‖g x‖ * ‖g (x + u)‖) ≤
      ∫ x, (schurRatio W w x (x - u) + schurRatio W w x (x + u)) * ‖g x‖ ^ 2 := by
  have h1 := shift_amgm_integral hw hgc hgs hgW u
  have h2 := shift_amgm_integral hw hgc hgs hgW (-u)
  simp only [neg_neg] at h2
  have hm : (fun x => ‖g x‖ * ‖g (x - u)‖) = fun x => ‖g x‖ * ‖g (x + -u)‖ := by
    funext x; rw [sub_eq_add_neg]
  have hr : (fun x => (schurRatio W w x (x - u) + schurRatio W w x (x + u)) * ‖g x‖ ^ 2)
      = fun x => schurRatio W w x (x + -u) * ‖g x‖ ^ 2 + schurRatio W w x (x + u) * ‖g x‖ ^ 2 := by
    funext x; rw [sub_eq_add_neg]; ring
  rw [hm, hr, integral_add (integrable_ratio_mul hw hgc hgs (-u)) (integrable_ratio_mul hw hgc hgs u)]
  linarith

/-- **Continuous Schur test** for a window-compressed positive shift comb. -/
theorem schur_comb (hw : SchurWeight W w) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ W → g x = 0) (ι : Finset ℕ) (c u : ℕ → ℝ) (hc : ∀ n ∈ ι, 0 ≤ c n) (lam : ℝ)
    (hS : ∀ x ∈ W, ∑ n ∈ ι, c n * (W.indicator w (x - u n) + W.indicator w (x + u n)) ≤ lam * w x) :
    ∑ n ∈ ι, c n * ((∫ x, ‖g x‖ * ‖g (x - u n)‖) + ∫ x, ‖g x‖ * ‖g (x + u n)‖)
      ≤ lam * ∫ x, ‖g x‖ ^ 2 := by
  have hpos := hw.pos
  have hIn : ∀ n, Integrable
      (fun x => (schurRatio W w x (x - u n) + schurRatio W w x (x + u n)) * ‖g x‖ ^ 2) := by
    intro n
    have e : (fun x => (schurRatio W w x (x - u n) + schurRatio W w x (x + u n)) * ‖g x‖ ^ 2)
        = fun x => schurRatio W w x (x + -u n) * ‖g x‖ ^ 2 + schurRatio W w x (x + u n) * ‖g x‖ ^ 2 := by
      funext x; rw [sub_eq_add_neg]; ring
    rw [e]
    exact (integrable_ratio_mul hw hgc hgs _).add (integrable_ratio_mul hw hgc hgs _)
  calc ∑ n ∈ ι, c n * ((∫ x, ‖g x‖ * ‖g (x - u n)‖) + ∫ x, ‖g x‖ * ‖g (x + u n)‖)
      ≤ ∑ n ∈ ι, c n * ∫ x, (schurRatio W w x (x - u n) + schurRatio W w x (x + u n)) * ‖g x‖ ^ 2 :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (two_sided_shift hw hgc hgs hgW _) (hc n hn)
    _ = ∫ x, ∑ n ∈ ι, c n * ((schurRatio W w x (x - u n) + schurRatio W w x (x + u n)) * ‖g x‖ ^ 2) := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun n _ => ?_
          rw [integral_const_mul]
        · exact fun n _ => (hIn n).const_mul _
    _ ≤ ∫ x, lam * ‖g x‖ ^ 2 := by
        refine integral_mono (integrable_finsetSum _ fun n _ => (hIn n).const_mul _)
          ((integrable_normSq hgc hgs).const_mul lam) fun x => ?_
        by_cases hx : x ∈ W
        · have hwx := hpos x hx
          have hsum : ∑ n ∈ ι, c n * ((schurRatio W w x (x - u n) + schurRatio W w x (x + u n)) * ‖g x‖ ^ 2)
              = (∑ n ∈ ι, c n * (W.indicator w (x - u n) + W.indicator w (x + u n))) / w x * ‖g x‖ ^ 2 := by
            rw [Finset.sum_div, Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [schurRatio_eq_indicator hx, schurRatio_eq_indicator hx]
            field_simp
          rw [hsum]
          have hle : (∑ n ∈ ι, c n * (W.indicator w (x - u n) + W.indicator w (x + u n))) / w x ≤ lam := by
            rw [div_le_iff₀ hwx]; exact hS x hx
          exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        · simp [hgW x hx]
    _ = lam * ∫ x, ‖g x‖ ^ 2 := integral_const_mul _ _

end Integrals

/-! ## C. The prime side of the explicit formula on a window: form-level comb bound -/

section PrimeSide

open ArithmeticFunction

lemma norm_autocorr_le (g : ℝ → ℂ) (u : ℝ) : ‖autocorr g u‖ ≤ ∫ v, ‖g v‖ * ‖g (v - u)‖ := by
  unfold autocorr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  rw [norm_mul, Complex.norm_conj]

lemma autocorr_eq_zero_of_far {g : ℝ → ℂ} {L : ℝ} (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0)
    {u : ℝ} (hu : 2 * L < |u|) : autocorr g u = 0 := by
  unfold autocorr
  have hz : (fun v => g v * (starRingEnd ℂ) (g (v - u))) = fun _ => (0 : ℂ) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-L) L
    · have hvu : v - u ∉ Set.Icc (-L) L := by
        intro h
        rcases hv with ⟨h1, h2⟩
        rcases h with ⟨h3, h4⟩
        have : |u| ≤ 2 * L := by rw [abs_le]; constructor <;> linarith
        linarith
      simp [hgW _ hvu]
    · simp [hgW v hv]
  rw [hz, integral_zero]

/-- On a window, the prime side of `autocorr g` is a finite sum (`n < N0` with `log N0 > 2L`). -/
lemma primeSide_autocorr_eq_sum {g : ℝ → ℂ} {L : ℝ} (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0)
    (N0 : ℕ) (hN0 : 2 * L < Real.log N0) :
    primeSide (autocorr g) = ∑ n ∈ range N0,
      ((Λ n / Real.sqrt n : ℝ) : ℂ) * (autocorr g (Real.log n) + autocorr g (-Real.log n)) := by
  unfold primeSide
  apply tsum_eq_sum
  intro n hn
  have hnN : N0 ≤ n := by simpa using hn
  have hfar : 2 * L < |Real.log n| := by
    rcases Nat.eq_zero_or_pos N0 with h0 | h0
    · subst h0
      simp at hN0
      exact lt_of_lt_of_le (by linarith) (abs_nonneg _)
    · have hle : Real.log N0 ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hnN)
      exact lt_of_lt_of_le (lt_of_lt_of_le hN0 hle) (le_abs_self _)
  have hfar' : 2 * L < |-Real.log n| := by rwa [abs_neg]
  rw [autocorr_eq_zero_of_far hgW hfar, autocorr_eq_zero_of_far hgW hfar']
  simp

/-- **Form-level comb bound** (THEOREM, kernel-checked): a Schur weight for the window-compressed
comb `∑ Λ(n)/√n (τ_{log n} + τ_{log n}^*)` bounds the prime side of the explicit formula on every
autocorrelation of a test supported in the window. -/
theorem primeSide_autocorr_le {L : ℝ} {w : ℝ → ℝ} (hw : SchurWeight (Set.Icc (-L) L) w)
    (N0 : ℕ) (hN0 : 2 * L < Real.log N0) (lam : ℝ)
    (hS : ∀ x ∈ Set.Icc (-L) L, ∑ n ∈ range N0, (Λ n / Real.sqrt n) *
        ((Set.Icc (-L) L).indicator w (x - Real.log n) + (Set.Icc (-L) L).indicator w (x + Real.log n))
        ≤ lam * w x)
    {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ lam * ∫ x, ‖g x‖ ^ 2 := by
  rw [primeSide_autocorr_eq_sum hgW N0 hN0]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (schur_comb hw hgc hgs hgW (range N0) (fun n => Λ n / Real.sqrt n)
    (fun n => Real.log n) (fun n _ => div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)) lam hS)
  refine Finset.sum_le_sum fun n _ => ?_
  have hc : 0 ≤ Λ n / Real.sqrt n := div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine (norm_add_le _ _).trans (add_le_add (norm_autocorr_le g _) ?_)
  have := norm_autocorr_le g (-Real.log n)
  simpa [sub_neg_eq_add] using this

/-- Modulation by `e^{irx}` multiplies the autocorrelation by `e^{iru}`: on the prime side this is
the comb twisted by the frequency `r` (the symbol `P_L(t + r)`). -/
lemma autocorr_modulate (g : ℝ → ℂ) (r u : ℝ) :
    autocorr (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x) u
      = Complex.exp (((r * u : ℝ) : ℂ) * I) * autocorr g u := by
  unfold autocorr
  rw [← integral_const_mul]
  congr 1
  funext v
  have hc : (starRingEnd ℂ) (Complex.exp (((r * (v - u) : ℝ) : ℂ) * I))
      = Complex.exp (-(((r * (v - u) : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hexp : Complex.exp (((r * v : ℝ) : ℂ) * I) * Complex.exp (-(((r * (v - u) : ℝ) : ℂ) * I))
      = Complex.exp (((r * u : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [map_mul, hc, ← hexp]
  ring

lemma primeSide_autocorr_modulate (g : ℝ → ℂ) (r : ℝ) :
    primeSide (autocorr (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          (Complex.exp (((r * Real.log n : ℝ) : ℂ) * I) * autocorr g (Real.log n)
            + Complex.exp (((r * -Real.log n : ℝ) : ℂ) * I) * autocorr g (-Real.log n)) := by
  unfold primeSide
  congr 1
  funext n
  rw [autocorr_modulate, autocorr_modulate]

/-- **Twist invariance** (uses `Λ ≥ 0` through `schur_comb`): the same constant bounds the prime
side for every frequency twist, i.e. every high-frequency Rayleigh quotient of the comb. -/
theorem primeSide_autocorr_twist_le {L : ℝ} {w : ℝ → ℝ} (hw : SchurWeight (Set.Icc (-L) L) w)
    (N0 : ℕ) (hN0 : 2 * L < Real.log N0) (lam : ℝ)
    (hS : ∀ x ∈ Set.Icc (-L) L, ∑ n ∈ range N0, (Λ n / Real.sqrt n) *
        ((Set.Icc (-L) L).indicator w (x - Real.log n) + (Set.Icc (-L) L).indicator w (x + Real.log n))
        ≤ lam * w x)
    {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0) (r : ℝ) :
    ‖primeSide (autocorr (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x))‖
      ≤ lam * ∫ x, ‖g x‖ ^ 2 := by
  have hn : ∀ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ = ‖g x‖ := by
    intro x
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hc : Continuous (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x) := by
    fun_prop
  have hs : HasCompactSupport (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x) :=
    hgs.mul_left
  have hW : ∀ x, x ∉ Set.Icc (-L) L → Complex.exp (((r * x : ℝ) : ℂ) * I) * g x = 0 := by
    intro x hx; simp [hgW x hx]
  have h := primeSide_autocorr_le hw N0 hN0 lam hS hc hs hW
  have hint : (∫ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ ^ 2) = ∫ x, ‖g x‖ ^ 2 := by
    congr 1
    funext x
    rw [hn x]
  rw [hint] at h
  exact h

/-- Corollary on the Weil functional (THEOREM, kernel-checked): the prime side can be replaced by the
form-level constant. `Re W(g * g~) ≥ Re Arch(g * g~) - lam ‖g‖²` for every smooth test supported in
the window. -/
theorem weilForm_autocorr_ge {L : ℝ} {w : ℝ → ℝ} (hw : SchurWeight (Set.Icc (-L) L) w)
    (N0 : ℕ) (hN0 : 2 * L < Real.log N0) (lam : ℝ)
    (hS : ∀ x ∈ Set.Icc (-L) L, ∑ n ∈ range N0, (Λ n / Real.sqrt n) *
        ((Set.Icc (-L) L).indicator w (x - Real.log n) + (Set.Icc (-L) L).indicator w (x + Real.log n))
        ≤ lam * w x)
    {g : ℝ → ℂ} (hg : IsWeilTest g) (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0) :
    (archSide (autocorr g)).re - lam * ∫ x, ‖g x‖ ^ 2 ≤ (weilForm (autocorr g)).re := by
  have h := primeSide_autocorr_le hw N0 hN0 lam hS hg.1.continuous hg.2 hgW
  have hre : (primeSide (autocorr g)).re ≤ ‖primeSide (autocorr g)‖ := Complex.re_le_norm _
  unfold weilForm
  rw [Complex.sub_re]
  linarith

end PrimeSide

/-! ## D. Exact-integer certificate machinery (kernel-evaluated checker + real-number soundness) -/

section Checker

/-- Complete binary tree of natural-number weights: `O(depth)` lookups under kernel reduction. -/
inductive WTree where
  | leaf : ℕ → WTree
  | node : WTree → WTree → WTree

/-- `WTree.get d t i`: the `i`-th leaf (prefix layout) of a tree of depth `d`. -/
def WTree.get : ℕ → WTree → ℕ → ℕ
  | _, .leaf v, _ => v
  | 0, .node _ _, _ => 0
  | d + 1, .node l r, i => if i < 2 ^ d then WTree.get d l i else WTree.get d r (i - 2 ^ d)

/-- `maxR f lo len = max_{lo ≤ j < lo + len} f j` (and `0` for an empty range). -/
def maxR (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | lo, len + 1 => max (f lo) (maxR f (lo + 1) len)

lemma le_maxR (f : ℕ → ℕ) : ∀ (len lo j : ℕ), lo ≤ j → j < lo + len → f j ≤ maxR f lo len
  | 0, lo, j, h1, h2 => by omega
  | len + 1, lo, j, h1, h2 => by
    unfold maxR
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (le_maxR f len (lo + 1) j h (by omega)) (le_max_right _ _)

/-- Largest weight the shifted point `x - log n` can see, `x` in cell `k`, `log n ∈ [A q, B q]`. -/
def mMinus (f : ℕ → ℕ) (N H k A B : ℕ) : ℕ :=
  if (k + 1) * H < A then 0
  else maxR f ((k * H - B) / H) (min (((k + 1) * H - A) / H) (N - 1) + 1 - (k * H - B) / H)

/-- Largest weight the shifted point `x + log n` can see. -/
def mPlus (f : ℕ → ℕ) (N H k A B : ℕ) : ℕ :=
  if N < (k * H + A) / H then 0
  else maxR f (min ((k * H + A) / H) (N - 1))
    (min ((k * H + H + B) / H) (N - 1) + 1 - min ((k * H + A) / H) (N - 1))

/-- Row sum of the integer Schur test; entries are `(n, C, A, B)`. -/
def rowSum (f : ℕ → ℕ) (N H : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, C, A, B) :: ds, k => C * (mMinus f N H k A B + mPlus f N H k A B) + rowSum f N H ds k

/-- The whole certificate check, rows `0 .. K-1`. -/
def checkRows (f : ℕ → ℕ) (N H Lam Wmax : ℕ) (ds : List (ℕ × ℕ × ℕ × ℕ)) : ℕ → Bool
  | 0 => true
  | k + 1 => (decide (0 < f k) && decide (f k ≤ Wmax) && decide (rowSum f N H ds k ≤ Lam * f k))
      && checkRows f N H Lam Wmax ds k

lemma checkRows_sound {f : ℕ → ℕ} {N H Lam Wmax : ℕ} {ds : List (ℕ × ℕ × ℕ × ℕ)} :
    ∀ K, checkRows f N H Lam Wmax ds K = true →
      ∀ k < K, 0 < f k ∧ f k ≤ Wmax ∧ rowSum f N H ds k ≤ Lam * f k
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | K + 1, h, k, hk => by
    simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · exact checkRows_sound K h.2 k hk'
    · subst hk'; exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

end Checker

section CellGeometry

/-- Cell of `x` in the uniform grid `x0 + h ℕ` with `N` cells (last cell closed). -/
def cellIdx (x0 h : ℝ) (N : ℕ) (x : ℝ) : ℕ := min ⌊(x - x0) / h⌋₊ (N - 1)

/-- Step weight attached to integer weights `f`. -/
def stepW (f : ℕ → ℕ) (x0 h : ℝ) (N : ℕ) (x : ℝ) : ℝ := (f (cellIdx x0 h N x) : ℝ)

variable {x0 h : ℝ} {N : ℕ}

lemma cellIdx_le_pred (x : ℝ) : cellIdx x0 h N x ≤ N - 1 := min_le_right _ _

lemma cell_bounds (hh : 0 < h) (hN : 1 ≤ N) {x : ℝ} (hx : x ∈ Set.Icc x0 (x0 + N * h)) :
    (cellIdx x0 h N x : ℝ) ≤ (x - x0) / h ∧ (x - x0) / h ≤ (cellIdx x0 h N x : ℝ) + 1 := by
  have ht0 : 0 ≤ (x - x0) / h := div_nonneg (by linarith [hx.1]) hh.le
  have htN : (x - x0) / h ≤ N := by
    rw [div_le_iff₀ hh]; linarith [hx.2]
  have hfl := Nat.floor_le ht0
  have hlt := Nat.lt_floor_add_one ((x - x0) / h)
  unfold cellIdx
  rcases le_or_gt ⌊(x - x0) / h⌋₊ (N - 1) with hc | hc
  · rw [min_eq_left hc]; exact ⟨hfl, hlt.le⟩
  · rw [min_eq_right hc.le]
    have hNfl : (N : ℝ) ≤ ⌊(x - x0) / h⌋₊ := by exact_mod_cast (by omega : N ≤ ⌊(x - x0) / h⌋₊)
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; simp
    rw [hcast]
    constructor <;> linarith

lemma le_cellIdx {lo : ℕ} {x : ℝ} (h1 : (lo : ℝ) ≤ (x - x0) / h) (h2 : lo ≤ N - 1) :
    lo ≤ cellIdx x0 h N x :=
  le_min (Nat.le_floor h1) h2

lemma cellIdx_le_of {a H : ℕ} {x : ℝ} (h1 : (x - x0) / h ≤ (a : ℝ) / H) :
    cellIdx x0 h N x ≤ a / H := by
  refine le_trans (min_le_left _ _) ?_
  rw [← Nat.floor_div_eq_div (K := ℝ) a H]
  exact Nat.floor_le_floor h1

end CellGeometry

section Soundness

variable {x0 h q : ℝ} {N H : ℕ}

lemma mMinus_sound (f : ℕ → ℕ) (hh : 0 < h) (hN : 1 ≤ N) (hH : 0 < H) (hq : q * H = h)
    {x : ℝ} (hx : x ∈ Set.Icc x0 (x0 + N * h)) {u : ℝ} {A B : ℕ}
    (hA : (A : ℝ) * q ≤ u) (hB : u ≤ (B : ℝ) * q) :
    (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x - u)
      ≤ (mMinus f N H (cellIdx x0 h N x) A B : ℝ) := by
  by_cases hy : x - u ∈ Set.Icc x0 (x0 + N * h)
  · rw [Set.indicator_of_mem hy]
    set k := cellIdx x0 h N x with hk
    obtain ⟨hk1, hk2⟩ := cell_bounds hh hN hx
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hq0 : q = h / H := by field_simp; linarith
    -- u / h ∈ [A / H, B / H]
    have huA : (A : ℝ) / H ≤ u / h := by
      rw [div_le_div_iff₀ hHr hh]; rw [hq0] at hA
      have := mul_le_mul_of_nonneg_right hA hHr.le
      field_simp at this ⊢; nlinarith
    have huB : u / h ≤ (B : ℝ) / H := by
      rw [div_le_div_iff₀ hh hHr]; rw [hq0] at hB
      have := mul_le_mul_of_nonneg_right hB hHr.le
      field_simp at this ⊢; nlinarith
    have hs : (x - u - x0) / h = (x - x0) / h - u / h := by ring
    have hs0 : 0 ≤ (x - u - x0) / h := div_nonneg (by linarith [hy.1]) hh.le
    -- the branch condition
    have hAk : A ≤ (k + 1) * H := by
      have h1 : (A : ℝ) / H ≤ (k : ℝ) + 1 := by linarith
      have h2 : (A : ℝ) ≤ ((k : ℝ) + 1) * H := by rwa [div_le_iff₀ hHr] at h1
      exact_mod_cast h2
    unfold mMinus
    rw [if_neg (by omega)]
    set j := cellIdx x0 h N (x - u)
    -- lower end of the range
    have hlo : (k * H - B) / H ≤ j := by
      apply le_cellIdx
      · rcases le_or_gt B (k * H) with hBk | hBk
        · have e : (((k * H - B : ℕ) : ℝ)) = (k : ℝ) * H - B := by
            rw [Nat.cast_sub hBk]; push_cast; ring
          calc (((k * H - B) / H : ℕ) : ℝ) ≤ ((k * H - B : ℕ) : ℝ) / H := Nat.cast_div_le
            _ = (k : ℝ) - B / H := by rw [e]; field_simp
            _ ≤ (x - u - x0) / h := by rw [hs]; linarith
        · have : k * H - B = 0 := by omega
          rw [this, Nat.zero_div]; simpa using hs0
      · have : (k * H - B) / H ≤ k := by
          calc (k * H - B) / H ≤ k * H / H := Nat.div_le_div_right (Nat.sub_le _ _)
            _ = k := Nat.mul_div_cancel k hH
        exact le_trans this (cellIdx_le_pred x)
    -- upper end of the range
    have hhi : j ≤ min (((k + 1) * H - A) / H) (N - 1) := by
      refine le_min ?_ (cellIdx_le_pred _)
      apply cellIdx_le_of
      have e : (((k + 1) * H - A : ℕ) : ℝ) = ((k : ℝ) + 1) * H - A := by
        rw [Nat.cast_sub hAk]; push_cast; ring
      rw [e, hs]
      have : (((k : ℝ) + 1) * H - A) / H = (k : ℝ) + 1 - A / H := by field_simp
      rw [this]; linarith
    have hmax := le_maxR f (min (((k + 1) * H - A) / H) (N - 1) + 1 - (k * H - B) / H)
      ((k * H - B) / H) j hlo (by omega)
    unfold stepW
    exact_mod_cast hmax
  · rw [Set.indicator_of_notMem hy]; exact Nat.cast_nonneg _

lemma mPlus_sound (f : ℕ → ℕ) (hh : 0 < h) (hN : 1 ≤ N) (hH : 0 < H) (hq : q * H = h)
    {x : ℝ} (hx : x ∈ Set.Icc x0 (x0 + N * h)) {u : ℝ} {A B : ℕ}
    (hA : (A : ℝ) * q ≤ u) (hB : u ≤ (B : ℝ) * q) :
    (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x + u)
      ≤ (mPlus f N H (cellIdx x0 h N x) A B : ℝ) := by
  by_cases hy : x + u ∈ Set.Icc x0 (x0 + N * h)
  · rw [Set.indicator_of_mem hy]
    set k := cellIdx x0 h N x with hk
    obtain ⟨hk1, hk2⟩ := cell_bounds hh hN hx
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hq0 : q = h / H := by field_simp; linarith
    have huA : (A : ℝ) / H ≤ u / h := by
      rw [div_le_div_iff₀ hHr hh]; rw [hq0] at hA
      have := mul_le_mul_of_nonneg_right hA hHr.le
      field_simp at this ⊢; nlinarith
    have huB : u / h ≤ (B : ℝ) / H := by
      rw [div_le_div_iff₀ hh hHr]; rw [hq0] at hB
      have := mul_le_mul_of_nonneg_right hB hHr.le
      field_simp at this ⊢; nlinarith
    have hs : (x + u - x0) / h = (x - x0) / h + u / h := by ring
    have hsN : (x + u - x0) / h ≤ N := by
      rw [div_le_iff₀ hh]; linarith [hy.2]
    -- lower index lo0 = (kH + A)/H satisfies lo0 ≤ s
    have hlo0 : (((k * H + A) / H : ℕ) : ℝ) ≤ (x + u - x0) / h := by
      calc (((k * H + A) / H : ℕ) : ℝ) ≤ ((k * H + A : ℕ) : ℝ) / H := Nat.cast_div_le
        _ = (k : ℝ) + A / H := by push_cast; field_simp
        _ ≤ (x + u - x0) / h := by rw [hs]; linarith
    have hlo0N : (k * H + A) / H ≤ N := by
      have : (((k * H + A) / H : ℕ) : ℝ) ≤ N := le_trans hlo0 hsN
      exact_mod_cast this
    unfold mPlus
    rw [if_neg (by omega)]
    set j := cellIdx x0 h N (x + u)
    have hlo : min ((k * H + A) / H) (N - 1) ≤ j :=
      min_le_min_right _ (Nat.le_floor hlo0)
    have hhi : j ≤ min ((k * H + H + B) / H) (N - 1) := by
      refine le_min ?_ (cellIdx_le_pred _)
      apply cellIdx_le_of
      rw [hs]
      have : ((k * H + H + B : ℕ) : ℝ) / H = (k : ℝ) + 1 + B / H := by push_cast; field_simp
      rw [this]; linarith
    have hmax := le_maxR f (min ((k * H + H + B) / H) (N - 1) + 1 - min ((k * H + A) / H) (N - 1))
      (min ((k * H + A) / H) (N - 1)) j hlo (by omega)
    unfold stepW
    exact_mod_cast hmax
  · rw [Set.indicator_of_notMem hy]; exact Nat.cast_nonneg _

end Soundness

section Assembly

open ArithmeticFunction

/-- Per-entry facts for `e = (n, C, A, B)`: `log n ∈ [A q, B q]` and `Λ(n)/√n ≤ C/S`. -/
def EntryOK (q S : ℝ) (e : ℕ × ℕ × ℕ × ℕ) : Prop :=
  ((e.2.2.1 : ℝ) * q ≤ Real.log e.1 ∧ Real.log e.1 ≤ (e.2.2.2 : ℝ) * q) ∧
    Λ e.1 / Real.sqrt e.1 ≤ (e.2.1 : ℝ) / S

variable {x0 h q S : ℝ} {N H : ℕ}

lemma listSum_le_rowSum (f : ℕ → ℕ) (hh : 0 < h) (hN : 1 ≤ N) (hH : 0 < H) (hq : q * H = h)
    (hS : 0 < S) {x : ℝ} (hx : x ∈ Set.Icc x0 (x0 + N * h)) :
    ∀ ds : List (ℕ × ℕ × ℕ × ℕ), (∀ e ∈ ds, EntryOK q S e) →
      (ds.map (fun e => Λ e.1 / Real.sqrt e.1 *
        ((Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x - Real.log e.1)
          + (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x + Real.log e.1)))).sum
        ≤ (rowSum f N H ds (cellIdx x0 h N x) : ℝ) / S
  | [], _ => by simp [rowSum]
  | (n, C, A, B) :: ds, hds => by
    have he := hds (n, C, A, B) List.mem_cons_self
    have ih := listSum_le_rowSum f hh hN hH hq hS hx ds
      (fun e he' => hds e (List.mem_cons_of_mem _ he'))
    simp only [List.map_cons, List.sum_cons, rowSum]
    push_cast
    obtain ⟨⟨hA, hB⟩, hC⟩ := he
    have hm := mMinus_sound f hh hN hH hq hx hA hB
    have hp := mPlus_sound f hh hN hH hq hx hA hB
    have hi0 : 0 ≤ (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x - Real.log n)
        + (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x + Real.log n) :=
      add_nonneg (Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _)
    have key := mul_le_mul hC (add_le_add hm hp) hi0 (div_nonneg (Nat.cast_nonneg C) hS.le)
    simp only at key
    rw [add_div]
    have e2 : (C : ℝ) / S * ((mMinus f N H (cellIdx x0 h N x) A B : ℝ)
        + (mPlus f N H (cellIdx x0 h N x) A B : ℝ))
        = (C : ℝ) * ((mMinus f N H (cellIdx x0 h N x) A B : ℝ)
          + (mPlus f N H (cellIdx x0 h N x) A B : ℝ)) / S := by ring
    rw [e2] at key
    linarith

/-- The checker's output implies the pointwise Schur inequality of `primeSide_autocorr_le`. -/
theorem schur_of_check (f : ℕ → ℕ) (hh : 0 < h) (hN : 1 ≤ N) (hH : 0 < H) (hq : q * H = h)
    (hS : 0 < S) (Lam Wmax : ℕ) (ds : List (ℕ × ℕ × ℕ × ℕ))
    (hcheck : checkRows f N H Lam Wmax ds N = true) (hent : ∀ e ∈ ds, EntryOK q S e)
    (N0 : ℕ) (hnodup : (ds.map Prod.fst).Nodup) (hsub : ∀ n ∈ ds.map Prod.fst, n < N0)
    (hzero : ∀ n < N0, n ∉ ds.map Prod.fst → Λ n = 0)
    {x : ℝ} (hx : x ∈ Set.Icc x0 (x0 + N * h)) :
    ∑ n ∈ range N0, Λ n / Real.sqrt n *
        ((Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x - Real.log n)
          + (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x + Real.log n))
      ≤ ((Lam : ℝ) / S) * stepW f x0 h N x := by
  set F : ℕ → ℝ := fun n => Λ n / Real.sqrt n *
    ((Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x - Real.log n)
      + (Set.Icc x0 (x0 + N * h)).indicator (stepW f x0 h N) (x + Real.log n)) with hF
  have hsubset : (ds.map Prod.fst).toFinset ⊆ range N0 := by
    intro n hn
    rw [List.mem_toFinset] at hn
    exact Finset.mem_range.mpr (hsub n hn)
  have h1 : ∑ n ∈ range N0, F n = ∑ n ∈ (ds.map Prod.fst).toFinset, F n := by
    refine (Finset.sum_subset hsubset fun n hn hnot => ?_).symm
    rw [List.mem_toFinset] at hnot
    simp [hF, hzero n (Finset.mem_range.mp hn) hnot]
  have h2 : ∑ n ∈ (ds.map Prod.fst).toFinset, F n = (ds.map (fun e => F e.1)).sum := by
    rw [List.sum_toFinset F hnodup, List.map_map]
    rfl
  rw [h1, h2]
  have hk : cellIdx x0 h N x < N := by
    have := cellIdx_le_pred (x0 := x0) (h := h) (N := N) x; omega
  obtain ⟨-, -, hrow⟩ := checkRows_sound N hcheck _ hk
  have hrowR : (rowSum f N H ds (cellIdx x0 h N x) : ℝ) ≤ (Lam : ℝ) * f (cellIdx x0 h N x) := by
    exact_mod_cast hrow
  calc (ds.map (fun e => F e.1)).sum ≤ (rowSum f N H ds (cellIdx x0 h N x) : ℝ) / S :=
        listSum_le_rowSum f hh hN hH hq hS hx ds hent
    _ ≤ (Lam : ℝ) * f (cellIdx x0 h N x) / S := div_le_div_of_nonneg_right hrowR hS.le
    _ = ((Lam : ℝ) / S) * stepW f x0 h N x := by unfold stepW; ring

lemma schurWeight_stepW (f : ℕ → ℕ) (hN : 1 ≤ N) {Lam Wmax : ℕ} {ds : List (ℕ × ℕ × ℕ × ℕ)}
    (hcheck : checkRows f N H Lam Wmax ds N = true) :
    SchurWeight (Set.Icc x0 (x0 + N * h)) (stepW f x0 h N) where
  meas_W := measurableSet_Icc
  meas_w := by
    have : stepW f x0 h N = (fun m : ℕ => (f (min m (N - 1)) : ℝ)) ∘ (fun x => ⌊(x - x0) / h⌋₊) := by
      funext x; rfl
    rw [this]
    exact measurable_from_nat.comp (Nat.measurable_floor.comp ((measurable_id.sub_const x0).div_const h))
  lower := ⟨1, one_pos, fun x _ => by
    have hk : cellIdx x0 h N x < N := by
      have := cellIdx_le_pred (x0 := x0) (h := h) (N := N) x; omega
    have := (checkRows_sound N hcheck _ hk).1
    unfold stepW
    exact_mod_cast this⟩
  upper := ⟨Wmax, fun x _ => by
    have hk : cellIdx x0 h N x < N := by
      have := cellIdx_le_pred (x0 := x0) (h := h) (N := N) x; omega
    have := (checkRows_sound N hcheck _ hk).2.1
    unfold stepW
    exact_mod_cast this⟩

/-- **Certificate-to-theorem bridge**: a passing integer check plus per-entry facts gives the
form-level comb bound on the Weil prime side for every test supported in `[-L, L]`. -/
theorem primeSide_autocorr_le_of_check {L h q S : ℝ} (f : ℕ → ℕ) (N H Lam Wmax N0 : ℕ)
    (ds : List (ℕ × ℕ × ℕ × ℕ)) (hh : 0 < h) (hN : 1 ≤ N) (hH : 0 < H) (hq : q * H = h)
    (hS : 0 < S) (hwin : -L + N * h = L)
    (hcheck : checkRows f N H Lam Wmax ds N = true) (hent : ∀ e ∈ ds, EntryOK q S e)
    (hnodup : (ds.map Prod.fst).Nodup) (hsub : ∀ n ∈ ds.map Prod.fst, n < N0)
    (hzero : ∀ n < N0, n ∉ ds.map Prod.fst → Λ n = 0) (hN0 : 2 * L < Real.log N0)
    {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-L) L → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ ((Lam : ℝ) / S) * ∫ x, ‖g x‖ ^ 2 := by
  have hWeq : Set.Icc (-L) (-L + N * h) = Set.Icc (-L) L := by rw [hwin]
  have hw := schurWeight_stepW (x0 := -L) (h := h) f hN hcheck
  rw [hWeq] at hw
  refine primeSide_autocorr_le hw N0 hN0 _ (fun x hx => ?_) hgc hgs hgW
  have hx' : x ∈ Set.Icc (-L) (-L + N * h) := by rw [hWeq]; exact hx
  have := schur_of_check (x0 := -L) f hh hN hH hq hS Lam Wmax ds hcheck hent N0 hnodup hsub hzero hx'
  rw [hWeq] at this
  exact this

end Assembly

