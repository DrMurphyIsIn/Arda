/-
  Crux2_verified_window.lean (rvm_bridge island) -- crux2 lens "verified-window": the FORM-LEVEL
  comb constant for the Weil explicit formula on a fixed window, kernel-certified at L' = 2.3, and the
  gluing skeleton "verified zeros below T + window arithmetic above T => almost-positivity".

  conjecture1_proved = False.  Nothing here proves, reduces, or is equivalent to RH.  Everything is
  about a FIXED window [-L', L'] (Weil positivity for all windows is RH; for one window it is not).

  Checked by: cd telperion/examples/rvm_bridge/lean &&
    leanlock.sh lake env lean Crux/Crux2_verified_window.lean
  (Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 @ fbdc36bb).  No `sorry`, no `admit`, no
  `native_decide`, no `opaque`, no new `axiom`.  The certificate is evaluated by the KERNEL
  (`decide +kernel`, pure `Nat` arithmetic).  `#print axioms` at the end: only propext,
  Classical.choice, Quot.sound.

  CONSUMED (unconditional on this island): RvMBridge4.limit_explicit_formula (the E8 node: Weil /
  Guinand explicit formula for smooth compactly supported tests), RvMBridge4.zeroMult_eq_zero_of_
  not_nontrivial, RvMBridge5.isWeilTest_autocorr, RvMBridge5.weilKernel_autocorr_line; Mathlib's
  Real.log_two_gt_d9 / lt_d9, Real.abs_log_sub_add_sum_range_le, ArithmeticFunction.vonMangoldt.

  WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
  (A) `schur_twist_bound`: the finite core (discrete Schur test with entrywise domination), ported
      from the idea-stage CombSchur.lean.
  (B) `schur_comb`: continuous Schur / Collatz-Wielandt test for a window-compressed positive shift
      comb:  if w > 0 on W and  Σ_n c_n (1_W w(x - u_n) + 1_W w(x + u_n)) <= lam w(x)  on W, then
        Σ_n c_n (∫|g(x)||g(x - u_n)| + ∫|g(x)||g(x + u_n)|) <= lam ∫|g|²   (g continuous, supp in W).
  (C) `primeSide_autocorr_le`: the prime side of the E8 explicit formula on g⋆g~ is bounded by the
      form-level constant:  ‖Σ_n Λ(n)/√n (g⋆g~(log n) + g⋆g~(-log n))‖ <= lam ‖g‖².  The triangle
      inequality |∫ g(v) conj g(v - u)| <= ∫|g(v)||g(v - u)| plus Λ >= 0 is the entrywise domination:
      `primeSide_autocorr_twist_le` gives the SAME bound for every twist g ↦ e^{irx} g, whose prime
      side is the comb twisted by e^{±ir log n} (`primeSide_autocorr_modulate`), i.e. every
      high-frequency Rayleigh quotient of the comb symbol P(t + r).
  (D) An exact-integer certificate (920 cells, 35 prime powers n < 100, rigorous rational enclosures
      of log p for p <= 97 from Mathlib's log 2 bounds and the log series) checked by the kernel:
        `primeSide_autocorr_le_cert`: for every continuous compactly supported g vanishing off
        [-2.3, 2.3],  ‖primeSide(g⋆g~)‖ <= 11.161373010 ‖g‖².
      `combMass_gt_three_lam`: 3 * 11.161373010 < Σ_{n<100} 2Λ(n)/√n (the pointwise comb constant
      A_{2.3} ≈ 33.79 = sup_t P_{2.3}(t), the constant of every pointwise-envelope certificate).
      `weilForm_autocorr_ge_cert`: Re W(g⋆g~) >= Re Arch(g⋆g~) - 11.161373 ‖g‖² on that window.
  (F) `weil_almost_pos_of_glue` / `weil_almost_pos_cert`: the gluing of Theorem 2 on the real E8
      explicit formula: with Gφ := g⋆g~ - gH⋆gH~, if |ĝH| <= |ĝ| on R, every nontrivial zero with
      |Im| <= T is on the line, the unverified-zero tail of Gφ is at most E₁, and Re Arch(gH⋆gH~) >=
      lam ‖gH‖² - E₂, then Re W(g⋆g~) >= -(E₁ + E₂).

  WHAT IT DOES NOT ESTABLISH:
  * No RH progress; no exact positivity at any window (only the prime-side constant and the gluing).
  * The numerical instance of Theorem 2 (with the constant certified here: λ_min(Q_L) >= -10^-997
    for every L <= 2.25 at T = 640000; research/crux2_verified-window/README.md) is NOT in this
    file: its three analytic inputs (the multiplier K = 1_{[-T_m,T_m]} * Fejér^m and its tail
    bounds, the digamma envelope and leakage below R, Trudgian's explicit S(t)) are paper proofs,
    and the zero hypothesis is the Arb-conditional AllZeros_h640000 of the li_positivity island
    (a different toolchain; islands compose at registry level, not by import).
    `weil_almost_pos_cert` takes exactly these as named hypotheses.
  * The certified 11.161373 is an UPPER bound; the true window norm A_win(2.3) is >= 11.0586
    (Galerkin, floating point, not kernel-checked).  Sharpness of A_win at high frequency
    (Kronecker) is a paper proof, not formalized.
  * The Fourier/Plancherel identity (1/2π)∫|ĝ|² P(t) dt = primeSide(g⋆g~) is used only to READ the
    result in frequency language; every statement here is in x-space on the island's own vocabulary.
  * Davenport-Heilbronn: signed coefficients break the Λ >= 0 domination; the theorems in (B) hold
    with |c_n| but the twisted supremum then genuinely exceeds the untwisted norm (numerical negative
    control in the research README).
-/
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



section Instance

open ArithmeticFunction

/-- Per-entry facts for a prime power `n = p^k` from an enclosure of `log p` and a lower bound `s ≤ √n`. -/
lemma entryOK_of {q S : ℝ} {n p k C A B : ℕ} {lo hi s : ℝ}
    (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (hlog : lo < Real.log p ∧ Real.log p < hi)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ (n : ℝ))
    (hA : (A : ℝ) * q ≤ k * lo) (hB : (k : ℝ) * hi ≤ (B : ℝ) * q) (hC : hi / s ≤ (C : ℝ) / S) :
    EntryOK q S (n, C, A, B) := by
  subst hn
  have hΛ : Λ (p ^ k) = Real.log p := by rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  have hlogn : Real.log (((p ^ k : ℕ) : ℝ)) = k * Real.log p := by push_cast; rw [Real.log_pow]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hlogp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (A : ℝ) * q ≤ Real.log (((p ^ k : ℕ) : ℝ))
    rw [hlogn]; nlinarith [hlog.1]
  · show Real.log (((p ^ k : ℕ) : ℝ)) ≤ (B : ℝ) * q
    rw [hlogn]; nlinarith [hlog.2]
  · show Λ (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ (C : ℝ) / S
    rw [hΛ]
    have hsq : s ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.le_sqrt_of_sq_le hs
    have hsqrt0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := lt_of_lt_of_le hs0 hsq
    have hhi0 : 0 ≤ hi := le_trans hlogp0.le hlog.2.le
    calc Real.log p / Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ hi / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hlog.2.le hsqrt0.le
      _ ≤ hi / s := div_le_div_of_nonneg_left hhi0 hs0 hsq
      _ ≤ (C : ℝ) / S := hC

/-- Lower bound `D / S ≤ 2 Λ(n) / √n` for a prime power `n = p^k` (used only for the comparison with
the pointwise comb mass). -/
lemma entryLow_of {S : ℝ} {n p k D : ℕ} {lo s : ℝ}
    (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (hlog : lo < Real.log p) (hlo : 0 ≤ lo) (hs0 : 0 < s) (hs : (n : ℝ) ≤ s ^ 2)
    (hD : (D : ℝ) / S ≤ 2 * lo / s) :
    (D : ℝ) / S ≤ 2 * Λ n / Real.sqrt n := by
  subst hn
  rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  have hsq : Real.sqrt ((p ^ k : ℕ) : ℝ) ≤ s := by
    rw [Real.sqrt_le_left hs0.le]; exact hs
  have hsqrt0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr; exact_mod_cast pow_pos hp.pos k
  calc (D : ℝ) / S ≤ 2 * lo / s := hD
    _ ≤ 2 * lo / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hsqrt0 hsq
    _ ≤ 2 * Real.log p / Real.sqrt ((p ^ k : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hsqrt0.le

/-- `Λ n = 0` when `n = a b` with coprime `a, b > 1` (so `n` is not a prime power). -/
lemma vonMangoldt_eq_zero_of_coprime {n : ℕ} (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hab : Nat.Coprime a b) (hn : n = a * b) : Λ n = 0 := by
  rw [vonMangoldt_eq_zero_iff]
  intro hpp
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, k, hp, -, hpk⟩ := hpp
  have hadvd : a ∣ p ^ k := by rw [hpk, hn]; exact Dvd.intro b rfl
  have hbdvd : b ∣ p ^ k := by rw [hpk, hn]; exact Dvd.intro_left a rfl
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hadvd
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hbdvd
  have hi0 : i ≠ 0 := by rintro rfl; simp at ha
  have hj0 : j ≠ 0 := by rintro rfl; simp at hb
  have hdvd : p ∣ Nat.gcd (p ^ i) (p ^ j) := Nat.dvd_gcd (dvd_pow_self p hi0) (dvd_pow_self p hj0)
  have hg : Nat.gcd (p ^ i) (p ^ j) = 1 := hab
  rw [hg] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- `log 2` from Mathlib's `Real.log_two_gt_d9`, `Real.log_two_lt_d9`. -/
lemma log2_bounds : (6931471803 / 10000000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (108304247 / 156250000 : ℝ) := by
  constructor
  · have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  · have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma log3_bounds : (274653072037 / 250000000000 : ℝ) < Real.log 3 ∧ Real.log 3 < (1098612289149 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  have hm : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = ((2 : ℝ) ^ 2) by norm_num, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 4)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 21
  have h1 : Real.log (1 - (1 : ℝ) / 4) = Real.log 3 - Real.log 4 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log5_bounds : (1609437911653 / 1000000000000 : ℝ) < Real.log 5 ∧ Real.log 5 < (402359478289 / 250000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (6 : ℝ) = 1 * Real.log 2 + 1 * Real.log 3 := by
    rw [show (6 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 6)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 16
  have h1 : Real.log (1 - (1 : ℝ) / 6) = Real.log 5 - Real.log 6 := by
    rw [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 6 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log7_bounds : (77836405931 / 40000000000 : ℝ) < Real.log 7 ∧ Real.log 7 < (121619384361 / 62500000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  have hm : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = ((2 : ℝ) ^ 3) by norm_num, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 8)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 14
  have h1 : Real.log (1 - (1 : ℝ) / 8) = Real.log 7 - Real.log 8 := by
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 8 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log11_bounds : (1198947635879 / 500000000000 : ℝ) < Real.log 11 ∧ Real.log 11 < (14986845461 / 6250000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (12 : ℝ) = 2 * Real.log 2 + 1 * Real.log 3 := by
    rw [show (12 : ℝ) = ((2 : ℝ) ^ 2) * ((3 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 12)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 12
  have h1 : Real.log (1 - (1 : ℝ) / 12) = Real.log 11 - Real.log 12 := by
    rw [show (1 : ℝ) - 1 / 12 = 11 / 12 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 12 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log13_bounds : (2564949356421 / 1000000000000 : ℝ) < Real.log 13 ∧ Real.log 13 < (2564949358423 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a7, b7⟩ := log7_bounds
  have hm : Real.log (14 : ℝ) = 1 * Real.log 2 + 1 * Real.log 7 := by
    rw [show (14 : ℝ) = ((2 : ℝ) ^ 1) * ((7 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 14)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 11
  have h1 : Real.log (1 - (1 : ℝ) / 14) = Real.log 13 - Real.log 14 := by
    rw [show (1 : ℝ) - 1 / 14 = 13 / 14 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 14 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log17_bounds : (708303335689 / 250000000000 : ℝ) < Real.log 17 ∧ Real.log 17 < (2833213345259 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (18 : ℝ) = 1 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 18)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have h1 : Real.log (1 - (1 : ℝ) / 18) = Real.log 17 - Real.log 18 := by
    rw [show (1 : ℝ) - 1 / 18 = 17 / 18 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 18 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log19_bounds : (588887795573 / 200000000000 : ℝ) < Real.log 19 ∧ Real.log 19 < (2944438980369 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log (20 : ℝ) = 2 * Real.log 2 + 1 * Real.log 5 := by
    rw [show (20 : ℝ) = ((2 : ℝ) ^ 2) * ((5 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 20)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 10
  have h1 : Real.log (1 - (1 : ℝ) / 20) = Real.log 19 - Real.log 20 := by
    rw [show (1 : ℝ) - 1 / 20 = 19 / 20 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 20 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log23_bounds : (3135494214629 / 1000000000000 : ℝ) < Real.log 23 ∧ Real.log 23 < (3135494217131 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (24 : ℝ) = 3 * Real.log 2 + 1 * Real.log 3 := by
    rw [show (24 : ℝ) = ((2 : ℝ) ^ 3) * ((3 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 24)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 9
  have h1 : Real.log (1 - (1 : ℝ) / 24) = Real.log 23 - Real.log 24 := by
    rw [show (1 : ℝ) - 1 / 24 = 23 / 24 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 24 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log29_bounds : (134691833137 / 40000000000 : ℝ) < Real.log 29 ∧ Real.log 29 < (336729583143 / 100000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log (30 : ℝ) = 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 := by
    rw [show (30 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 1) * ((5 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 30)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have h1 : Real.log (1 - (1 : ℝ) / 30) = Real.log 29 - Real.log 30 := by
    rw [show (1 : ℝ) - 1 / 30 = 29 / 30 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 30 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log31_bounds : (686797440637 / 200000000000 : ℝ) < Real.log 31 ∧ Real.log 31 < (1716993602843 / 500000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  have hm : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = ((2 : ℝ) ^ 5) by norm_num, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 32)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have h1 : Real.log (1 - (1 : ℝ) / 32) = Real.log 31 - Real.log 32 := by
    rw [show (1 : ℝ) - 1 / 32 = 31 / 32 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 32 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log37_bounds : (1805458955541 / 500000000000 : ℝ) < Real.log 37 ∧ Real.log 37 < (3610917914087 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a19, b19⟩ := log19_bounds
  have hm : Real.log (38 : ℝ) = 1 * Real.log 2 + 1 * Real.log 19 := by
    rw [show (38 : ℝ) = ((2 : ℝ) ^ 1) * ((19 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 38)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have h1 : Real.log (1 - (1 : ℝ) / 38) = Real.log 37 - Real.log 38 := by
    rw [show (1 : ℝ) - 1 / 38 = 37 / 38 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 38 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log41_bounds : (3713572065143 / 1000000000000 : ℝ) < Real.log 41 ∧ Real.log 41 < (1856786034073 / 500000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  obtain ⟨a7, b7⟩ := log7_bounds
  have hm : Real.log (42 : ℝ) = 1 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 7 := by
    rw [show (42 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 1) * ((7 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 42)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 8
  have h1 : Real.log (1 - (1 : ℝ) / 42) = Real.log 41 - Real.log 42 := by
    rw [show (1 : ℝ) - 1 / 42 = 41 / 42 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 42 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log43_bounds : (3761200114133 / 1000000000000 : ℝ) < Real.log 43 ∧ Real.log 43 < (235075007321 / 62500000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a11, b11⟩ := log11_bounds
  have hm : Real.log (44 : ℝ) = 2 * Real.log 2 + 1 * Real.log 11 := by
    rw [show (44 : ℝ) = ((2 : ℝ) ^ 2) * ((11 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 44)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 44) = Real.log 43 - Real.log 44 := by
    rw [show (1 : ℝ) - 1 / 44 = 43 / 44 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 44 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log47_bounds : (77002952003 / 20000000000 : ℝ) < Real.log 47 ∧ Real.log 47 < (240634225197 / 62500000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (48 : ℝ) = 4 * Real.log 2 + 1 * Real.log 3 := by
    rw [show (48 : ℝ) = ((2 : ℝ) ^ 4) * ((3 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 48)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 48) = Real.log 47 - Real.log 48 := by
    rw [show (1 : ℝ) - 1 / 48 = 47 / 48 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 48 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log53_bounds : (3970291911731 / 1000000000000 : ℝ) < Real.log 53 ∧ Real.log 53 < (794058383047 / 200000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (54 : ℝ) = 1 * Real.log 2 + 3 * Real.log 3 := by
    rw [show (54 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 3) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 54)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 54) = Real.log 53 - Real.log 54 := by
    rw [show (1 : ℝ) - 1 / 54 = 53 / 54 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 54 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log59_bounds : (1019384360521 / 250000000000 : ℝ) < Real.log 59 ∧ Real.log 59 < (4077537445589 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log (60 : ℝ) = 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 5 := by
    rw [show (60 : ℝ) = ((2 : ℝ) ^ 2) * ((3 : ℝ) ^ 1) * ((5 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 60)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 60) = Real.log 59 - Real.log 60 := by
    rw [show (1 : ℝ) - 1 / 60 = 59 / 60 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 60 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log61_bounds : (4110873862613 / 1000000000000 : ℝ) < Real.log 61 ∧ Real.log 61 < (822174773123 / 200000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a31, b31⟩ := log31_bounds
  have hm : Real.log (62 : ℝ) = 1 * Real.log 2 + 1 * Real.log 31 := by
    rw [show (62 : ℝ) = ((2 : ℝ) ^ 1) * ((31 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 62)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 62) = Real.log 61 - Real.log 62 := by
    rw [show (1 : ℝ) - 1 / 62 = 61 / 62 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 62 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log67_bounds : (420469261757 / 100000000000 : ℝ) < Real.log 67 ∧ Real.log 67 < (2102346310537 / 500000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a17, b17⟩ := log17_bounds
  have hm : Real.log (68 : ℝ) = 2 * Real.log 2 + 1 * Real.log 17 := by
    rw [show (68 : ℝ) = ((2 : ℝ) ^ 2) * ((17 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 68)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 68) = Real.log 67 - Real.log 68 := by
    rw [show (1 : ℝ) - 1 / 68 = 67 / 68 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 68 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log71_bounds : (4262679875221 / 1000000000000 : ℝ) < Real.log 71 ∧ Real.log 71 < (1065669969681 / 250000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  have hm : Real.log (72 : ℝ) = 3 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (72 : ℝ) = ((2 : ℝ) ^ 3) * ((3 : ℝ) ^ 2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 72)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 7
  have h1 : Real.log (1 - (1 : ℝ) / 72) = Real.log 71 - Real.log 72 := by
    rw [show (1 : ℝ) - 1 / 72 = 71 / 72 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 72 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log73_bounds : (2145229719663 / 500000000000 : ℝ) < Real.log 73 ∧ Real.log 73 < (268153715177 / 62500000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a37, b37⟩ := log37_bounds
  have hm : Real.log (74 : ℝ) = 1 * Real.log 2 + 1 * Real.log 37 := by
    rw [show (74 : ℝ) = ((2 : ℝ) ^ 1) * ((37 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 74)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 6
  have h1 : Real.log (1 - (1 : ℝ) / 74) = Real.log 73 - Real.log 74 := by
    rw [show (1 : ℝ) - 1 / 74 = 73 / 74 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 74 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log79_bounds : (2184723925323 / 500000000000 : ℝ) < Real.log 79 ∧ Real.log 79 < (87388957083 / 20000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log (80 : ℝ) = 4 * Real.log 2 + 1 * Real.log 5 := by
    rw [show (80 : ℝ) = ((2 : ℝ) ^ 4) * ((5 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 80)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 6
  have h1 : Real.log (1 - (1 : ℝ) / 80) = Real.log 79 - Real.log 80 := by
    rw [show (1 : ℝ) - 1 / 80 = 79 / 80 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 80 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log83_bounds : (552355075747 / 125000000000 : ℝ) < Real.log 83 ∧ Real.log 83 < (4418840609479 / 1000000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  obtain ⟨a7, b7⟩ := log7_bounds
  have hm : Real.log (84 : ℝ) = 2 * Real.log 2 + 1 * Real.log 3 + 1 * Real.log 7 := by
    rw [show (84 : ℝ) = ((2 : ℝ) ^ 2) * ((3 : ℝ) ^ 1) * ((7 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 84)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 6
  have h1 : Real.log (1 - (1 : ℝ) / 84) = Real.log 83 - Real.log 84 := by
    rw [show (1 : ℝ) - 1 / 84 = 83 / 84 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 84 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log89_bounds : (89772727353 / 20000000000 : ℝ) < Real.log 89 ∧ Real.log 89 < (561079546457 / 125000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a3, b3⟩ := log3_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log (90 : ℝ) = 1 * Real.log 2 + 2 * Real.log 3 + 1 * Real.log 5 := by
    rw [show (90 : ℝ) = ((2 : ℝ) ^ 1) * ((3 : ℝ) ^ 2) * ((5 : ℝ) ^ 1) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 90)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 6
  have h1 : Real.log (1 - (1 : ℝ) / 90) = Real.log 89 - Real.log 90 := by
    rw [show (1 : ℝ) - 1 / 90 = 89 / 90 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 90 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

lemma log97_bounds : (2287355488341 / 500000000000 : ℝ) < Real.log 97 ∧ Real.log 97 < (914942196037 / 200000000000 : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a7, b7⟩ := log7_bounds
  have hm : Real.log (98 : ℝ) = 1 * Real.log 2 + 2 * Real.log 7 := by
    rw [show (98 : ℝ) = ((2 : ℝ) ^ 1) * ((7 : ℝ) ^ 2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hser := Real.abs_log_sub_add_sum_range_le (x := (1 : ℝ) / 98)
    (by rw [abs_of_pos (by norm_num)]; norm_num) 6
  have h1 : Real.log (1 - (1 : ℝ) / 98) = Real.log 97 - Real.log 98 := by
    rw [show (1 : ℝ) - 1 / 98 = 97 / 98 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [h1, hm, abs_of_pos (show (0 : ℝ) < 1 / 98 by norm_num), abs_le] at hser
  norm_num [Finset.sum_range_succ] at hser
  obtain ⟨hs1, hs2⟩ := hser
  constructor <;> linarith

/-- Integer weight tree (920 cells of width 1/200, depth 10; leaves past 920 are padding). -/
def cwTree : WTree :=
  (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 1000000000) (.leaf 995576748)) (.node (.leaf 993327896) (.leaf 988555021))) (.node (.node (.leaf 988756373) (.leaf 987151887)) (.node (.leaf 989177600) (.leaf 948950648)))) (.node (.node (.node (.leaf 947771310) (.leaf 949695996)) (.node (.leaf 949968585) (.leaf 953561220))) (.node (.node (.leaf 947535267) (.leaf 945116055)) (.node (.leaf 947853412) (.leaf 950680673))))) (.node (.node (.node (.node (.leaf 945012330) (.leaf 948648089)) (.node (.leaf 948281691) (.leaf 950993844))) (.node (.node (.leaf 947178467) (.leaf 949966168)) (.node (.leaf 949824290) (.leaf 953704972)))) (.node (.node (.node (.leaf 914122493) (.leaf 916173100)) (.node (.leaf 916454116) (.leaf 918094822))) (.node (.node (.leaf 918343786) (.leaf 917438442)) (.node (.leaf 921141180) (.leaf 917247741)))))) (.node (.node (.node (.node (.node (.leaf 922889179) (.leaf 923499222)) (.node (.leaf 915082013) (.leaf 921212857))) (.node (.node (.leaf 924288365) (.leaf 924116428)) (.node (.leaf 885617259) (.leaf 886050608)))) (.node (.node (.node (.leaf 887856095) (.leaf 886088133)) (.node (.leaf 891127933) (.leaf 879684012))) (.node (.node (.leaf 882726410) (.leaf 887607822)) (.node (.leaf 885140166) (.leaf 887642933))))) (.node (.node (.node (.node (.leaf 846245189) (.leaf 846765479)) (.node (.leaf 848796992) (.leaf 853193636))) (.node (.node (.leaf 852124069) (.leaf 847634954)) (.node (.leaf 848800193) (.leaf 854146432)))) (.node (.node (.node (.leaf 852362489) (.leaf 857492307)) (.node (.leaf 861004243) (.leaf 856883965))) (.node (.node (.leaf 861592103) (.leaf 859174491)) (.node (.leaf 862712783) (.leaf 820632410))))))) (.node (.node (.node (.node (.node (.node (.leaf 818770034) (.leaf 822244530)) (.node (.leaf 822426878) (.leaf 826178460))) (.node (.node (.leaf 828702615) (.leaf 786631844)) (.node (.leaf 786448416) (.leaf 788927207)))) (.node (.node (.node (.leaf 793339976) (.leaf 795228247)) (.node (.leaf 797531804) (.leaf 794117086))) (.node (.node (.leaf 795813979) (.leaf 795369048)) (.node (.leaf 798101241) (.leaf 800810963))))) (.node (.node (.node (.node (.leaf 802223994) (.leaf 759461580)) (.node (.leaf 759650651) (.leaf 762405692))) (.node (.node (.leaf 765354050) (.leaf 764249249)) (.node (.leaf 768588068) (.leaf 772535317)))) (.node (.node (.node (.leaf 765894145) (.leaf 769790423)) (.node (.leaf 759946828) (.leaf 761783205))) (.node (.node (.leaf 765814610) (.leaf 762151047)) (.node (.leaf 765560016) (.leaf 765564119)))))) (.node (.node (.node (.node (.node (.leaf 769014518) (.leaf 768941471)) (.node (.leaf 771697666) (.leaf 728868695))) (.node (.node (.leaf 727845372) (.leaf 730726607)) (.node (.leaf 733995846) (.leaf 734032291)))) (.node (.node (.node (.leaf 736484790) (.leaf 737997038)) (.node (.leaf 693070029) (.leaf 694663423))) (.node (.node (.leaf 700353831) (.leaf 701690522)) (.node (.leaf 697881221) (.leaf 699772123))))) (.node (.node (.node (.node (.leaf 701068229) (.leaf 700032143)) (.node (.leaf 699889769) (.leaf 702024245))) (.node (.node (.leaf 701544615) (.leaf 702498557)) (.node (.leaf 703939821) (.leaf 709008284)))) (.node (.node (.node (.leaf 713148528) (.leaf 704955342)) (.node (.leaf 708637524) (.leaf 708245938))) (.node (.node (.leaf 708542219) (.leaf 708177714)) (.node (.leaf 714578816) (.leaf 664892783)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 666035788) (.leaf 668394617)) (.node (.leaf 674161116) (.leaf 674619320))) (.node (.node (.leaf 670001123) (.leaf 671891509)) (.node (.leaf 673786767) (.leaf 679663303)))) (.node (.node (.node (.leaf 671542982) (.leaf 673386872)) (.node (.leaf 719606954) (.leaf 718382743))) (.node (.node (.leaf 716853295) (.leaf 718423642)) (.node (.leaf 721060626) (.leaf 693503194))))) (.node (.node (.node (.node (.leaf 694810829) (.leaf 695201260)) (.node (.leaf 694186375) (.leaf 697830362))) (.node (.node (.leaf 699893442) (.leaf 699177872)) (.node (.leaf 705187652) (.leaf 654031736)))) (.node (.node (.node (.leaf 652951084) (.leaf 658718803)) (.node (.leaf 660061383) (.leaf 664138777))) (.node (.node (.leaf 658273977) (.leaf 662434239)) (.node (.leaf 662438333) (.leaf 661881896)))))) (.node (.node (.node (.node (.node (.leaf 666945106) (.leaf 665275586)) (.node (.leaf 665339555) (.leaf 667911740))) (.node (.node (.leaf 668979464) (.leaf 667252829)) (.node (.leaf 672176390) (.leaf 672394745)))) (.node (.node (.node (.leaf 671303494) (.leaf 622827218)) (.node (.leaf 621956890) (.leaf 628125035))) (.node (.node (.leaf 629270533) (.leaf 631967363)) (.node (.leaf 633427021) (.leaf 635447720))))) (.node (.node (.node (.node (.leaf 638565669) (.leaf 636276692)) (.node (.leaf 639369508) (.leaf 588454057))) (.node (.node (.leaf 588992874) (.leaf 591901179)) (.node (.leaf 594047421) (.leaf 593357482)))) (.node (.node (.node (.leaf 595251822) (.leaf 594542820)) (.node (.leaf 596388598) (.leaf 600263220))) (.node (.node (.leaf 600298378) (.leaf 602186040)) (.node (.leaf 597926451) (.leaf 599866746))))))) (.node (.node (.node (.node (.node (.node (.leaf 599844978) (.leaf 602960797)) (.node (.leaf 605502734) (.leaf 601134274))) (.node (.node (.leaf 604345005) (.leaf 604990025)) (.node (.leaf 609167429) (.leaf 557864874)))) (.node (.node (.node (.leaf 556851933) (.leaf 558765680)) (.node (.leaf 556382273) (.leaf 560464702))) (.node (.node (.leaf 560524513) (.leaf 561203653)) (.node (.leaf 564345859) (.leaf 563238741))))) (.node (.node (.node (.node (.leaf 562323714) (.leaf 567179631)) (.node (.leaf 569489837) (.leaf 563690931))) (.node (.node (.leaf 565687397) (.leaf 567012285)) (.node (.leaf 567784496) (.leaf 568308234)))) (.node (.node (.node (.leaf 567638909) (.leaf 561887387)) (.node (.leaf 563701697) (.leaf 623015844))) (.node (.node (.leaf 620216133) (.leaf 619644491)) (.node (.leaf 619486126) (.leaf 614701792)))))) (.node (.node (.node (.node (.node (.leaf 617563292) (.leaf 616787743)) (.node (.leaf 618865679) (.leaf 621853255))) (.node (.node (.leaf 610517602) (.leaf 610732213)) (.node (.leaf 613958214) (.leaf 613985531)))) (.node (.node (.node (.leaf 614154928) (.leaf 618047671)) (.node (.leaf 620617993) (.leaf 565285082))) (.node (.node (.leaf 563662012) (.leaf 567051398)) (.node (.leaf 564612645) (.leaf 569380895))))) (.node (.node (.node (.node (.leaf 571325789) (.leaf 571091568)) (.node (.leaf 575222932) (.leaf 574334306))) (.node (.node (.leaf 576325697) (.leaf 576865932)) (.node (.leaf 578314639) (.leaf 577581523)))) (.node (.node (.node (.leaf 523732786) (.leaf 522655824)) (.node (.leaf 525716147) (.leaf 527837684))) (.node (.node (.leaf 527971891) (.leaf 530859602)) (.node (.leaf 530902418) (.leaf 531243161))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 530623229) (.leaf 535287946)) (.node (.leaf 533026713) (.leaf 535718357))) (.node (.node (.leaf 536004475) (.leaf 535782872)) (.node (.leaf 519857864) (.leaf 517461926)))) (.node (.node (.node (.leaf 517962312) (.leaf 519611342)) (.node (.leaf 520851208) (.leaf 520902120))) (.node (.node (.leaf 518347399) (.leaf 524012131)) (.node (.leaf 526552094) (.leaf 519752559))))) (.node (.node (.node (.node (.leaf 522699403) (.leaf 525650308)) (.node (.leaf 525746146) (.leaf 524392567))) (.node (.node (.leaf 527975568) (.leaf 559483575)) (.node (.leaf 530362203) (.leaf 525261110)))) (.node (.node (.node (.leaf 525360193) (.leaf 528474559)) (.node (.leaf 528150741) (.leaf 528172642))) (.node (.node (.leaf 530365150) (.leaf 532596177)) (.node (.leaf 535503568) (.leaf 532752743)))))) (.node (.node (.node (.node (.node (.leaf 534263221) (.leaf 531629701)) (.node (.leaf 531769236) (.leaf 534787662))) (.node (.node (.leaf 538071043) (.leaf 537906665)) (.node (.leaf 481286033) (.leaf 480554990)))) (.node (.node (.node (.leaf 484272011) (.leaf 484383817)) (.node (.leaf 486082468) (.leaf 485987866))) (.node (.node (.leaf 486662972) (.leaf 483825431)) (.node (.leaf 486857148) (.leaf 488215136))))) (.node (.node (.node (.node (.leaf 482173370) (.leaf 485960333)) (.node (.leaf 489544577) (.leaf 489053749))) (.node (.node (.leaf 488502529) (.leaf 491146324)) (.node (.leaf 492372787) (.leaf 493161659)))) (.node (.node (.node (.leaf 494277334) (.leaf 486405413)) (.node (.leaf 489626568) (.leaf 489680887))) (.node (.node (.leaf 490376536) (.leaf 490220534)) (.node (.leaf 488885782) (.leaf 485950922))))))) (.node (.node (.node (.node (.node (.node (.leaf 488300553) (.leaf 554634672)) (.node (.leaf 553472973) (.leaf 548451141))) (.node (.node (.leaf 547947674) (.leaf 549864646)) (.node (.leaf 546834512) (.leaf 549615654)))) (.node (.node (.node (.leaf 550584738) (.leaf 547644534)) (.node (.leaf 551278884) (.leaf 551070468))) (.node (.node (.leaf 554519904) (.leaf 494049459)) (.node (.leaf 493966593) (.leaf 496332423))))) (.node (.node (.node (.node (.leaf 497753954) (.leaf 498445860)) (.node (.leaf 496654891) (.leaf 499417053))) (.node (.node (.leaf 501572998) (.leaf 499849596)) (.node (.leaf 503274097) (.leaf 502902829)))) (.node (.node (.node (.leaf 499852852) (.leaf 502610398)) (.node (.leaf 503160679) (.leaf 501284800))) (.node (.node (.leaf 501253805) (.leaf 503383939)) (.node (.leaf 502650630) (.leaf 506469672)))))) (.node (.node (.node (.node (.node (.leaf 509269097) (.leaf 509125130)) (.node (.leaf 512231356) (.leaf 450913543))) (.node (.node (.leaf 449442694) (.leaf 454805759)) (.node (.leaf 453859544) (.leaf 452331002)))) (.node (.node (.node (.leaf 455073203) (.leaf 455054643)) (.node (.leaf 458394220) (.leaf 456728969))) (.node (.node (.leaf 460132891) (.leaf 461039699)) (.node (.leaf 461051742) (.leaf 443582995))))) (.node (.node (.node (.node (.leaf 444655726) (.leaf 444816203)) (.node (.leaf 443995877) (.leaf 441763824))) (.node (.node (.leaf 444955242) (.leaf 447551834)) (.node (.leaf 444857023) (.leaf 445897991)))) (.node (.node (.node (.leaf 445924049) (.leaf 444069354)) (.node (.leaf 448310367) (.leaf 448470730))) (.node (.node (.leaf 451826250) (.leaf 444707872)) (.node (.leaf 446054085) (.leaf 446179407)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 446944862) (.leaf 444288163)) (.node (.leaf 443870793) (.leaf 440802211))) (.node (.node (.leaf 443676347) (.leaf 507161779)) (.node (.leaf 506684794) (.leaf 503471615)))) (.node (.node (.node (.leaf 503805357) (.leaf 506452641)) (.node (.leaf 500453380) (.leaf 502962151))) (.node (.node (.leaf 503230627) (.leaf 500067853)) (.node (.leaf 500050478) (.leaf 498048183))))) (.node (.node (.node (.node (.leaf 503031456) (.leaf 505309826)) (.node (.leaf 503803890) (.leaf 503389398))) (.node (.node (.leaf 506795344) (.leaf 505612195)) (.node (.leaf 505947058) (.leaf 509597916)))) (.node (.node (.node (.leaf 511918251) (.leaf 448523862)) (.node (.leaf 447459840) (.leaf 447108065))) (.node (.node (.leaf 448314420) (.leaf 448133112)) (.node (.leaf 445168127) (.leaf 470859695)))))) (.node (.node (.node (.node (.node (.leaf 470732235) (.leaf 471898214)) (.node (.leaf 472736278) (.leaf 469712264))) (.node (.node (.leaf 472884957) (.leaf 469295867)) (.node (.leaf 469795066) (.leaf 470617679)))) (.node (.node (.node (.leaf 471023089) (.leaf 470779660)) (.node (.leaf 470591542) (.leaf 472711646))) (.node (.node (.leaf 467172610) (.leaf 466103703)) (.node (.leaf 469694566) (.leaf 469139439))))) (.node (.node (.node (.node (.leaf 471707016) (.leaf 469845908)) (.node (.leaf 472296620) (.leaf 472126353))) (.node (.node (.leaf 472828909) (.leaf 472299432)) (.node (.leaf 473779923) (.leaf 507717377)))) (.node (.node (.node (.leaf 506780742) (.leaf 507332900)) (.node (.leaf 443582660) (.leaf 444218369))) (.node (.node (.leaf 446269697) (.leaf 445659705)) (.node (.leaf 445414325) (.leaf 443004324))))))) (.node (.node (.node (.node (.node (.node (.leaf 445603077) (.leaf 445001914)) (.node (.leaf 447673076) (.leaf 447754607))) (.node (.node (.leaf 447309724) (.leaf 447571332)) (.node (.leaf 446670406) (.leaf 443446848)))) (.node (.node (.node (.leaf 445771046) (.leaf 446374645)) (.node (.leaf 445765350) (.leaf 448805987))) (.node (.node (.leaf 448604408) (.leaf 448798505)) (.node (.leaf 445758402) (.leaf 446370447))))) (.node (.node (.node (.node (.leaf 445784387) (.leaf 443443056)) (.node (.leaf 446670047) (.leaf 447568624))) (.node (.node (.leaf 447324237) (.leaf 447760311)) (.node (.leaf 447654280) (.leaf 444977686)))) (.node (.node (.node (.leaf 445603338) (.leaf 443020121)) (.node (.leaf 445422439) (.leaf 445661939))) (.node (.node (.leaf 446263180) (.leaf 444209373)) (.node (.leaf 443587021) (.leaf 507622932)))))) (.node (.node (.node (.node (.node (.leaf 506909157) (.leaf 507559484)) (.node (.leaf 473759509) (.leaf 472308474))) (.node (.node (.leaf 472836739) (.leaf 472115999)) (.node (.leaf 472270676) (.leaf 469826625)))) (.node (.node (.node (.leaf 471693769) (.leaf 469141833)) (.node (.leaf 469693607) (.leaf 466098950))) (.node (.node (.leaf 467170297) (.leaf 472720041)) (.node (.leaf 470599595) (.leaf 470778391))))) (.node (.node (.node (.node (.leaf 471027729) (.leaf 470627202)) (.node (.leaf 469815211) (.leaf 469282144))) (.node (.node (.leaf 472886943) (.leaf 469718466)) (.node (.leaf 472747759) (.leaf 471881667)))) (.node (.node (.node (.leaf 470640336) (.leaf 470747579)) (.node (.leaf 445168423) (.leaf 448136080))) (.node (.node (.leaf 448318342) (.leaf 447112874)) (.node (.leaf 447452225) (.leaf 448504023)))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 512192618) (.leaf 509877560)) (.node (.leaf 505955516) (.leaf 505587266))) (.node (.node (.leaf 506777797) (.leaf 503385024)) (.node (.leaf 503781612) (.leaf 505284847)))) (.node (.node (.node (.leaf 503024750) (.leaf 498049286)) (.node (.leaf 500061157) (.leaf 500072093))) (.node (.node (.leaf 503237379) (.leaf 502968239)) (.node (.leaf 500439652) (.leaf 506467649))))) (.node (.node (.node (.node (.leaf 503834409) (.leaf 503481002)) (.node (.leaf 506379479) (.leaf 506858339))) (.node (.node (.leaf 443690037) (.leaf 440821124)) (.node (.leaf 443894261) (.leaf 444283751)))) (.node (.node (.node (.leaf 446951422) (.leaf 446188044)) (.node (.leaf 446050145) (.leaf 444699601))) (.node (.node (.leaf 451847873) (.leaf 448489870)) (.node (.leaf 448329033) (.leaf 444062474)))))) (.node (.node (.node (.node (.node (.leaf 445917235) (.leaf 445884903)) (.node (.leaf 444840987) (.leaf 447538254))) (.node (.node (.leaf 444944077) (.leaf 441764565)) (.node (.leaf 443995986) (.leaf 444828107)))) (.node (.node (.node (.leaf 444650191) (.leaf 443583256)) (.node (.leaf 461115998) (.leaf 461103193))) (.node (.node (.leaf 460118445) (.leaf 456717587)) (.node (.leaf 458372768) (.leaf 455041529))))) (.node (.node (.node (.node (.leaf 455058619) (.leaf 452322045)) (.node (.leaf 453859250) (.leaf 454800883))) (.node (.node (.leaf 449449542) (.leaf 450903411)) (.node (.leaf 512505493) (.leaf 509384383)))) (.node (.node (.node (.leaf 509250228) (.leaf 506440463)) (.node (.leaf 502645466) (.leaf 503381912))) (.node (.node (.leaf 501241503) (.leaf 501259146)) (.node (.leaf 503150350) (.leaf 502629706))))))) (.node (.node (.node (.node (.node (.node (.leaf 499865552) (.leaf 502903294)) (.node (.leaf 503268616) (.leaf 499836501))) (.node (.node (.leaf 501555038) (.leaf 499406403)) (.node (.leaf 496643958) (.leaf 498433353)))) (.node (.node (.node (.leaf 497742122) (.leaf 496326400)) (.node (.leaf 493948019) (.leaf 494043846))) (.node (.node (.leaf 554787920) (.leaf 551337788)) (.node (.leaf 551269225) (.leaf 547628857))))) (.node (.node (.node (.node (.leaf 550582220) (.leaf 549610512)) (.node (.leaf 546823781) (.leaf 549876454))) (.node (.node (.leaf 547976268) (.leaf 548444392)) (.node (.leaf 553180334) (.leaf 554339464)))) (.node (.node (.node (.leaf 488313358) (.leaf 485948817)) (.node (.leaf 488883045) (.leaf 490230338))) (.node (.node (.leaf 490382617) (.leaf 489676671)) (.node (.leaf 489612899) (.leaf 486401515)))))) (.node (.node (.node (.node (.node (.leaf 494298423) (.leaf 493181208)) (.node (.leaf 492390270) (.leaf 491126421))) (.node (.node (.leaf 488487861) (.leaf 489034991)) (.node (.leaf 489528019) (.leaf 485954635)))) (.node (.node (.node (.leaf 482153008) (.leaf 488214751)) (.node (.leaf 486864105) (.leaf 483840111))) (.node (.node (.leaf 486668566) (.leaf 485991671)) (.node (.leaf 486069700) (.leaf 484368889))))) (.node (.node (.node (.node (.leaf 484245745) (.leaf 480542097)) (.node (.leaf 481259256) (.leaf 538166427))) (.node (.node (.leaf 538323991) (.leaf 534782133)) (.node (.leaf 531752681) (.leaf 531625728)))) (.node (.node (.node (.leaf 534273336) (.leaf 532741253)) (.node (.leaf 535503243) (.leaf 532571194))) (.node (.node (.leaf 530352070) (.leaf 528156039)) (.node (.leaf 528140444) (.leaf 528479370)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 525371055) (.leaf 525258264)) (.node (.leaf 530227931) (.leaf 559478866))) (.node (.node (.leaf 528117733) (.leaf 524391479)) (.node (.leaf 525717026) (.leaf 525624096)))) (.node (.node (.node (.leaf 522686646) (.leaf 519737988)) (.node (.leaf 526544420) (.leaf 524012617))) (.node (.node (.leaf 518369836) (.leaf 520885640)) (.node (.leaf 520838893) (.leaf 519598015))))) (.node (.node (.node (.node (.leaf 517956700) (.leaf 517434945)) (.node (.leaf 519862598) (.leaf 535892169))) (.node (.node (.leaf 536087329) (.leaf 535704953)) (.node (.leaf 533011645) (.leaf 535267279)))) (.node (.node (.node (.leaf 530617688) (.leaf 531216681)) (.node (.leaf 530906389) (.leaf 530855151))) (.node (.node (.leaf 527970720) (.leaf 527816120)) (.node (.leaf 525690788) (.leaf 522647119)))))) (.node (.node (.node (.node (.node (.leaf 523721135) (.leaf 577840885)) (.node (.leaf 578551859) (.leaf 576847504))) (.node (.node (.leaf 576298339) (.leaf 574337456)) (.node (.leaf 575230859) (.leaf 571068412)))) (.node (.node (.node (.leaf 571292181) (.leaf 569344641)) (.node (.leaf 564598492) (.leaf 567043450))) (.node (.node (.leaf 563667435) (.leaf 565270171)) (.node (.leaf 620845141) (.leaf 618283774))))) (.node (.node (.node (.node (.leaf 614166049) (.leaf 613980615)) (.node (.leaf 613932297) (.leaf 610714992))) (.node (.node (.leaf 610495376) (.leaf 621880889)) (.node (.leaf 618920736) (.leaf 616786037)))) (.node (.node (.node (.leaf 617539110) (.leaf 614691769)) (.node (.leaf 619528421) (.leaf 619658787))) (.node (.node (.leaf 619950823) (.leaf 622742602)) (.node (.leaf 563700049) (.leaf 561904944))))))) (.node (.node (.node (.node (.node (.node (.leaf 567667879) (.leaf 568320919)) (.node (.leaf 567780398) (.leaf 566983802))) (.node (.node (.leaf 565662289) (.leaf 563646933)) (.node (.leaf 569495500) (.leaf 567192129)))) (.node (.node (.node (.leaf 562345398) (.leaf 563234283)) (.node (.leaf 564328427) (.leaf 561193613))) (.node (.node (.leaf 560517675) (.leaf 560459903)) (.node (.leaf 556385266) (.leaf 558770659))))) (.node (.node (.node (.node (.leaf 556849786) (.leaf 557832369)) (.node (.leaf 609375825) (.leaf 605223667))) (.node (.node (.leaf 604334263) (.leaf 601103470)) (.node (.leaf 605497339) (.leaf 602966686)))) (.node (.node (.node (.leaf 599831021) (.leaf 599833427)) (.node (.leaf 597907488) (.leaf 602194477))) (.node (.node (.leaf 600310945) (.leaf 600246100)) (.node (.leaf 596373563) (.leaf 594530508)))))) (.node (.node (.node (.node (.node (.leaf 595249201) (.leaf 593367732)) (.node (.leaf 594021733) (.leaf 591877613))) (.node (.node (.leaf 588971548) (.leaf 588434516)) (.node (.leaf 639592216) (.leaf 636508088)))) (.node (.node (.node (.leaf 638553361) (.leaf 635419346)) (.node (.leaf 633414009) (.leaf 631947220))) (.node (.node (.leaf 629245454) (.leaf 628088061)) (.node (.leaf 621943676) (.leaf 622811516))))) (.node (.node (.node (.node (.leaf 671533510) (.leaf 672608242)) (.node (.leaf 672153749) (.leaf 667215750))) (.node (.node (.leaf 668974035) (.leaf 667909833)) (.node (.leaf 665319164) (.leaf 665250870)))) (.node (.node (.node (.leaf 666940814) (.leaf 661902688)) (.node (.leaf 662433053) (.leaf 662402709))) (.node (.node (.leaf 658254128) (.leaf 664125680)) (.node (.leaf 660057606) (.leaf 658723132))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 652943706) (.leaf 654007865)) (.node (.leaf 705389229) (.leaf 699382741))) (.node (.node (.leaf 699861348) (.leaf 697816745)) (.node (.leaf 694186606) (.leaf 695213211)))) (.node (.node (.node (.leaf 694801624) (.leaf 693471076)) (.node (.leaf 721169671) (.leaf 718550412))) (.node (.node (.leaf 716854595) (.leaf 718179029)) (.node (.leaf 719404218) (.leaf 673390175))))) (.node (.node (.node (.node (.leaf 671514665) (.leaf 679649361)) (.node (.leaf 673807813) (.leaf 671906484))) (.node (.node (.leaf 669983855) (.leaf 674594593)) (.node (.leaf 674133352) (.leaf 668396765)))) (.node (.node (.node (.leaf 666014224) (.leaf 664870202)) (.node (.leaf 714766413) (.leaf 708394622))) (.node (.node (.leaf 708524943) (.leaf 708236834)) (.node (.leaf 708627077) (.leaf 704926748)))))) (.node (.node (.node (.node (.node (.leaf 713140039) (.leaf 709009304)) (.node (.leaf 703932989) (.leaf 702481996))) (.node (.node (.leaf 701530478) (.leaf 702001151)) (.node (.leaf 699862648) (.leaf 700050971)))) (.node (.node (.node (.leaf 701083575) (.leaf 699772540)) (.node (.leaf 697859342) (.leaf 701680993))) (.node (.node (.leaf 700328832) (.leaf 694662557)) (.node (.leaf 693036477) (.leaf 738201683))))) (.node (.node (.node (.node (.leaf 736698843) (.leaf 734013899)) (.node (.leaf 733965368) (.leaf 730697439))) (.node (.node (.leaf 727825217) (.leaf 728816551)) (.node (.leaf 771879759) (.leaf 769122947)))) (.node (.node (.node (.leaf 769023046) (.leaf 765572293)) (.node (.leaf 765538667) (.leaf 762126851))) (.node (.node (.leaf 765802633) (.leaf 761792143)) (.node (.leaf 759936316) (.leaf 769797195))))))) (.node (.node (.node (.node (.node (.node (.leaf 765901941) (.leaf 772549950)) (.node (.leaf 768595618) (.leaf 764274352))) (.node (.node (.leaf 765327654) (.leaf 762377759)) (.node (.leaf 759618832) (.leaf 759436591)))) (.node (.node (.node (.leaf 802401716) (.leaf 800985645)) (.node (.leaf 798079492) (.leaf 795378613))) (.node (.node (.leaf 795801382) (.leaf 794098445)) (.node (.leaf 797517091) (.leaf 795223607))))) (.node (.node (.node (.node (.leaf 793337538) (.leaf 788904359)) (.node (.leaf 786428299) (.leaf 786577215))) (.node (.node (.leaf 828882631) (.leaf 826354737)) (.node (.leaf 822435940) (.leaf 822237620)))) (.node (.node (.node (.leaf 818742133) (.leaf 820599172)) (.node (.leaf 862872585) (.leaf 859348511))) (.node (.node (.leaf 861583839) (.leaf 856880078)) (.node (.leaf 861002262) (.leaf 857473653)))))) (.node (.node (.node (.node (.node (.leaf 852340608) (.leaf 854121402)) (.node (.leaf 848788943) (.leaf 847621398))) (.node (.node (.leaf 852142568) (.leaf 853203398)) (.node (.leaf 848791307) (.leaf 846749249)))) (.node (.node (.node (.leaf 846228805) (.leaf 887822549)) (.node (.leaf 885311004) (.leaf 887569350))) (.node (.node (.leaf 882685013) (.leaf 879658184)) (.node (.leaf 891162412) (.leaf 886136389))))) (.node (.node (.node (.node (.leaf 887858344) (.leaf 886035280)) (.node (.leaf 885590691) (.leaf 924287075))) (.node (.node (.leaf 924451698) (.leaf 921198228)) (.node (.leaf 915066426) (.leaf 923502597)))) (.node (.node (.node (.leaf 922889255) (.leaf 917226302)) (.node (.leaf 921113268) (.leaf 917421329))) (.node (.node (.leaf 918370737) (.leaf 918094796)) (.node (.leaf 916469169) (.leaf 916157191)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 914090807) (.leaf 953887392)) (.node (.leaf 950001900) (.leaf 949936878))) (.node (.node (.leaf 947145296) (.leaf 951003583)) (.node (.leaf 948293205) (.leaf 948642114)))) (.node (.node (.node (.leaf 945012098) (.leaf 950694681)) (.node (.leaf 947863036) (.leaf 945107626))) (.node (.node (.leaf 947530917) (.leaf 953586007)) (.node (.leaf 949996547) (.leaf 949689048))))) (.node (.node (.node (.node (.leaf 947765885) (.leaf 948951725)) (.node (.leaf 989373496) (.leaf 987338592))) (.node (.node (.leaf 988778631) (.leaf 988582870)) (.node (.leaf 993373476) (.leaf 995389648)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))))) (.node (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))))) (.node (.node (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))))) (.node (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))))))))))

/-- Shift data `(n, C, A, B)`: `log n ∈ [A q, B q]`, `Λ(n)/√n ≤ C / S`, all prime powers `n < 100`. -/
def cwShifts : List (ℕ × ℕ × ℕ × ℕ) :=
  [(2, 490129073, 1386294360, 1386294362),
    (3, 634284102, 2197224576, 2197224579),
    (4, 346573591, 2772588721, 2772588724),
    (5, 719762517, 3218875823, 3218875827),
    (7, 735484905, 3891820296, 3891820300),
    (8, 245064537, 4158883081, 4158883085),
    (9, 366204097, 4394449152, 4394449157),
    (11, 722992629, 4795790543, 4795790548),
    (13, 711388957, 5129898712, 5129898717),
    (16, 173286796, 5545177442, 5545177447),
    (17, 687155170, 5666426685, 5666426691),
    (19, 675500630, 5888877955, 5888877961),
    (23, 653795740, 6270988429, 6270988435),
    (25, 321887583, 6437751646, 6437751653),
    (27, 211428034, 6591673728, 6591673735),
    (29, 625291139, 6734591656, 6734591663),
    (31, 616762310, 6867974406, 6867974412),
    (32, 122532268, 6931471803, 6931471808),
    (37, 593631249, 7221835822, 7221835829),
    (41, 579962520, 7427144130, 7427144137),
    (43, 573577641, 7522400228, 7522400235),
    (47, 561601748, 7700295200, 7700295207),
    (49, 277987165, 7783640593, 7783640600),
    (53, 545361537, 7940583823, 7940583831),
    (59, 530850160, 8155074884, 8155074892),
    (61, 526343464, 8221747725, 8221747732),
    (64, 86643398, 8317766163, 8317766170),
    (67, 513684962, 8409385235, 8409385243),
    (71, 505887030, 8525359750, 8525359758),
    (73, 502160296, 8580918878, 8580918886),
    (79, 491601292, 8738895701, 8738895709),
    (81, 122068033, 8788898305, 8788898314),
    (83, 485030770, 8837681211, 8837681219),
    (89, 475794504, 8977272735, 8977272744),
    (97, 464491526, 9149421953, 9149421961)]

/-- The kernel evaluates the whole integer Schur test (920 rows x 35 shifts x 2 sides). -/
theorem cw_check : checkRows (WTree.get 10 cwTree) 920 10000000 11161373010 1000000000 cwShifts 920 = true := by
  decide +kernel

lemma cw_entry_2 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (2, 490129073, 1386294360, 1386294362) :=
  entryOK_of (p := 2) (k := 1) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (707106781 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_3 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (3, 634284102, 2197224576, 2197224579) :=
  entryOK_of (p := 3) (k := 1) (lo := (274653072037 / 250000000000 : ℝ)) (hi := (1098612289149 / 1000000000000 : ℝ)) (s := (1732050807 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log3_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_4 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (4, 346573591, 2772588721, 2772588724) :=
  entryOK_of (p := 2) (k := 2) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_5 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (5, 719762517, 3218875823, 3218875827) :=
  entryOK_of (p := 5) (k := 1) (lo := (1609437911653 / 1000000000000 : ℝ)) (hi := (402359478289 / 250000000000 : ℝ)) (s := (2236067977 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log5_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_7 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (7, 735484905, 3891820296, 3891820300) :=
  entryOK_of (p := 7) (k := 1) (lo := (77836405931 / 40000000000 : ℝ)) (hi := (121619384361 / 62500000000 : ℝ)) (s := (2645751311 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log7_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_8 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (8, 245064537, 4158883081, 4158883085) :=
  entryOK_of (p := 2) (k := 3) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (707106781 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_9 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (9, 366204097, 4394449152, 4394449157) :=
  entryOK_of (p := 3) (k := 2) (lo := (274653072037 / 250000000000 : ℝ)) (hi := (1098612289149 / 1000000000000 : ℝ)) (s := (3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log3_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_11 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (11, 722992629, 4795790543, 4795790548) :=
  entryOK_of (p := 11) (k := 1) (lo := (1198947635879 / 500000000000 : ℝ)) (hi := (14986845461 / 6250000000 : ℝ)) (s := (331662479 / 100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log11_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_13 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (13, 711388957, 5129898712, 5129898717) :=
  entryOK_of (p := 13) (k := 1) (lo := (2564949356421 / 1000000000000 : ℝ)) (hi := (2564949358423 / 1000000000000 : ℝ)) (s := (144222051 / 40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log13_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_16 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (16, 173286796, 5545177442, 5545177447) :=
  entryOK_of (p := 2) (k := 4) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_17 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (17, 687155170, 5666426685, 5666426691) :=
  entryOK_of (p := 17) (k := 1) (lo := (708303335689 / 250000000000 : ℝ)) (hi := (2833213345259 / 1000000000000 : ℝ)) (s := (6596969 / 1600000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log17_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_19 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (19, 675500630, 5888877955, 5888877961) :=
  entryOK_of (p := 19) (k := 1) (lo := (588887795573 / 200000000000 : ℝ)) (hi := (2944438980369 / 1000000000000 : ℝ)) (s := (4358898943 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log19_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_23 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (23, 653795740, 6270988429, 6270988435) :=
  entryOK_of (p := 23) (k := 1) (lo := (3135494214629 / 1000000000000 : ℝ)) (hi := (3135494217131 / 1000000000000 : ℝ)) (s := (4795831523 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log23_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_25 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (25, 321887583, 6437751646, 6437751653) :=
  entryOK_of (p := 5) (k := 2) (lo := (1609437911653 / 1000000000000 : ℝ)) (hi := (402359478289 / 250000000000 : ℝ)) (s := (5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log5_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_27 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (27, 211428034, 6591673728, 6591673735) :=
  entryOK_of (p := 3) (k := 3) (lo := (274653072037 / 250000000000 : ℝ)) (hi := (1098612289149 / 1000000000000 : ℝ)) (s := (2598076211 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log3_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_29 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (29, 625291139, 6734591656, 6734591663) :=
  entryOK_of (p := 29) (k := 1) (lo := (134691833137 / 40000000000 : ℝ)) (hi := (336729583143 / 100000000000 : ℝ)) (s := (5385164807 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log29_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_31 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (31, 616762310, 6867974406, 6867974412) :=
  entryOK_of (p := 31) (k := 1) (lo := (686797440637 / 200000000000 : ℝ)) (hi := (1716993602843 / 500000000000 : ℝ)) (s := (2783882181 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log31_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_32 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (32, 122532268, 6931471803, 6931471808) :=
  entryOK_of (p := 2) (k := 5) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (5656854249 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_37 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (37, 593631249, 7221835822, 7221835829) :=
  entryOK_of (p := 37) (k := 1) (lo := (1805458955541 / 500000000000 : ℝ)) (hi := (3610917914087 / 1000000000000 : ℝ)) (s := (608276253 / 100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log37_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_41 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (41, 579962520, 7427144130, 7427144137) :=
  entryOK_of (p := 41) (k := 1) (lo := (3713572065143 / 1000000000000 : ℝ)) (hi := (1856786034073 / 500000000000 : ℝ)) (s := (6403124237 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log41_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_43 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (43, 573577641, 7522400228, 7522400235) :=
  entryOK_of (p := 43) (k := 1) (lo := (3761200114133 / 1000000000000 : ℝ)) (hi := (235075007321 / 62500000000 : ℝ)) (s := (1639359631 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log43_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_47 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (47, 561601748, 7700295200, 7700295207) :=
  entryOK_of (p := 47) (k := 1) (lo := (77002952003 / 20000000000 : ℝ)) (hi := (240634225197 / 62500000000 : ℝ)) (s := (34278273 / 5000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log47_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_49 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (49, 277987165, 7783640593, 7783640600) :=
  entryOK_of (p := 7) (k := 2) (lo := (77836405931 / 40000000000 : ℝ)) (hi := (121619384361 / 62500000000 : ℝ)) (s := (7 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log7_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_53 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (53, 545361537, 7940583823, 7940583831) :=
  entryOK_of (p := 53) (k := 1) (lo := (3970291911731 / 1000000000000 : ℝ)) (hi := (794058383047 / 200000000000 : ℝ)) (s := (7280109889 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log53_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_59 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (59, 530850160, 8155074884, 8155074892) :=
  entryOK_of (p := 59) (k := 1) (lo := (1019384360521 / 250000000000 : ℝ)) (hi := (4077537445589 / 1000000000000 : ℝ)) (s := (7681145747 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log59_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_61 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (61, 526343464, 8221747725, 8221747732) :=
  entryOK_of (p := 61) (k := 1) (lo := (4110873862613 / 1000000000000 : ℝ)) (hi := (822174773123 / 200000000000 : ℝ)) (s := (312409987 / 40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log61_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_64 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (64, 86643398, 8317766163, 8317766170) :=
  entryOK_of (p := 2) (k := 6) (lo := (6931471803 / 10000000000 : ℝ)) (hi := (108304247 / 156250000 : ℝ)) (s := (8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log2_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_67 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (67, 513684962, 8409385235, 8409385243) :=
  entryOK_of (p := 67) (k := 1) (lo := (420469261757 / 100000000000 : ℝ)) (hi := (2102346310537 / 500000000000 : ℝ)) (s := (8185352771 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log67_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_71 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (71, 505887030, 8525359750, 8525359758) :=
  entryOK_of (p := 71) (k := 1) (lo := (4262679875221 / 1000000000000 : ℝ)) (hi := (1065669969681 / 250000000000 : ℝ)) (s := (8426149773 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log71_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_73 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (73, 502160296, 8580918878, 8580918886) :=
  entryOK_of (p := 73) (k := 1) (lo := (2145229719663 / 500000000000 : ℝ)) (hi := (268153715177 / 62500000000 : ℝ)) (s := (1708800749 / 200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log73_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_79 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (79, 491601292, 8738895701, 8738895709) :=
  entryOK_of (p := 79) (k := 1) (lo := (2184723925323 / 500000000000 : ℝ)) (hi := (87388957083 / 20000000000 : ℝ)) (s := (8888194417 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log79_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_81 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (81, 122068033, 8788898305, 8788898314) :=
  entryOK_of (p := 3) (k := 4) (lo := (274653072037 / 250000000000 : ℝ)) (hi := (1098612289149 / 1000000000000 : ℝ)) (s := (9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log3_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_83 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (83, 485030770, 8837681211, 8837681219) :=
  entryOK_of (p := 83) (k := 1) (lo := (552355075747 / 125000000000 : ℝ)) (hi := (4418840609479 / 1000000000000 : ℝ)) (s := (9110433579 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log83_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_89 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (89, 475794504, 8977272735, 8977272744) :=
  entryOK_of (p := 89) (k := 1) (lo := (89772727353 / 20000000000 : ℝ)) (hi := (561079546457 / 125000000000 : ℝ)) (s := (2358495283 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log89_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entry_97 : EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) (97, 464491526, 9149421953, 9149421961) :=
  entryOK_of (p := 97) (k := 1) (lo := (2287355488341 / 500000000000 : ℝ)) (hi := (914942196037 / 200000000000 : ℝ)) (s := (9848857801 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast log97_bounds) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma cw_entries : ∀ e ∈ cwShifts, EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ) e := by
  have hall : List.Forall (EntryOK (1 / 2000000000 : ℝ) (1000000000 : ℝ)) cwShifts :=
    ⟨cw_entry_2,
    cw_entry_3,
    cw_entry_4,
    cw_entry_5,
    cw_entry_7,
    cw_entry_8,
    cw_entry_9,
    cw_entry_11,
    cw_entry_13,
    cw_entry_16,
    cw_entry_17,
    cw_entry_19,
    cw_entry_23,
    cw_entry_25,
    cw_entry_27,
    cw_entry_29,
    cw_entry_31,
    cw_entry_32,
    cw_entry_37,
    cw_entry_41,
    cw_entry_43,
    cw_entry_47,
    cw_entry_49,
    cw_entry_53,
    cw_entry_59,
    cw_entry_61,
    cw_entry_64,
    cw_entry_67,
    cw_entry_71,
    cw_entry_73,
    cw_entry_79,
    cw_entry_81,
    cw_entry_83,
    cw_entry_89,
    cw_entry_97⟩
  exact List.forall_iff_forall_mem.mp hall

lemma vm_0 : Λ 0 = 0 := ArithmeticFunction.map_zero
lemma vm_1 : Λ 1 = 0 := vonMangoldt_apply_one
lemma vm_6 : Λ 6 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_10 : Λ 10 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_12 : Λ 12 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_14 : Λ 14 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_15 : Λ 15 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_18 : Λ 18 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_20 : Λ 20 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_21 : Λ 21 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_22 : Λ 22 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_24 : Λ 24 = 0 :=
  vonMangoldt_eq_zero_of_coprime 8 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_26 : Λ 26 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_28 : Λ 28 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_30 : Λ 30 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_33 : Λ 33 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_34 : Λ 34 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_35 : Λ 35 = 0 :=
  vonMangoldt_eq_zero_of_coprime 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_36 : Λ 36 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_38 : Λ 38 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_39 : Λ 39 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_40 : Λ 40 = 0 :=
  vonMangoldt_eq_zero_of_coprime 8 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_42 : Λ 42 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_44 : Λ 44 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_45 : Λ 45 = 0 :=
  vonMangoldt_eq_zero_of_coprime 9 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_46 : Λ 46 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_48 : Λ 48 = 0 :=
  vonMangoldt_eq_zero_of_coprime 16 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_50 : Λ 50 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_51 : Λ 51 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_52 : Λ 52 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_54 : Λ 54 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_55 : Λ 55 = 0 :=
  vonMangoldt_eq_zero_of_coprime 5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_56 : Λ 56 = 0 :=
  vonMangoldt_eq_zero_of_coprime 8 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_57 : Λ 57 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_58 : Λ 58 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_60 : Λ 60 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_62 : Λ 62 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_63 : Λ 63 = 0 :=
  vonMangoldt_eq_zero_of_coprime 9 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_65 : Λ 65 = 0 :=
  vonMangoldt_eq_zero_of_coprime 5 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_66 : Λ 66 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_68 : Λ 68 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_69 : Λ 69 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_70 : Λ 70 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_72 : Λ 72 = 0 :=
  vonMangoldt_eq_zero_of_coprime 8 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_74 : Λ 74 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_75 : Λ 75 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_76 : Λ 76 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_77 : Λ 77 = 0 :=
  vonMangoldt_eq_zero_of_coprime 7 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_78 : Λ 78 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_80 : Λ 80 = 0 :=
  vonMangoldt_eq_zero_of_coprime 16 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_82 : Λ 82 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_84 : Λ 84 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_85 : Λ 85 = 0 :=
  vonMangoldt_eq_zero_of_coprime 5 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_86 : Λ 86 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_87 : Λ 87 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_88 : Λ 88 = 0 :=
  vonMangoldt_eq_zero_of_coprime 8 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_90 : Λ 90 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_91 : Λ 91 = 0 :=
  vonMangoldt_eq_zero_of_coprime 7 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_92 : Λ 92 = 0 :=
  vonMangoldt_eq_zero_of_coprime 4 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_93 : Λ 93 = 0 :=
  vonMangoldt_eq_zero_of_coprime 3 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_94 : Λ 94 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_95 : Λ 95 = 0 :=
  vonMangoldt_eq_zero_of_coprime 5 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_96 : Λ 96 = 0 :=
  vonMangoldt_eq_zero_of_coprime 32 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_98 : Λ 98 = 0 :=
  vonMangoldt_eq_zero_of_coprime 2 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
lemma vm_99 : Λ 99 = 0 :=
  vonMangoldt_eq_zero_of_coprime 9 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The integers `n < 100` that are not prime powers (`Λ n = 0`). -/
def nonPP100 : List ℕ := [0, 1, 6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63, 65, 66, 68, 69, 70, 72, 74, 75, 76, 77, 78, 80, 82, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 96, 98, 99]

lemma nonPP100_vm : ∀ n ∈ nonPP100, Λ n = 0 :=
  List.forall_iff_forall_mem.mp (show List.Forall (fun n => Λ n = 0) nonPP100 from ⟨vm_0, vm_1, vm_6, vm_10, vm_12, vm_14, vm_15, vm_18, vm_20, vm_21, vm_22, vm_24, vm_26, vm_28, vm_30, vm_33, vm_34, vm_35, vm_36, vm_38, vm_39, vm_40, vm_42, vm_44, vm_45, vm_46, vm_48, vm_50, vm_51, vm_52, vm_54, vm_55, vm_56, vm_57, vm_58, vm_60, vm_62, vm_63, vm_65, vm_66, vm_68, vm_69, vm_70, vm_72, vm_74, vm_75, vm_76, vm_77, vm_78, vm_80, vm_82, vm_84, vm_85, vm_86, vm_87, vm_88, vm_90, vm_91, vm_92, vm_93, vm_94, vm_95, vm_96, vm_98, vm_99⟩)

lemma cw_cover : ∀ n < 100, n ∉ cwShifts.map Prod.fst → n ∈ nonPP100 := by
  decide

lemma cw_zero : ∀ n < 100, n ∉ cwShifts.map Prod.fst → Λ n = 0 :=
  fun n hn hnot => nonPP100_vm n (cw_cover n hn hnot)

lemma log100_gt : 2 * (23 / 10 : ℝ) < Real.log ((100 : ℕ) : ℝ) := by
  obtain ⟨a2, b2⟩ := log2_bounds
  obtain ⟨a5, b5⟩ := log5_bounds
  have hm : Real.log ((100 : ℕ) : ℝ) = 2 * Real.log 2 + 2 * Real.log 5 := by
    rw [show ((100 : ℕ) : ℝ) = ((2 : ℝ) ^ 2) * ((5 : ℝ) ^ 2) by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hm]; linarith

/-- **Certified form-level comb constant at `L' = 2.3`** (THEOREM, kernel-checked): for every
continuous compactly supported `g` vanishing off `[-L', L']`,
`‖Σ_n Λ(n)/√n (g⋆g~(log n) + g⋆g~(-log n))‖ ≤ 11.161373010 ‖g‖²`.
(The pointwise comb constant of the same window is `Σ_{n<100} 2Λ(n)/√n ≈ 33.79`; see `combMass_gt_three_lam`.) -/
theorem primeSide_autocorr_le_cert {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ ((11161373010 : ℝ) / 1000000000) * ∫ x, ‖g x‖ ^ 2 := by
  have := primeSide_autocorr_le_of_check (L := (23 / 10 : ℝ)) (h := (1 / 200 : ℝ)) (q := (1 / 2000000000 : ℝ))
    (S := 1000000000) (WTree.get 10 cwTree) 920 10000000 11161373010 1000000000 100 cwShifts
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    cw_check cw_entries (by decide) (by decide) cw_zero log100_gt hgc hgs hgW
  exact_mod_cast this

/-- The certified constant on the E8 test class. -/
theorem primeSide_autocorr_le_cert_weil {g : ℝ → ℂ} (hg : IsWeilTest g)
    (hgW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → g x = 0) :
    ‖primeSide (autocorr g)‖ ≤ ((11161373010 : ℝ) / 1000000000) * ∫ x, ‖g x‖ ^ 2 :=
  primeSide_autocorr_le_cert hg.1.continuous hg.2 hgW

/-- **Twist invariance at the certified constant**: every frequency twist `g ↦ e^{irx} g` (the comb
symbol `P(t + r)`) obeys the same bound; this is where `Λ ≥ 0` is used. -/
theorem primeSide_autocorr_twist_le_cert {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → g x = 0) (r : ℝ) :
    ‖primeSide (autocorr (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x))‖
      ≤ ((11161373010 : ℝ) / 1000000000) * ∫ x, ‖g x‖ ^ 2 := by
  have hn : ∀ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ = ‖g x‖ := by
    intro x; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hc : Continuous (fun x => Complex.exp (((r * x : ℝ) : ℂ) * I) * g x) := by fun_prop
  have hW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → Complex.exp (((r * x : ℝ) : ℂ) * I) * g x = 0 := by
    intro x hx; simp [hgW x hx]
  have h := primeSide_autocorr_le_cert hc hgs.mul_left hW
  have hint : (∫ x, ‖Complex.exp (((r * x : ℝ) : ℂ) * I) * g x‖ ^ 2) = ∫ x, ‖g x‖ ^ 2 := by
    congr 1; funext x; rw [hn x]
  rw [hint] at h
  exact h

/-- **Form-level envelope on the Weil functional** (Theorem 1 with `ω ≡ 1`, kernel-checked):
`Re W(g ⋆ g~) ≥ Re Arch(g ⋆ g~) - 11.161373 ‖g‖²` for every smooth test supported in `[-L', L']`. -/
theorem weilForm_autocorr_ge_cert {g : ℝ → ℂ} (hg : IsWeilTest g)
    (hgW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → g x = 0) :
    (archSide (autocorr g)).re - ((11161373010 : ℝ) / 1000000000) * ∫ x, ‖g x‖ ^ 2 ≤ (weilForm (autocorr g)).re := by
  have h := primeSide_autocorr_le_cert_weil hg hgW
  have hre : (primeSide (autocorr g)).re ≤ ‖primeSide (autocorr g)‖ := Complex.re_le_norm _
  unfold weilForm
  rw [Complex.sub_re]
  linarith

lemma low_2 : ((980258142 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 2 / Real.sqrt ((2 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 2) (p := 2) (k := 1) (D := 980258142) (lo := (6931471803 / 10000000000 : ℝ)) (s := (1414213563 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_3 : ((1268568200 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 3 / Real.sqrt ((3 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 3) (p := 3) (k := 1) (D := 1268568200) (lo := (274653072037 / 250000000000 : ℝ)) (s := (216506351 / 125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log3_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_4 : ((693147180 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 4 / Real.sqrt ((4 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 4) (p := 2) (k := 2) (D := 693147180) (lo := (6931471803 / 10000000000 : ℝ)) (s := (2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_5 : ((1439525030 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 5 / Real.sqrt ((5 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 5) (p := 5) (k := 1) (D := 1439525030) (lo := (1609437911653 / 1000000000000 : ℝ)) (s := (1118033989 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log5_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_7 : ((1470969806 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 7 / Real.sqrt ((7 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 7) (p := 7) (k := 1) (D := 1470969806) (lo := (77836405931 / 40000000000 : ℝ)) (s := (165359457 / 62500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log7_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_8 : ((490129071 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 8 / Real.sqrt ((8 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 8) (p := 2) (k := 3) (D := 490129071) (lo := (6931471803 / 10000000000 : ℝ)) (s := (22627417 / 8000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_9 : ((732408192 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 9 / Real.sqrt ((9 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 9) (p := 3) (k := 2) (D := 732408192) (lo := (274653072037 / 250000000000 : ℝ)) (s := (3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log3_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_11 : ((1445985254 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 11 / Real.sqrt ((11 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 11) (p := 11) (k := 1) (D := 1445985254) (lo := (1198947635879 / 500000000000 : ℝ)) (s := (3316624791 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log11_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_13 : ((1422777911 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 13 / Real.sqrt ((13 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 13) (p := 13) (k := 1) (D := 1422777911) (lo := (2564949356421 / 1000000000000 : ℝ)) (s := (901387819 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log13_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_16 : ((346573590 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 16 / Real.sqrt ((16 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 16) (p := 2) (k := 4) (D := 346573590) (lo := (6931471803 / 10000000000 : ℝ)) (s := (4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_17 : ((1374310337 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 17 / Real.sqrt ((17 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 17) (p := 17) (k := 1) (D := 1374310337) (lo := (708303335689 / 250000000000 : ℝ)) (s := (2061552813 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log17_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_19 : ((1351001257 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 19 / Real.sqrt ((19 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 19) (p := 19) (k := 1) (D := 1351001257) (lo := (588887795573 / 200000000000 : ℝ)) (s := (17026949 / 3906250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log19_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_23 : ((1307591477 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 23 / Real.sqrt ((23 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 23) (p := 23) (k := 1) (D := 1307591477) (lo := (3135494214629 / 1000000000000 : ℝ)) (s := (1198957881 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log23_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_25 : ((643775164 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 25 / Real.sqrt ((25 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 25) (p := 5) (k := 2) (D := 643775164) (lo := (1609437911653 / 1000000000000 : ℝ)) (s := (5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log5_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_27 : ((422856066 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 27 / Real.sqrt ((27 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 27) (p := 3) (k := 3) (D := 422856066) (lo := (274653072037 / 250000000000 : ℝ)) (s := (5196152423 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log3_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_29 : ((1250582275 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 29 / Real.sqrt ((29 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 29) (p := 29) (k := 1) (D := 1250582275) (lo := (134691833137 / 40000000000 : ℝ)) (s := (673145601 / 125000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log29_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_31 : ((1233524617 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 31 / Real.sqrt ((31 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 31) (p := 31) (k := 1) (D := 1233524617) (lo := (686797440637 / 200000000000 : ℝ)) (s := (5567764363 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log31_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_32 : ((245064535 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 32 / Real.sqrt ((32 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 32) (p := 2) (k := 5) (D := 245064535) (lo := (6931471803 / 10000000000 : ℝ)) (s := (22627417 / 4000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_37 : ((1187262495 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 37 / Real.sqrt ((37 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 37) (p := 37) (k := 1) (D := 1187262495) (lo := (1805458955541 / 500000000000 : ℝ)) (s := (6082762531 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log37_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_41 : ((1159925038 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 41 / Real.sqrt ((41 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 41) (p := 41) (k := 1) (D := 1159925038) (lo := (3713572065143 / 1000000000000 : ℝ)) (s := (3201562119 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log41_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_43 : ((1147155280 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 43 / Real.sqrt ((43 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 43) (p := 43) (k := 1) (D := 1147155280) (lo := (3761200114133 / 1000000000000 : ℝ)) (s := (262297541 / 40000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log43_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_47 : ((1123203493 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 47 / Real.sqrt ((47 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 47) (p := 47) (k := 1) (D := 1123203493) (lo := (77002952003 / 20000000000 : ℝ)) (s := (6855654601 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log47_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_49 : ((555974328 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 49 / Real.sqrt ((49 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 49) (p := 7) (k := 2) (D := 555974328) (lo := (77836405931 / 40000000000 : ℝ)) (s := (7 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log7_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_53 : ((1090723071 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 53 / Real.sqrt ((53 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 53) (p := 53) (k := 1) (D := 1090723071) (lo := (3970291911731 / 1000000000000 : ℝ)) (s := (728010989 / 100000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log53_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_59 : ((1061700318 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 59 / Real.sqrt ((59 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 59) (p := 59) (k := 1) (D := 1061700318) (lo := (1019384360521 / 250000000000 : ℝ)) (s := (1920286437 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log59_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_61 : ((1052686926 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 61 / Real.sqrt ((61 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 61) (p := 61) (k := 1) (D := 1052686926) (lo := (4110873862613 / 1000000000000 : ℝ)) (s := (1952562419 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log61_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_64 : ((173286795 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 64 / Real.sqrt ((64 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 64) (p := 2) (k := 6) (D := 173286795) (lo := (6931471803 / 10000000000 : ℝ)) (s := (8 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log2_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_67 : ((1027369921 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 67 / Real.sqrt ((67 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 67) (p := 67) (k := 1) (D := 1027369921) (lo := (420469261757 / 100000000000 : ℝ)) (s := (2046338193 / 250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log67_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_71 : ((1011774058 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 71 / Real.sqrt ((71 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 71) (p := 71) (k := 1) (D := 1011774058) (lo := (4262679875221 / 1000000000000 : ℝ)) (s := (4213074887 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log71_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_73 : ((1004320589 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 73 / Real.sqrt ((73 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 73) (p := 73) (k := 1) (D := 1004320589) (lo := (2145229719663 / 500000000000 : ℝ)) (s := (4272001873 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log73_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_79 : ((983202582 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 79 / Real.sqrt ((79 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 79) (p := 79) (k := 1) (D := 983202582) (lo := (2184723925323 / 500000000000 : ℝ)) (s := (4444097209 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log79_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_81 : ((244136064 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 81 / Real.sqrt ((81 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 81) (p := 3) (k := 4) (D := 244136064) (lo := (274653072037 / 250000000000 : ℝ)) (s := (9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log3_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_83 : ((970061538 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 83 / Real.sqrt ((83 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 83) (p := 83) (k := 1) (D := 970061538) (lo := (552355075747 / 125000000000 : ℝ)) (s := (455521679 / 50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log83_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_89 : ((951589006 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 89 / Real.sqrt ((89 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 89) (p := 89) (k := 1) (D := 951589006) (lo := (89772727353 / 20000000000 : ℝ)) (s := (9433981133 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log89_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

lemma low_97 : ((928983049 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ 97 / Real.sqrt ((97 : ℕ) : ℝ) := by
  have := entryLow_of (S := 1000000000) (n := 97) (p := 97) (k := 1) (D := 928983049) (lo := (2287355488341 / 500000000000 : ℝ)) (s := (4924428901 / 500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (log97_bounds).1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact_mod_cast this

/-- Lower-bound data `(n, D)`: `D / S ≤ 2 Λ(n)/√n` for the prime powers `n < 100`. -/
def lowData : List (ℕ × ℕ) := [(2, 980258142), (3, 1268568200), (4, 693147180), (5, 1439525030), (7, 1470969806), (8, 490129071), (9, 732408192), (11, 1445985254), (13, 1422777911), (16, 346573590), (17, 1374310337), (19, 1351001257), (23, 1307591477), (25, 643775164), (27, 422856066), (29, 1250582275), (31, 1233524617), (32, 245064535), (37, 1187262495), (41, 1159925038), (43, 1147155280), (47, 1123203493), (49, 555974328), (53, 1090723071), (59, 1061700318), (61, 1052686926), (64, 173286795), (67, 1027369921), (71, 1011774058), (73, 1004320589), (79, 983202582), (81, 244136064), (83, 970061538), (89, 951589006), (97, 928983049)]

lemma lowData_ok : ∀ e ∈ lowData, ((e.2 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ e.1 / Real.sqrt e.1 :=
  List.forall_iff_forall_mem.mp (show List.Forall (fun e : ℕ × ℕ => ((e.2 : ℕ) : ℝ) / 1000000000 ≤
    2 * Λ e.1 / Real.sqrt e.1) lowData from ⟨low_2, low_3, low_4, low_5, low_7, low_8, low_9, low_11, low_13, low_16, low_17, low_19, low_23, low_25, low_27, low_29, low_31, low_32, low_37, low_41, low_43, low_47, low_49, low_53, low_59, low_61, low_64, low_67, low_71, low_73, low_79, low_81, low_83, low_89, low_97⟩)

lemma listSum_low : ∀ ds : List (ℕ × ℕ), (∀ e ∈ ds, ((e.2 : ℕ) : ℝ) / 1000000000 ≤ 2 * Λ e.1 / Real.sqrt e.1) →
    ((ds.map Prod.snd).sum : ℝ) / 1000000000 ≤ (ds.map (fun e => 2 * Λ e.1 / Real.sqrt e.1)).sum
  | [], _ => by simp
  | e :: ds, h => by
    have h1 := h e List.mem_cons_self
    have h2 := listSum_low ds (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
    linarith

/-- **The certified form-level constant is below one third of the pointwise comb mass of the same
window** (kernel-checked): `3 · 11.161373 < Σ_{n<100} 2Λ(n)/√n` (the latter is `A_{L'} = sup_t P_{L'}(t)`,
the constant of every pointwise-envelope certificate, Zhu's Lemma 3.2). -/
theorem combMass_gt_three_lam : 3 * ((11161373010 : ℝ) / 1000000000) < ∑ n ∈ range 100, 2 * Λ n / Real.sqrt n := by
  have hsubset : (lowData.map Prod.fst).toFinset ⊆ range 100 := by
    intro n hn; rw [List.mem_toFinset] at hn; exact Finset.mem_range.mpr (by revert n hn; decide)
  have hmap : lowData.map Prod.fst = cwShifts.map Prod.fst := by decide
  have h1 : ∑ n ∈ range 100, 2 * Λ n / Real.sqrt n
      = ∑ n ∈ (lowData.map Prod.fst).toFinset, 2 * Λ n / Real.sqrt n := by
    refine (Finset.sum_subset hsubset fun n hn hnot => ?_).symm
    rw [List.mem_toFinset, hmap] at hnot
    simp [cw_zero n (Finset.mem_range.mp hn) hnot]
  have hnd : (lowData.map Prod.fst).Nodup := by decide
  rw [h1, List.sum_toFinset _ hnd, List.map_map]
  have := listSum_low lowData lowData_ok
  have hsum : ((lowData.map Prod.snd).sum : ℝ) = (33792402655 : ℝ) := by
    have : (lowData.map Prod.snd).sum = 33792402655 := by decide
    exact_mod_cast this
  rw [hsum] at this
  have hlt : 3 * ((11161373010 : ℝ) / 1000000000) < (33792402655 : ℝ) / 1000000000 := by norm_num
  exact lt_of_lt_of_le hlt (le_of_le_of_eq this rfl)

end Instance

/-! ## F. The gluing of Theorem 2 on the E8 explicit formula (skeleton; analytic inputs named)

`Gφ := g⋆g~ - gH⋆gH~`.  In the paper `gH = μ * g` with `μ̂ = ω = 1 - K`; the pointwise split
`|F|² = (1 - |ω|²)|F|² + |ωF|²` is the split of the test `g⋆g~ = Gφ + gH⋆gH~`, so there are no cross
terms.  The zero side is used for `Gφ` (verified zeros contribute `≥ 0` because `|ω| ≤ 1`), the prime
side (form-level constant) for `gH⋆gH~`.  The three analytic inputs of the paper proof enter as
hypotheses: `hcontr` (`|ω| ≤ 1` on the line), `htail` (explicit tail over unverified zeros; paper:
`|φ| ≤ 3|K|`, `|F F*| ≤ 2 L e^L`, Trudgian's `S(t)`), `harch` (archimedean envelope; paper: digamma
lower bound, pole terms, leakage below `R = 2π e^{A⁺}`). -/

section Gluing

open ArithmeticFunction

lemma integrable_weilKernel_integrand {G : ℝ → ℂ} (hG : IsWeilTest G) (s : ℂ) :
    Integrable (fun u : ℝ => G u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := by
  have hc : Continuous (fun u : ℝ => G u * Complex.exp ((s - 1 / 2) * (u : ℂ))) := by
    have := hG.1.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport hG.2.mul_right

lemma weilKernel_sub {G₁ G₂ : ℝ → ℂ} (h₁ : IsWeilTest G₁) (h₂ : IsWeilTest G₂) (s : ℂ) :
    weilKernel (fun u => G₁ u - G₂ u) s = weilKernel G₁ s - weilKernel G₂ s := by
  unfold weilKernel
  rw [← integral_sub (integrable_weilKernel_integrand h₁ s) (integrable_weilKernel_integrand h₂ s)]
  congr 1; funext u; ring

lemma isWeilTest_sub {G₁ G₂ : ℝ → ℂ} (h₁ : IsWeilTest G₁) (h₂ : IsWeilTest G₂) :
    IsWeilTest (fun u => G₁ u - G₂ u) :=
  ⟨h₁.1.sub h₂.1, h₁.2.sub h₂.2⟩

/-- **Theorem 2, gluing skeleton** (THEOREM, kernel-checked, conditional on the named inputs):
verified zeros up to `T` plus the form-level comb bound give almost-positivity. -/
theorem weil_almost_pos_of_glue {g gH : ℝ → ℂ} (hg : IsWeilTest g) (hgH : IsWeilTest gH)
    (T lam E₁ E₂ : ℝ)
    (hPB : ‖primeSide (autocorr gH)‖ ≤ lam * ∫ x, ‖gH x‖ ^ 2)
    (hcontr : ∀ t : ℝ, ‖Zeta23.paperFT gH t‖ ≤ ‖Zeta23.paperFT g t‖)
    (hzeros : ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (htail : Summable (fun ρ : ℂ => if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0))
    (htailE : (∑' ρ : ℂ, if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0) ≤ E₁)
    (harch : lam * (∫ x, ‖gH x‖ ^ 2) - E₂ ≤ (archSide (autocorr gH)).re) :
    -(E₁ + E₂) ≤ (weilForm (autocorr g)).re := by
  have hA := RvMBridge5.isWeilTest_autocorr hg
  have hAH := RvMBridge5.isWeilTest_autocorr hgH
  have hφ := isWeilTest_sub hA hAH
  set Gφ : ℝ → ℂ := fun u => autocorr g u - autocorr gH u with hGφ
  -- explicit formula for the three tests
  have EF := (RvMBridge4.limit_explicit_formula _ hA).2
  have EFH := (RvMBridge4.limit_explicit_formula _ hAH).2
  have EFφ := (RvMBridge4.limit_explicit_formula _ hφ).2
  -- additivity of the zero side: W(g⋆g~) = W(Gφ) + W(gH⋆gH~)
  have hsplit : weilForm (autocorr g) = (archSide Gφ - primeSide Gφ) + weilForm (autocorr gH) := by
    have hadd := EFφ.add EFH
    have hfun : (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel Gφ ρ
        + (zeroMult ρ : ℂ) * weilKernel (autocorr gH) ρ)
        = fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ := by
      funext ρ
      rw [hGφ, weilKernel_sub hA hAH]
      ring
    rw [hfun] at hadd
    unfold weilForm
    exact EF.unique hadd
  -- zero side of Gφ: verified zeros contribute ≥ 0, unverified ones are in the tail
  have hzero_side : -E₁ ≤ (archSide Gφ - primeSide Gφ).re := by
    have hre := Complex.hasSum_re EFφ
    have hneg := htail.hasSum.neg
    refine le_trans (neg_le_neg htailE) (hasSum_le (fun ρ => ?_) hneg hre)
    by_cases hT : T < |ρ.im|
    · simp only [hT, if_true]
      have := Complex.re_le_norm (-( (zeroMult ρ : ℂ) * weilKernel Gφ ρ))
      rw [norm_neg, Complex.neg_re] at this
      linarith
    · simp only [hT, if_false, neg_zero]
      by_cases hz : Zeta23.IsNontrivialZero ρ
      · have hre12 := hzeros ρ hz (le_of_not_gt hT)
        have hρ : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
          apply Complex.ext <;> simp [hre12]
        have hk : weilKernel Gφ ρ = weilKernel Gφ (1 / 2 + (ρ.im : ℂ) * I) := by rw [← hρ]
        rw [hk, hGφ, weilKernel_sub hA hAH, RvMBridge5.weilKernel_autocorr_line hg,
          RvMBridge5.weilKernel_autocorr_line hgH]
        have hmono : ‖Zeta23.paperFT gH ρ.im‖ ^ 2 ≤ ‖Zeta23.paperFT g ρ.im‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hcontr ρ.im) 2
        have hcast : (zeroMult ρ : ℂ) * ((‖Zeta23.paperFT g ρ.im‖ : ℂ) ^ 2 - (‖Zeta23.paperFT gH ρ.im‖ : ℂ) ^ 2)
            = (((zeroMult ρ : ℝ) * (‖Zeta23.paperFT g ρ.im‖ ^ 2 - ‖Zeta23.paperFT gH ρ.im‖ ^ 2) : ℝ) : ℂ) := by
          push_cast; ring
        rw [hcast, Complex.ofReal_re]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial hz]
        simp
  -- arithmetic side of gH⋆gH~: form-level comb bound
  have harith : -E₂ ≤ (weilForm (autocorr gH)).re := by
    have hre : (primeSide (autocorr gH)).re ≤ ‖primeSide (autocorr gH)‖ := Complex.re_le_norm _
    unfold weilForm
    rw [Complex.sub_re]
    linarith
  rw [hsplit, Complex.add_re]
  linarith

/-- Theorem 2 skeleton with the kernel-certified constant: `gH` supported in `[-L', L']`. -/
theorem weil_almost_pos_cert {g gH : ℝ → ℂ} (hg : IsWeilTest g) (hgH : IsWeilTest gH)
    (hgHW : ∀ x, x ∉ Set.Icc (-(23 / 10 : ℝ)) (23 / 10 : ℝ) → gH x = 0) (T E₁ E₂ : ℝ)
    (hcontr : ∀ t : ℝ, ‖Zeta23.paperFT gH t‖ ≤ ‖Zeta23.paperFT g t‖)
    (hzeros : ∀ ρ : ℂ, Zeta23.IsNontrivialZero ρ → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (htail : Summable (fun ρ : ℂ => if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0))
    (htailE : (∑' ρ : ℂ, if T < |ρ.im| then
        ‖(zeroMult ρ : ℂ) * weilKernel (fun u => autocorr g u - autocorr gH u) ρ‖ else 0) ≤ E₁)
    (harch : ((11161373010 : ℝ) / 1000000000) * (∫ x, ‖gH x‖ ^ 2) - E₂ ≤ (archSide (autocorr gH)).re) :
    -(E₁ + E₂) ≤ (weilForm (autocorr g)).re :=
  weil_almost_pos_of_glue hg hgH T _ E₁ E₂ (primeSide_autocorr_le_cert_weil hgH hgHW) hcontr hzeros
    htail htailE harch

end Gluing

end Crux2VerifiedWindow

#print axioms Crux2VerifiedWindow.amgm_weighted
#print axioms Crux2VerifiedWindow.schur_twist_bound
#print axioms Crux2VerifiedWindow.amgm_window
#print axioms Crux2VerifiedWindow.schur_comb
#print axioms Crux2VerifiedWindow.primeSide_autocorr_le
#print axioms Crux2VerifiedWindow.autocorr_modulate
#print axioms Crux2VerifiedWindow.primeSide_autocorr_modulate
#print axioms Crux2VerifiedWindow.primeSide_autocorr_twist_le
#print axioms Crux2VerifiedWindow.weilForm_autocorr_ge
#print axioms Crux2VerifiedWindow.checkRows_sound
#print axioms Crux2VerifiedWindow.mMinus_sound
#print axioms Crux2VerifiedWindow.mPlus_sound
#print axioms Crux2VerifiedWindow.schur_of_check
#print axioms Crux2VerifiedWindow.primeSide_autocorr_le_of_check
#print axioms Crux2VerifiedWindow.cw_check
#print axioms Crux2VerifiedWindow.primeSide_autocorr_le_cert
#print axioms Crux2VerifiedWindow.primeSide_autocorr_le_cert_weil
#print axioms Crux2VerifiedWindow.primeSide_autocorr_twist_le_cert
#print axioms Crux2VerifiedWindow.weilForm_autocorr_ge_cert
#print axioms Crux2VerifiedWindow.combMass_gt_three_lam
#print axioms Crux2VerifiedWindow.weil_almost_pos_of_glue
#print axioms Crux2VerifiedWindow.weil_almost_pos_cert
