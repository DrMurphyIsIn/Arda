import Crux3_BandDH

/-!
# CF_Test: the M-mode Dirichlet-cosine window test and its closed forms

Counterfeit-ladder lane (CF), 2026-09-24, `rvm_bridge` island.

`conjecture1_proved = False`.  Pure real analysis on one explicit family of test functions.

Crux3's `bandV` has two modes.  The counterfeit-ladder certificate at `x ~ 28` needs nine, so this
file redoes the Crux3 closed forms for any finite family of Dirichlet cosines.

THE TEST.  Fix `A > 0`, `M` frequencies `k i > 0` (pairwise distinct) with `cos(k_i A) = 0` and
`sin(k_i A) = s_i` (`ModeHyp`), and real coefficients `c i`.  Then
`bandM A M k c u = sum_{i < M} c_i cos(k_i clamp(u))` equals the cosine sum on `[-A, A]` and vanishes
outside.  It is continuous (Lipschitz) and even.

PROVED:
* `bandM_freqData`: the Crux3 `FreqData` hypotheses, with the one-mode transform decay
  `|int_{-A}^{A} cos(k u) cos(r u) du| <= (2A(1 + 4k^2) + 8k/3 + 2/(3k))/(1 + r^2)` for every `k > 0`
  (Crux3 needed `k >= 1`; the lowest mode here has `k < 1`);
* `acR_bandM`: the autocorrelation on `[0, 2A]` is `sum_{i,j} c_i c_j blk_ij(y)`, with the Crux3 blocks
  `gD` on the diagonal and `s_i s_j (k_i sin(k_j y) - k_j sin(k_i y))/(k_i^2 - k_j^2)` off it;
  `acR_bandM_zero`: `g(0) = A sum c_i^2`;
* `lorTermB_bandM`: every Lorentzian term `int g(y) e^{-2b|y|} dy`, `b > 0`, in closed form:
  `4 b A sum_i c_i^2/(4b^2 + k_i^2) + 2 (1 + e^{-4bA}) (sum_i c_i s_i k_i/(4b^2 + k_i^2))^2`;
* `poleT_bandM`: `int v(u) e^{-u/2} du = sum_i c_i 2 k_i s_i cosh(A/2)/(k_i^2 + 1/4)`.
No `sorry`.
-/

open MeasureTheory Complex Zeta23 Set Filter Crux3
open scoped ComplexConjugate

noncomputable section

namespace CF

/-- The Dirichlet hypotheses on a finite family of frequencies. -/
structure ModeHyp (A : ℝ) (M : ℕ) (k s : ℕ → ℝ) : Prop where
  A0 : 0 < A
  kpos : ∀ i, i < M → 0 < k i
  cosk : ∀ i, i < M → Real.cos (k i * A) = 0
  sink : ∀ i, i < M → Real.sin (k i * A) = s i
  kinj : ∀ i, i < M → ∀ j, j < M → i ≠ j → k i ≠ k j

/-- The cosine sum `sum_{i < M} c_i cos(k_i u)`. -/
def wSum (M : ℕ) (k c : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range M, c i * Real.cos (k i * u)

/-- The M-mode window test `v = wSum o clamp`. -/
def bandM (A : ℝ) (M : ℕ) (k c : ℕ → ℝ) (u : ℝ) : ℝ := wSum M k c (clampA A u)

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

lemma ModeHyp.abs_s (i : ℕ) (hi : i < M) : |s i| ≤ 1 := by
  rw [← h.sink i hi]; exact Real.abs_sin_le_one _

lemma ModeHyp.s_sq (i : ℕ) (hi : i < M) : s i ^ 2 = 1 := by
  rw [← h.sink i hi]
  have := Real.sin_sq_add_cos_sq (k i * A)
  rw [h.cosk i hi] at this
  linarith

lemma wSum_A : wSum M k c A = 0 := by
  unfold wSum
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h.cosk i (Finset.mem_range.mp hi), mul_zero]

lemma wSum_negA : wSum M k c (-A) = 0 := by
  unfold wSum
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [mul_neg, Real.cos_neg, h.cosk i (Finset.mem_range.mp hi), mul_zero]

omit h in
lemma bandM_of_mem {u : ℝ} (hu : |u| ≤ A) : bandM A M k c u = wSum M k c u := by
  unfold bandM
  rw [clampA_of_mem hu]

lemma bandM_of_gt {u : ℝ} (hu : A < |u|) : bandM A M k c u = 0 := by
  unfold bandM clampA
  rcases lt_abs.mp hu with hu | hu
  · rw [min_eq_left hu.le, max_eq_right (by linarith [h.A0])]
    exact wSum_A h c
  · rw [min_eq_right (by linarith [h.A0]), max_eq_left (by linarith)]
    exact wSum_negA h c

omit h in
lemma continuous_wSum : Continuous (wSum M k c) := by
  unfold wSum
  exact continuous_finsetSum _ fun i _ => by fun_prop

omit h in
lemma continuous_bandM : Continuous (bandM A M k c) := by
  unfold bandM
  exact (continuous_wSum c).comp (by unfold clampA; fun_prop)

omit h in
lemma wSum_neg (u : ℝ) : wSum M k c (-u) = wSum M k c u := by
  unfold wSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_neg, Real.cos_neg]

lemma bandM_even (u : ℝ) : bandM A M k c (-u) = bandM A M k c u := by
  by_cases hu : |u| ≤ A
  · have hu' : |-u| ≤ A := by rwa [abs_neg]
    rw [bandM_of_mem c hu, bandM_of_mem c hu', wSum_neg]
  · rw [not_le] at hu
    have hu' : A < |-u| := by rwa [abs_neg]
    rw [bandM_of_gt h c hu, bandM_of_gt h c hu']

lemma tsupport_bandM : tsupport (fun u => ((bandM A M k c u : ℝ) : ℂ)) ⊆ Icc (-A) A := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hc
  apply hu
  have : A < |u| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
    · exact lt_of_lt_of_le hc (le_abs_self u)
  rw [bandM_of_gt h c this]
  simp

/-- The transform of the M-mode test is the real cosine sum of the one-mode transforms. -/
lemma paperFT_bandM (r : ℝ) :
    paperFT (fun u => ((bandM A M k c u : ℝ) : ℂ)) r
      = ((∑ i ∈ Finset.range M, c i * (∫ u in (-A)..A, Real.cos (k i * u) * Real.cos (r * u)) : ℝ) : ℂ) := by
  unfold paperFT
  have hA := h.A0
  have hvan : ∀ u ∉ Icc (-A) A, ((bandM A M k c u : ℝ) : ℂ) * Complex.exp (Complex.I * r * u) = 0 := by
    intro u hu
    have : A < |u| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le hu (le_abs_self u)
    rw [bandM_of_gt h c this]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ u ∈ uIcc (-A) A, ((bandM A M k c u : ℝ) : ℂ) * Complex.exp (Complex.I * r * u)
      = ((wSum M k c u * Real.cos (r * u) : ℝ) : ℂ)
        + ((wSum M k c u * Real.sin (r * u) : ℝ) : ℂ) * Complex.I := by
    intro u hu
    rw [uIcc_of_le (by linarith), mem_Icc] at hu
    rw [bandM_of_mem c (abs_le.mpr hu)]
    rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hw := continuous_wSum (M := M) (k := k) c
  have hi1 : IntervalIntegrable (fun u => ((wSum M k c u * Real.cos (r * u) : ℝ) : ℂ)) volume (-A) A :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hi2 : IntervalIntegrable (fun u => ((wSum M k c u * Real.sin (r * u) : ℝ) : ℂ) * Complex.I)
      volume (-A) A :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hsin : ∫ u in (-A)..A, wSum M k c u * Real.sin (r * u) = 0 := by
    apply integral_odd_sym
    intro u
    rw [wSum_neg, mul_neg, Real.sin_neg]
    ring
  rw [hsin]
  have hcos : ∫ u in (-A)..A, wSum M k c u * Real.cos (r * u)
      = ∑ i ∈ Finset.range M, c i * (∫ u in (-A)..A, Real.cos (k i * u) * Real.cos (r * u)) := by
    unfold wSum
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  rw [hcos]
  simp

end

/-- The one-mode decay bound for ANY `k > 0`:
`|int_{-A}^{A} cos(k u) cos(r u) du| <= Kk/(1 + r^2)`, `Kk = 2A(1 + 4k^2) + 8k/3 + 2/(3k)`. -/
lemma abs_integral_cos_cos_decay' {k A s : ℝ} (hA : 0 ≤ A) (hk : 0 < k) (hc : Real.cos (k * A) = 0)
    (hs : Real.sin (k * A) = s) (hs1 : |s| ≤ 1) (r : ℝ) :
    |∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)|
      ≤ (2 * A * (1 + 4 * k ^ 2) + (8 * k / 3 + 2 / (3 * k))) / (1 + r ^ 2) := by
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hB : 0 ≤ 8 * k / 3 + 2 / (3 * k) := by positivity
  rw [le_div_iff₀ hpos]
  by_cases hr : r ^ 2 < 4 * k ^ 2
  · have h1 := abs_integral_cos_cos_le k r A hA
    have h2 : 0 ≤ |∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)| := abs_nonneg _
    nlinarith
  · rw [not_lt] at hr
    have hk2 : k ^ 2 < r ^ 2 := by nlinarith
    have hkr1 : k - r ≠ 0 := by
      intro h0; have : r = k := by linarith
      rw [this] at hk2; exact lt_irrefl _ hk2
    have hkr2 : k + r ≠ 0 := by
      intro h0; have : r = -k := by linarith
      rw [this, neg_sq] at hk2; exact lt_irrefl _ hk2
    rw [integral_cos_cos_dirichlet hc hs hkr1 hkr2]
    have hden : 0 < r ^ 2 - k ^ 2 := by linarith
    rw [abs_div, abs_of_neg (by linarith : k ^ 2 - r ^ 2 < 0)]
    have hnum : |2 * s * k * Real.cos (r * A)| ≤ 2 * k := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hk]
      have hc1 := Real.abs_cos_le_one (r * A)
      calc 2 * |s| * k * |Real.cos (r * A)| = 2 * k * (|s| * |Real.cos (r * A)|) := by ring
        _ ≤ 2 * k * 1 :=
          mul_le_mul_of_nonneg_left (mul_le_one₀ hs1 (abs_nonneg _) hc1) (by linarith)
        _ = 2 * k := by ring
    rw [neg_sub, div_mul_eq_mul_div, div_le_iff₀ hden]
    -- (2k)(1 + r^2) <= (8k/3 + 2/(3k)) (r^2 - k^2)  since r^2 >= 4k^2
    have h3 : (2 * k) * (1 + r ^ 2) ≤ (8 * k / 3 + 2 / (3 * k)) * (r ^ 2 - k ^ 2) := by
      have e : (8 * k / 3 + 2 / (3 * k)) * (r ^ 2 - k ^ 2)
          = (2 * k) * (1 + r ^ 2) + ((2 * k / 3) * (r ^ 2 - 4 * k ^ 2) + (2 / (3 * k)) * (r ^ 2 - 4 * k ^ 2)) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ (2 * k / 3) * (r ^ 2 - 4 * k ^ 2) + (2 / (3 * k)) * (r ^ 2 - 4 * k ^ 2) := by
        have : 0 ≤ r ^ 2 - 4 * k ^ 2 := by linarith
        positivity
      linarith
    have h4 : 0 ≤ 2 * A * (1 + 4 * k ^ 2) * (r ^ 2 - k ^ 2) := by positivity
    nlinarith [abs_nonneg (2 * s * k * Real.cos (r * A))]

/-- The one-mode decay constant. -/
def Kmode (A k : ℝ) : ℝ := 2 * A * (1 + 4 * k ^ 2) + (8 * k / 3 + 2 / (3 * k))

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

/-- The decay bound of the M-mode test's transform. -/
lemma norm_paperFT_bandM_le (r : ℝ) :
    ‖paperFT (fun u => ((bandM A M k c u : ℝ) : ℂ)) r‖
      ≤ (∑ i ∈ Finset.range M, |c i| * Kmode A (k i)) / (1 + r ^ 2) := by
  rw [paperFT_bandM h c r, Complex.norm_real, Real.norm_eq_abs, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  rw [abs_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (abs_integral_cos_cos_decay' h.A0.le (h.kpos i hi') (h.cosk i hi')
    (h.sink i hi') (h.abs_s i hi') r) (abs_nonneg _)

/-- The M-mode test satisfies the Crux3 frequency-side hypotheses. -/
theorem bandM_freqData :
    FreqData (bandM A M k c) A (∑ i ∈ Finset.range M, |c i| * Kmode A (k i)) where
  cont := continuous_bandM c
  even := bandM_even h c
  supp := tsupport_bandM h c
  K0 := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hk := h.kpos i (Finset.mem_range.mp hi)
    have hA := h.A0
    unfold Kmode
    positivity
  decay := fun r => norm_paperFT_bandM_le h c r

end

/-! ## The autocorrelation in closed form -/

/-- The `(i, j)` block of the autocorrelation on `[0, 2A]`. -/
def blk (A : ℝ) (k s : ℕ → ℝ) (i j : ℕ) (y : ℝ) : ℝ :=
  if i = j then gD A (k i) y
  else s i * s j * (k i * Real.sin (k j * y) - k j * Real.sin (k i * y)) / (k i ^ 2 - k j ^ 2)

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

/-- The autocorrelation of the M-mode test on `[0, 2A]`. -/
theorem acR_bandM {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 2 * A) :
    acR (bandM A M k c) y
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, c i * c j * blk A k s i j y := by
  have hA := h.A0
  unfold acR
  have hvan : ∀ x ∉ Icc (y - A) A, bandM A M k c x * bandM A M k c (x - y) = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have : A < |x - y| := lt_of_lt_of_le (by linarith) (neg_le_abs (x - y))
      rw [bandM_of_gt h c this, mul_zero]
    · have : A < |x| := lt_of_lt_of_le hx (le_abs_self x)
      rw [bandM_of_gt h c this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ x ∈ uIcc (y - A) A, bandM A M k c x * bandM A M k c (x - y)
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c i * c j * (Real.cos (k i * x) * Real.cos (k j * (x - y))) := by
    intro x hx
    rw [uIcc_of_le (by linarith), mem_Icc] at hx
    rw [bandM_of_mem c (abs_le.mpr ⟨by linarith, hx.2⟩),
      bandM_of_mem c (abs_le.mpr ⟨by linarith, by linarith⟩)]
    unfold wSum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => Real.cos (a * x) * Real.cos (b * (x - y))) volume (y - A) A :=
    fun a b => Continuous.intervalIntegrable (by fun_prop) _ _
  have hsum : ∀ i : ℕ, IntervalIntegrable
      (fun x => ∑ j ∈ Finset.range M, c i * c j * (Real.cos (k i * x) * Real.cos (k j * (x - y)))) volume (y - A) A :=
    fun i => Continuous.intervalIntegrable (continuous_finsetSum _ fun j _ => by fun_prop) _ _
  rw [intervalIntegral.integral_finsetSum (fun i _ => hsum i)]
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hi _ _).const_mul _)]
  refine Finset.sum_congr rfl fun j hj' => ?_
  rw [intervalIntegral.integral_const_mul]
  have hiM := Finset.mem_range.mp hi'
  have hjM := Finset.mem_range.mp hj'
  congr 1
  unfold blk
  split_ifs with hij
  · subst hij
    rw [diag_block (h.cosk i hiM) (h.kpos i hiM).ne']
    rfl
  · have hne := h.kinj i hiM j hjM hij
    have hd : k i - k j ≠ 0 := sub_ne_zero.mpr hne
    have hs : k i + k j ≠ 0 := by linarith [h.kpos i hiM, h.kpos j hjM]
    exact cross_block (h.cosk i hiM) (h.cosk j hjM) (h.sink i hiM) (h.sink j hjM) hd hs

/-- `g(0) = A sum c_i^2` (orthogonality of Dirichlet cosines). -/
theorem acR_bandM_zero : acR (bandM A M k c) 0 = A * ∑ i ∈ Finset.range M, c i ^ 2 := by
  rw [acR_bandM h c le_rfl (by linarith [h.A0]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · unfold blk gD; simp; ring
  · intro j _ hji
    unfold blk
    rw [if_neg (Ne.symm hji)]
    simp
  · intro hi'; exact absurd hi hi'

end

/-! ## The Lorentzian terms in closed form -/

/-- The `(i, j)` Lorentzian block `2 int_0^{2A} blk_ij(y) e^{-2by} dy`. -/
def lblk (A : ℝ) (k s : ℕ → ℝ) (i j : ℕ) (b : ℝ) : ℝ :=
  if i = j then Jd A (k i) b else Jx A (k i) (k j) (s i) (s j) b

lemma integral_blk {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) {i j : ℕ} (hi : i < M) (hj : j < M)
    {b : ℝ} (hb : 0 < b) :
    ∫ t in (0 : ℝ)..(2 * A), blk A k s i j t * Real.exp (-(2 * b) * t) = lblk A k s i j b / 2 := by
  have hki := h.kpos i hi
  have hkj := h.kpos j hj
  have hDi : 0 < (2 * b) ^ 2 + k i ^ 2 := by positivity
  have hDj : 0 < (2 * b) ^ 2 + k j ^ 2 := by positivity
  have ci := cos_two_kA (h.cosk i hi)
  have si := sin_two_kA (h.cosk i hi)
  have cj := cos_two_kA (h.cosk j hj)
  have sj := sin_two_kA (h.cosk j hj)
  have iE : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 (2 * A) :=
    fun f hf => hf.intervalIntegrable _ _
  have e4 : ∀ kk : ℝ, 4 * b ^ 2 + kk ^ 2 = (2 * b) ^ 2 + kk ^ 2 := fun kk => by ring
  unfold blk lblk
  split_ifs with hij
  · subst hij
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) (2 * A), gD A (k i) t * Real.exp (-(2 * b) * t)
        = A * (Real.exp (-(2 * b) * t) * Real.cos (k i * t))
          - (1 / 2) * (t * (Real.exp (-(2 * b) * t) * Real.cos (k i * t)))
          + (1 / (2 * k i)) * (Real.exp (-(2 * b) * t) * Real.sin (k i * t)) := by
      intro t _
      unfold gD
      field_simp
      try ring
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add ((iE _ (by fun_prop)).sub (iE _ (by fun_prop))) (iE _ (by fun_prop)),
      intervalIntegral.integral_sub (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_exp_cos hDi ci si, integral_y_exp_cos hDi ci si, integral_exp_sin hDi ci si]
    unfold Jd
    rw [e4]
    generalize Real.exp (-(2 * b) * (2 * A)) = E
    field_simp
    try ring
  · have hne := h.kinj i hi j hj hij
    have h4 : k i ^ 2 - k j ^ 2 ≠ 0 := by
      rw [show k i ^ 2 - k j ^ 2 = (k i - k j) * (k i + k j) by ring]
      exact mul_ne_zero (sub_ne_zero.mpr hne) (by linarith)
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) (2 * A),
        s i * s j * (k i * Real.sin (k j * t) - k j * Real.sin (k i * t)) / (k i ^ 2 - k j ^ 2)
          * Real.exp (-(2 * b) * t)
        = (s i * s j * k i / (k i ^ 2 - k j ^ 2)) * (Real.exp (-(2 * b) * t) * Real.sin (k j * t))
          - (s i * s j * k j / (k i ^ 2 - k j ^ 2)) * (Real.exp (-(2 * b) * t) * Real.sin (k i * t)) := by
      intro t _
      field_simp
      try ring
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_sub (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_exp_sin hDj cj sj, integral_exp_sin hDi ci si]
    unfold Jx
    rw [e4, e4]
    generalize Real.exp (-(2 * b) * (2 * A)) = E
    field_simp
    try ring

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

/-- The `b`-Lorentzian term of the M-mode test as a double sum of blocks (any `b > 0`). -/
theorem lorTermB_bandM_blocks (b : ℝ) (hb0 : 0 < b) :
    lorTermB (bandM A M k c) b
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, c i * c j * lblk A k s i j b := by
  have hv := bandM_freqData h c
  have hA := h.A0
  unfold lorTermB
  have e1 : (fun y => acR (bandM A M k c) y * Real.exp (-2 * b * |y|))
      = fun y => (fun t => acR (bandM A M k c) t * Real.exp (-(2 * b) * t)) |y| := by
    funext y
    simp only
    rcases abs_choice y with hy | hy
    · rw [hy]; ring_nf
    · rw [hy, hv.acR_neg]; ring_nf
  rw [e1, integral_comp_abs (f := fun t => acR (bandM A M k c) t * Real.exp (-(2 * b) * t))]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (2 * A) ⊆ Ioi 0) (fun t ht => by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and_or, not_le] at ht
      rcases ht.2 with h1 | h1
      · exact absurd ht.1 (not_lt.mpr (le_of_lt (lt_of_le_of_lt (le_refl t) (by linarith))))
      · rw [hv.acR_eq_zero (by rw [abs_of_pos ht.1]; exact h1.le), zero_mul])]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) (2 * A), acR (bandM A M k c) t * Real.exp (-(2 * b) * t)
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c i * c j * (blk A k s i j t * Real.exp (-(2 * b) * t)) := by
    intro t ht
    rw [uIcc_of_le (by linarith), mem_Icc] at ht
    rw [acR_bandM h c ht.1 ht.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hcb : ∀ i j : ℕ, Continuous (fun t => blk A k s i j t * Real.exp (-(2 * b) * t)) := by
    intro i j
    unfold blk gD
    split_ifs <;> fun_prop
  have hsum : ∀ i : ℕ, IntervalIntegrable
      (fun t => ∑ j ∈ Finset.range M, c i * c j * (blk A k s i j t * Real.exp (-(2 * b) * t))) volume 0 (2 * A) :=
    fun i => Continuous.intervalIntegrable (continuous_finsetSum _ fun j _ => (hcb i j).const_mul _) _ _
  rw [intervalIntegral.integral_finsetSum (fun i _ => hsum i)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum (fun j _ => ((hcb i j).intervalIntegrable _ _).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [intervalIntegral.integral_const_mul,
    integral_blk h (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hb0]
  ring

/-- **The Lorentzian term in square form**: for every `b > 0`,
`lorTermB v b = 4 b A sum_i c_i^2/(4b^2 + k_i^2) + 2 (1 + e^{-4bA}) (sum_i c_i s_i k_i/(4b^2 + k_i^2))^2`. -/
theorem lorTermB_bandM (b : ℝ) (hb0 : 0 < b) :
    lorTermB (bandM A M k c) b
      = 4 * b * A * (∑ i ∈ Finset.range M, c i ^ 2 / (4 * b ^ 2 + k i ^ 2))
        + 2 * (1 + Real.exp (-(2 * b) * (2 * A)))
          * (∑ i ∈ Finset.range M, c i * s i * k i / (4 * b ^ 2 + k i ^ 2)) ^ 2 := by
  rw [lorTermB_bandM_blocks h c b hb0]
  set E := Real.exp (-(2 * b) * (2 * A)) with hE
  have hD : ∀ i, i < M → 0 < 4 * b ^ 2 + k i ^ 2 := fun i hi => by
    have := h.kpos i hi; positivity
  -- expand every block into the diagonal part plus a rank-one part
  have hblock : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M,
      c i * c j * lblk A k s i j b
        = (if i = j then 4 * b * A * (c j ^ 2 / (4 * b ^ 2 + k j ^ 2)) else 0)
          + 2 * (1 + E) * ((c i * s i * k i / (4 * b ^ 2 + k i ^ 2)) * (c j * s j * k j / (4 * b ^ 2 + k j ^ 2))) := by
    intro i hi j hj
    have hiM := Finset.mem_range.mp hi
    have hjM := Finset.mem_range.mp hj
    have hDi := hD i hiM
    have hDj := hD j hjM
    unfold lblk Jd Jx
    split_ifs with hij
    · subst hij
      rw [← hE]
      have hs2 := h.s_sq i hiM
      field_simp
      rw [show s i ^ 2 = 1 from hs2]
      ring
    · rw [← hE]
      field_simp
      ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hblock i hi j hj]
  simp_rw [Finset.sum_add_distrib]
  have hdiag : ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      (if i = j then 4 * b * A * (c j ^ 2 / (4 * b ^ 2 + k j ^ 2)) else 0)
      = 4 * b * A * ∑ i ∈ Finset.range M, c i ^ 2 / (4 * b ^ 2 + k i ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, if_pos hi]
  rw [hdiag]
  congr 1
  have hsq : ∀ (x : ℝ) (f : ℕ → ℝ), x * (∑ i ∈ Finset.range M, f i) ^ 2
      = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M, x * (f i * f j) := by
    intro x f
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [hsq]

end

/-! ## The pole integral in closed form -/

/-- `int_{-A}^{A} cos(k u) e^{-u/2} du = 2 k s cosh(A/2)/(k^2 + 1/4)` for a Dirichlet cosine. -/
lemma integral_cos_exp_half {k A s : ℝ} (hc : Real.cos (k * A) = 0) (hs : Real.sin (k * A) = s) :
    ∫ u in (-A)..A, Real.cos (k * u) * Real.exp (-(1 / 2) * u)
      = 2 * k * s * Real.cosh (A / 2) / (k ^ 2 + 1 / 4) := by
  have hD : 0 < k ^ 2 + 1 / 4 := by positivity
  have key : ∀ y : ℝ, HasDerivAt
      (fun y => Real.exp (-(1 / 2) * y) * (k * Real.sin (k * y) - (1 / 2) * Real.cos (k * y)) / (k ^ 2 + 1 / 4))
      (Real.cos (k * y) * Real.exp (-(1 / 2) * y)) y := by
    intro y
    have e1 : HasDerivAt (fun y => Real.exp (-(1 / 2) * y)) (Real.exp (-(1 / 2) * y) * (-(1 / 2) * 1)) y :=
      ((hasDerivAt_id y).const_mul (-(1 / 2))).exp
    have s1 : HasDerivAt (fun y => Real.sin (k * y)) (Real.cos (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).sin
    have c1 : HasDerivAt (fun y => Real.cos (k * y)) (-Real.sin (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).cos
    have := ((e1.mul ((s1.const_mul k).sub (c1.const_mul (1 / 2)))).div_const (k ^ 2 + 1 / 4))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => key y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_neg, Real.sin_neg, Real.cos_neg, hc, hs]
  rw [Real.cosh_eq]
  have e1 : -(1 / 2 : ℝ) * A = -(A / 2) := by ring
  simp only [e1, neg_neg]
  field_simp
  ring

/-- The pole value `P(v) = sum_i c_i 2 k_i s_i cosh(A/2)/(k_i^2 + 1/4)`. -/
def poleVal (A : ℝ) (M : ℕ) (k s c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, c i * (2 * k i * s i * Real.cosh (A / 2) / (k i ^ 2 + 1 / 4))

section
variable {A : ℝ} {M : ℕ} {k s : ℕ → ℝ} (h : ModeHyp A M k s) (c : ℕ → ℝ)
include h

/-- `int v(u) e^{-u/2} du = P(v)` for the M-mode test. -/
theorem integral_bandM_exp_half :
    ∫ u, bandM A M k c u * Real.exp (-(1 / 2) * u) = poleVal A M k s c := by
  have hA := h.A0
  have hvan : ∀ u ∉ Icc (-A) A, bandM A M k c u * Real.exp (-(1 / 2) * u) = 0 := by
    intro u hu
    have : A < |u| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le hu (le_abs_self u)
    rw [bandM_of_gt h c this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ u ∈ uIcc (-A) A, bandM A M k c u * Real.exp (-(1 / 2) * u)
      = ∑ i ∈ Finset.range M, c i * (Real.cos (k i * u) * Real.exp (-(1 / 2) * u)) := by
    intro u hu
    rw [uIcc_of_le (by linarith), mem_Icc] at hu
    rw [bandM_of_mem c (abs_le.mpr hu)]
    unfold wSum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold poleVal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiM := Finset.mem_range.mp hi
  rw [intervalIntegral.integral_const_mul, integral_cos_exp_half (h.cosk i hiM) (h.sink i hiM)]

end

end CF
