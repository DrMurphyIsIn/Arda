/-
  Crux3_BandTest -- the Dirichlet-cosine band test and its closed forms (rvm_bridge island,
  2026-09-24, crux lane 3).

  conjecture1_proved = False.  Pure real analysis on one explicit family of test functions.

  THE TEST.  For frequencies `k1 < k2` with `cos(k_i A) = 0`, `sin(k_i A) = s_i` (`PairHyp`), the band
  test `bandV A k1 k2 c1 c2 = wPair o clampA`, `wPair(u) = c1 cos(k1 u) + c2 cos(k2 u)`, equals `wPair`
  on `[-A, A]` and vanishes outside; it is continuous (Lipschitz) but NOT smooth, so it lies outside the
  registry's `IsWeilTest` class; the Weil functional `archSide - primeSide` is nevertheless defined on
  its autocorrelation, and `Crux3_BandAnalytic` bounds it.

  PROVED (all hypothesis-free given `PairHyp`):
    * `bandV_freqData`: the `FreqData` hypotheses (continuity, evenness, support, and the transform
      decay `K/(1 + r^2)` from the closed form `int cos(k u) cos(r u) = 2 s k cos(rA)/(k^2 - r^2)`);
    * `acR_bandV`: the autocorrelation on `[0, 2A]` is `c1^2 gD(k1) + 2 c1 c2 gX + c2^2 gD(k2)`,
      `gD(k, y) = (2A - y) cos(ky)/2 + sin(ky)/(2k)`, `gX = s1 s2 (k1 sin(k2 y) - k2 sin(k1 y))/(k1^2 - k2^2)`;
      `acR_bandV_zero`: `g(0) = A (c1^2 + c2^2)` (orthogonality);
    * `lorTerm_bandV`: each Lorentzian term `int g(y) e^{-2b|y|} dy` in closed form,
      `Jd(k, b) = 2A 2b/(4b^2 + k^2) + 2k^2 (1 + e^{-4bA})/(4b^2 + k^2)^2`,
      `Jx(b) = 2 s1 s2 k1 k2 (1 + e^{-4bA})/((4b^2 + k1^2)(4b^2 + k2^2))`
      (three FTC primitives of `e^{-by} cos`, `e^{-by} sin`, `y e^{-by} cos`).
  No `sorry`.
-/
import Crux3_BandAnalytic

open MeasureTheory Complex Zeta23 Set Filter
open scoped ComplexConjugate

noncomputable section

namespace Crux3
/-! ## Part B: the band test -/


/-- The clamp of `u` to `[-A, A]`. -/
def clampA (A u : ℝ) : ℝ := max (-A) (min A u)

/-- The cosine pair `w(u) = c1 cos(k1 u) + c2 cos(k2 u)`. -/
def wPair (k1 k2 c1 c2 u : ℝ) : ℝ := c1 * Real.cos (k1 * u) + c2 * Real.cos (k2 * u)

/-- The band test `v = w ∘ clamp`: it equals `w` on `[-A, A]` and vanishes outside because
`cos(k_i A) = 0` (Dirichlet cosines), and it is continuous. -/
def bandV (A k1 k2 c1 c2 : ℝ) (u : ℝ) : ℝ := wPair k1 k2 c1 c2 (clampA A u)

/-- The Dirichlet hypotheses on the pair of frequencies. -/
structure PairHyp (A k1 k2 s1 s2 : ℝ) : Prop where
  A0 : 0 < A
  k10 : 0 < k1
  k20 : 0 < k2
  k12 : k1 < k2
  k1one : 1 ≤ k1
  cos1 : Real.cos (k1 * A) = 0
  cos2 : Real.cos (k2 * A) = 0
  sin1 : Real.sin (k1 * A) = s1
  sin2 : Real.sin (k2 * A) = s2

section
variable {A k1 k2 s1 s2 : ℝ} (h : PairHyp A k1 k2 s1 s2) (c1 c2 : ℝ)
include h

omit h in
lemma clampA_of_mem {u : ℝ} (hu : |u| ≤ A) : clampA A u = u := by
  unfold clampA
  rw [abs_le] at hu
  rw [min_eq_right hu.2, max_eq_right hu.1]

lemma wPair_A : wPair k1 k2 c1 c2 A = 0 := by
  unfold wPair
  rw [h.cos1, h.cos2]
  ring

lemma wPair_negA : wPair k1 k2 c1 c2 (-A) = 0 := by
  unfold wPair
  rw [mul_neg, mul_neg, Real.cos_neg, Real.cos_neg, h.cos1, h.cos2]
  ring

omit h in
lemma bandV_of_mem {u : ℝ} (hu : |u| ≤ A) : bandV A k1 k2 c1 c2 u = wPair k1 k2 c1 c2 u := by
  unfold bandV
  rw [clampA_of_mem hu]

lemma bandV_of_gt {u : ℝ} (hu : A < |u|) : bandV A k1 k2 c1 c2 u = 0 := by
  unfold bandV clampA
  rcases lt_abs.mp hu with hu | hu
  · rw [min_eq_left hu.le, max_eq_right (by linarith [h.A0])]
    exact wPair_A h c1 c2
  · rw [min_eq_right (by linarith [h.A0]), max_eq_left (by linarith)]
    exact wPair_negA h c1 c2

omit h in
lemma continuous_bandV : Continuous (bandV A k1 k2 c1 c2) := by
  unfold bandV wPair clampA
  fun_prop

lemma bandV_even (u : ℝ) : bandV A k1 k2 c1 c2 (-u) = bandV A k1 k2 c1 c2 u := by
  by_cases hu : |u| ≤ A
  · have hu' : |-u| ≤ A := by rwa [abs_neg]
    rw [bandV_of_mem c1 c2 hu, bandV_of_mem c1 c2 hu']
    unfold wPair
    rw [mul_neg, mul_neg, Real.cos_neg, Real.cos_neg]
  · rw [not_le] at hu
    have hu' : A < |-u| := by rwa [abs_neg]
    rw [bandV_of_gt h c1 c2 hu, bandV_of_gt h c1 c2 hu']

lemma tsupport_bandV : tsupport (fun u => ((bandV A k1 k2 c1 c2 u : ℝ) : ℂ)) ⊆ Icc (-A) A := by
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
  rw [bandV_of_gt h c1 c2 this]
  simp


omit h in
lemma integral_cos_mul_sym {α : ℝ} (hα : α ≠ 0) (A : ℝ) :
    ∫ u in (-A)..A, Real.cos (α * u) = 2 * Real.sin (α * A) / α := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hα, integral_cos, mul_neg,
    Real.sin_neg, smul_eq_mul]
  field_simp
  ring

omit h in
lemma cos_mul_cos_eq (a b : ℝ) : Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

omit h in
lemma integral_cos_cos_sym {k r : ℝ} (A : ℝ) (h1 : k - r ≠ 0) (h2 : k + r ≠ 0) :
    ∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)
      = Real.sin ((k - r) * A) / (k - r) + Real.sin ((k + r) * A) / (k + r) := by
  have e : (fun u => Real.cos (k * u) * Real.cos (r * u))
      = fun u => (1 / 2) * Real.cos ((k - r) * u) + (1 / 2) * Real.cos ((k + r) * u) := by
    funext u
    rw [cos_mul_cos_eq]
    ring_nf
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_mul_sym h1, integral_cos_mul_sym h2]
  · ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

omit h in
/-- The cosine transform of one Dirichlet cosine: `int_{-A}^{A} cos(k u) cos(r u) du
= 2 s k cos(r A)/(k^2 - r^2)` for `r^2 != k^2` (`cos(kA) = 0`, `sin(kA) = s`). -/
lemma integral_cos_cos_dirichlet {k r A s : ℝ} (hc : Real.cos (k * A) = 0) (hs : Real.sin (k * A) = s)
    (h1 : k - r ≠ 0) (h2 : k + r ≠ 0) :
    ∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u) = 2 * s * k * Real.cos (r * A) / (k ^ 2 - r ^ 2) := by
  rw [integral_cos_cos_sym A h1 h2]
  have e1 : Real.sin ((k - r) * A) = s * Real.cos (r * A) := by
    rw [show (k - r) * A = k * A - r * A by ring, Real.sin_sub, hc, hs]; ring
  have e2 : Real.sin ((k + r) * A) = s * Real.cos (r * A) := by
    rw [show (k + r) * A = k * A + r * A by ring, Real.sin_add, hc, hs]; ring
  rw [e1, e2]
  have h3 : k ^ 2 - r ^ 2 = (k - r) * (k + r) := by ring
  rw [h3]
  field_simp
  ring

omit h in
lemma abs_integral_cos_cos_le (k r A : ℝ) (hA : 0 ≤ A) :
    |∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)| ≤ 2 * A := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -A) (b := A) (C := 1)
    (f := fun u => Real.cos (k * u) * Real.cos (r * u)) (fun u _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
  rw [Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A - -A)] at h
  linarith

omit h in
/-- The one-mode decay bound `|C(k, r)| <= Kk/(1 + r^2)`, `Kk = 2A(1 + 4k^2) + 16k/3`. -/
lemma abs_integral_cos_cos_decay {k A s : ℝ} (hA : 0 ≤ A) (hk : 1 ≤ k) (hc : Real.cos (k * A) = 0)
    (hs : Real.sin (k * A) = s) (hs1 : |s| ≤ 1) (r : ℝ) :
    |∫ u in (-A)..A, Real.cos (k * u) * Real.cos (r * u)| ≤ (2 * A * (1 + 4 * k ^ 2) + 16 * k / 3) / (1 + r ^ 2) := by
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
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
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < k)]
      have hc1 := Real.abs_cos_le_one (r * A)
      calc 2 * |s| * k * |Real.cos (r * A)| = 2 * k * (|s| * |Real.cos (r * A)|) := by ring
        _ ≤ 2 * k * 1 :=
          mul_le_mul_of_nonneg_left (mul_le_one₀ hs1 (abs_nonneg _) hc1) (by linarith)
        _ = 2 * k := by ring
    rw [neg_sub, div_mul_eq_mul_div, div_le_iff₀ hden]
    have h3 : (2 * k) * (1 + r ^ 2) ≤ (16 * k / 3) * (r ^ 2 - k ^ 2) := by nlinarith
    have h4 : 0 ≤ 2 * A * (1 + 4 * k ^ 2) * (r ^ 2 - k ^ 2) := by positivity
    nlinarith [abs_nonneg (2 * s * k * Real.cos (r * A))]


omit h in
lemma integral_odd_sym {f : ℝ → ℝ} (hf : ∀ u, f (-u) = -f u) (A : ℝ) : ∫ u in (-A)..A, f u = 0 := by
  have h1 := intervalIntegral.integral_comp_neg (a := -A) (b := A) f
  rw [neg_neg] at h1
  have h2 : ∫ u in (-A)..A, f (-u) = -∫ u in (-A)..A, f u := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun u _ => hf u)
  linarith

/-- The transform of the band test is the real cosine integral of the pair. -/
lemma paperFT_bandV (r : ℝ) :
    paperFT (fun u => ((bandV A k1 k2 c1 c2 u : ℝ) : ℂ)) r
      = ((c1 * (∫ u in (-A)..A, Real.cos (k1 * u) * Real.cos (r * u))
          + c2 * (∫ u in (-A)..A, Real.cos (k2 * u) * Real.cos (r * u)) : ℝ) : ℂ) := by
  unfold paperFT
  have hA := h.A0
  have hvan : ∀ u ∉ Icc (-A) A, ((bandV A k1 k2 c1 c2 u : ℝ) : ℂ) * Complex.exp (Complex.I * r * u) = 0 := by
    intro u hu
    have : A < |u| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le hu (le_abs_self u)
    rw [bandV_of_gt h c1 c2 this]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ u ∈ uIcc (-A) A, ((bandV A k1 k2 c1 c2 u : ℝ) : ℂ) * Complex.exp (Complex.I * r * u)
      = ((wPair k1 k2 c1 c2 u * Real.cos (r * u) : ℝ) : ℂ)
        + ((wPair k1 k2 c1 c2 u * Real.sin (r * u) : ℝ) : ℂ) * Complex.I := by
    intro u hu
    rw [uIcc_of_le (by linarith), mem_Icc] at hu
    rw [bandV_of_mem c1 c2 (abs_le.mpr hu)]
    rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hi1 : IntervalIntegrable (fun u => ((wPair k1 k2 c1 c2 u * Real.cos (r * u) : ℝ) : ℂ)) volume (-A) A :=
    (Continuous.intervalIntegrable (by unfold wPair; fun_prop) _ _)
  have hi2 : IntervalIntegrable (fun u => ((wPair k1 k2 c1 c2 u * Real.sin (r * u) : ℝ) : ℂ) * Complex.I)
      volume (-A) A :=
    (Continuous.intervalIntegrable (by unfold wPair; fun_prop) _ _)
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hsin : ∫ u in (-A)..A, wPair k1 k2 c1 c2 u * Real.sin (r * u) = 0 := by
    apply integral_odd_sym
    intro u
    unfold wPair
    rw [mul_neg, mul_neg, mul_neg, Real.cos_neg, Real.cos_neg, Real.sin_neg]
    ring
  rw [hsin]
  have hcos : ∫ u in (-A)..A, wPair k1 k2 c1 c2 u * Real.cos (r * u)
      = c1 * (∫ u in (-A)..A, Real.cos (k1 * u) * Real.cos (r * u))
        + c2 * (∫ u in (-A)..A, Real.cos (k2 * u) * Real.cos (r * u)) := by
    unfold wPair
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · congr 1
      funext u
      ring
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hcos]
  simp

/-- The decay bound of the band test's transform. -/
lemma norm_paperFT_bandV_le (r : ℝ) (hs1 : |s1| ≤ 1) (hs2 : |s2| ≤ 1) :
    ‖paperFT (fun u => ((bandV A k1 k2 c1 c2 u : ℝ) : ℂ)) r‖
      ≤ (|c1| * (2 * A * (1 + 4 * k1 ^ 2) + 16 * k1 / 3) + |c2| * (2 * A * (1 + 4 * k2 ^ 2) + 16 * k2 / 3))
        / (1 + r ^ 2) := by
  rw [paperFT_bandV h c1 c2 r, Complex.norm_real, Real.norm_eq_abs]
  have hA := h.A0.le
  have hk2 : 1 ≤ k2 := le_trans h.k1one h.k12.le
  have d1 := abs_integral_cos_cos_decay hA h.k1one h.cos1 h.sin1 hs1 r
  have d2 := abs_integral_cos_cos_decay hA hk2 h.cos2 h.sin2 hs2 r
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  calc |c1 * (∫ u in (-A)..A, Real.cos (k1 * u) * Real.cos (r * u))
        + c2 * (∫ u in (-A)..A, Real.cos (k2 * u) * Real.cos (r * u))|
      ≤ |c1| * |∫ u in (-A)..A, Real.cos (k1 * u) * Real.cos (r * u)|
        + |c2| * |∫ u in (-A)..A, Real.cos (k2 * u) * Real.cos (r * u)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |c1| * ((2 * A * (1 + 4 * k1 ^ 2) + 16 * k1 / 3) / (1 + r ^ 2))
        + |c2| * ((2 * A * (1 + 4 * k2 ^ 2) + 16 * k2 / 3) / (1 + r ^ 2)) := by
        gcongr
    _ = _ := by field_simp

end


/-! ## Part C: autocorrelation blocks -/


/-- Primitive for `cos(a x) cos(b (x - y))`, `a != b`, `a + b != 0`. -/
lemma integral_cos_cos_shift {a b : ℝ} (y p q : ℝ) (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ∫ x in p..q, Real.cos (a * x) * Real.cos (b * (x - y))
      = (Real.sin ((a - b) * q + b * y) / (2 * (a - b)) + Real.sin ((a + b) * q - b * y) / (2 * (a + b)))
        - (Real.sin ((a - b) * p + b * y) / (2 * (a - b)) + Real.sin ((a + b) * p - b * y) / (2 * (a + b))) := by
  have key : ∀ x : ℝ, HasDerivAt
      (fun x => Real.sin ((a - b) * x + b * y) / (2 * (a - b)) + Real.sin ((a + b) * x - b * y) / (2 * (a + b)))
      (Real.cos (a * x) * Real.cos (b * (x - y))) x := by
    intro x
    have d1 : HasDerivAt (fun x => Real.sin ((a - b) * x + b * y) / (2 * (a - b)))
        (Real.cos ((a - b) * x + b * y) * ((a - b) * 1) / (2 * (a - b))) x :=
      ((((hasDerivAt_id x).const_mul (a - b)).add_const (b * y)).sin).div_const (2 * (a - b))
    have d2 : HasDerivAt (fun x => Real.sin ((a + b) * x - b * y) / (2 * (a + b)))
        (Real.cos ((a + b) * x - b * y) * ((a + b) * 1) / (2 * (a + b))) x :=
      ((((hasDerivAt_id x).const_mul (a + b)).sub_const (b * y)).sin).div_const (2 * (a + b))
    refine (d1.add d2).congr_deriv ?_
    have c1 : Real.cos ((a - b) * x + b * y) * ((a - b) * 1) / (2 * (a - b)) = Real.cos (a * x - b * (x - y)) / 2 := by
      rw [show (a - b) * x + b * y = a * x - b * (x - y) by ring]; field_simp
    have c2 : Real.cos ((a + b) * x - b * y) * ((a + b) * 1) / (2 * (a + b)) = Real.cos (a * x + b * (x - y)) / 2 := by
      rw [show (a + b) * x - b * y = a * x + b * (x - y) by ring]; field_simp
    rw [c1, c2, Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- Primitive for `cos(a x) cos(a (x - y))`, `a != 0`. -/
lemma integral_cos_cos_shift_diag {a : ℝ} (y p q : ℝ) (ha : a ≠ 0) :
    ∫ x in p..q, Real.cos (a * x) * Real.cos (a * (x - y))
      = (q * Real.cos (a * y) / 2 + Real.sin (2 * a * q - a * y) / (4 * a))
        - (p * Real.cos (a * y) / 2 + Real.sin (2 * a * p - a * y) / (4 * a)) := by
  have key : ∀ x : ℝ, HasDerivAt
      (fun x => x * Real.cos (a * y) / 2 + Real.sin (2 * a * x - a * y) / (4 * a))
      (Real.cos (a * x) * Real.cos (a * (x - y))) x := by
    intro x
    have d1 : HasDerivAt (fun x => x * Real.cos (a * y) / 2) (1 * Real.cos (a * y) / 2) x :=
      ((hasDerivAt_id x).mul_const (Real.cos (a * y))).div_const 2
    have d2 : HasDerivAt (fun x => Real.sin (2 * a * x - a * y) / (4 * a))
        (Real.cos (2 * a * x - a * y) * ((2 * a) * 1) / (4 * a)) x :=
      ((((hasDerivAt_id x).const_mul (2 * a)).sub_const (a * y)).sin).div_const (4 * a)
    refine (d1.add d2).congr_deriv ?_
    have c2 : Real.cos (2 * a * x - a * y) * ((2 * a) * 1) / (4 * a) = Real.cos (a * x + a * (x - y)) / 2 := by
      rw [show 2 * a * x - a * y = a * x + a * (x - y) by ring]; field_simp; ring
    rw [c2, Real.cos_add, show a * y = a * x - a * (x - y) by ring, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]

/-- The off-diagonal autocorrelation block on `[y - A, A]` (Dirichlet: `cos(aA) = cos(bA) = 0`). -/
lemma cross_block {a b A sa sb y : ℝ} (ha : Real.cos (a * A) = 0) (hb : Real.cos (b * A) = 0)
    (hsa : Real.sin (a * A) = sa) (hsb : Real.sin (b * A) = sb) (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ∫ x in (y - A)..A, Real.cos (a * x) * Real.cos (b * (x - y))
      = sa * sb * (a * Real.sin (b * y) - b * Real.sin (a * y)) / (a ^ 2 - b ^ 2) := by
  rw [integral_cos_cos_shift y (y - A) A h1 h2]
  have e1 : Real.sin ((a - b) * A + b * y) = sa * sb * Real.sin (b * y) := by
    rw [show (a - b) * A + b * y = a * A - (b * A - b * y) by ring, Real.sin_sub, Real.cos_sub,
      Real.sin_sub, ha, hb, hsa, hsb]
    ring
  have e2 : Real.sin ((a + b) * A - b * y) = sa * sb * Real.sin (b * y) := by
    rw [show (a + b) * A - b * y = a * A + (b * A - b * y) by ring, Real.sin_add, Real.cos_sub,
      Real.sin_sub, ha, hb, hsa, hsb]
    ring
  have e3 : Real.sin ((a - b) * (y - A) + b * y) = sa * sb * Real.sin (a * y) := by
    rw [show (a - b) * (y - A) + b * y = a * y + (b * A - a * A) by ring, Real.sin_add, Real.cos_sub,
      Real.sin_sub, ha, hb, hsa, hsb]
    ring
  have e4 : Real.sin ((a + b) * (y - A) - b * y) = -(sa * sb * Real.sin (a * y)) := by
    rw [show (a + b) * (y - A) - b * y = a * y - (a * A + b * A) by ring, Real.sin_sub, Real.cos_add,
      Real.sin_add, ha, hb, hsa, hsb]
    ring
  rw [e1, e2, e3, e4]
  have h3 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [h3]
  field_simp
  ring

/-- The diagonal autocorrelation block on `[y - A, A]`. -/
lemma diag_block {a A y : ℝ} (ha : Real.cos (a * A) = 0) (ha0 : a ≠ 0) :
    ∫ x in (y - A)..A, Real.cos (a * x) * Real.cos (a * (x - y))
      = (2 * A - y) * Real.cos (a * y) / 2 + Real.sin (a * y) / (2 * a) := by
  rw [integral_cos_cos_shift_diag y (y - A) A ha0]
  have hc2 : Real.cos (2 * (a * A)) = -1 := by rw [Real.cos_two_mul, ha]; ring
  have hs2 : Real.sin (2 * (a * A)) = 0 := by rw [Real.sin_two_mul, ha]; ring
  have e1 : Real.sin (2 * a * A - a * y) = Real.sin (a * y) := by
    rw [show 2 * a * A - a * y = 2 * (a * A) - a * y by ring, Real.sin_sub, hc2, hs2]; ring
  have e2 : Real.sin (2 * a * (y - A) - a * y) = -Real.sin (a * y) := by
    rw [show 2 * a * (y - A) - a * y = a * y - 2 * (a * A) by ring, Real.sin_sub, hc2, hs2]; ring
  rw [e1, e2]
  field_simp
  ring


/-! ## Part D: the band autocorrelation and the Lorentzian terms in closed form -/

/-- The diagonal block `(2A - y) cos(k y)/2 + sin(k y)/(2k)`. -/
def gD (A k y : ℝ) : ℝ := (2 * A - y) * Real.cos (k * y) / 2 + Real.sin (k * y) / (2 * k)

/-- The cross block `s1 s2 (k1 sin(k2 y) - k2 sin(k1 y))/(k1^2 - k2^2)`. -/
def gX (k1 k2 s1 s2 y : ℝ) : ℝ := s1 * s2 * (k1 * Real.sin (k2 * y) - k2 * Real.sin (k1 * y)) / (k1 ^ 2 - k2 ^ 2)

section
variable {A k1 k2 s1 s2 : ℝ} (h : PairHyp A k1 k2 s1 s2) (c1 c2 : ℝ)
include h

/-- The autocorrelation of the band test on `[0, 2A]`, in closed form. -/
theorem acR_bandV {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 2 * A) :
    acR (bandV A k1 k2 c1 c2) y
      = c1 ^ 2 * gD A k1 y + 2 * c1 * c2 * gX k1 k2 s1 s2 y + c2 ^ 2 * gD A k2 y := by
  have hA := h.A0
  unfold acR
  have hvan : ∀ x ∉ Icc (y - A) A, bandV A k1 k2 c1 c2 x * bandV A k1 k2 c1 c2 (x - y) = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have : A < |x - y| := lt_of_lt_of_le (by linarith) (neg_le_abs (x - y))
      rw [bandV_of_gt h c1 c2 this, mul_zero]
    · have : A < |x| := lt_of_lt_of_le hx (le_abs_self x)
      rw [bandV_of_gt h c1 c2 this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hcongr : ∀ x ∈ uIcc (y - A) A, bandV A k1 k2 c1 c2 x * bandV A k1 k2 c1 c2 (x - y)
      = c1 ^ 2 * (Real.cos (k1 * x) * Real.cos (k1 * (x - y)))
        + c1 * c2 * (Real.cos (k1 * x) * Real.cos (k2 * (x - y)))
        + c1 * c2 * (Real.cos (k2 * x) * Real.cos (k1 * (x - y)))
        + c2 ^ 2 * (Real.cos (k2 * x) * Real.cos (k2 * (x - y))) := by
    intro x hx
    rw [uIcc_of_le (by linarith), mem_Icc] at hx
    rw [bandV_of_mem c1 c2 (abs_le.mpr ⟨by linarith, hx.2⟩),
      bandV_of_mem c1 c2 (abs_le.mpr ⟨by linarith, by linarith⟩)]
    unfold wPair
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => Real.cos (a * x) * Real.cos (b * (x - y))) volume (y - A) A :=
    fun a b => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add ((((hi _ _).const_mul _).add ((hi _ _).const_mul _)).add ((hi _ _).const_mul _))
      ((hi _ _).const_mul _),
    intervalIntegral.integral_add (((hi _ _).const_mul _).add ((hi _ _).const_mul _)) ((hi _ _).const_mul _),
    intervalIntegral.integral_add ((hi _ _).const_mul _) ((hi _ _).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  have hk1 : k1 ≠ 0 := h.k10.ne'
  have hk2 : k2 ≠ 0 := h.k20.ne'
  have hd : k1 - k2 ≠ 0 := by linarith [h.k12]
  have hd' : k2 - k1 ≠ 0 := by linarith [h.k12]
  have hs : k1 + k2 ≠ 0 := by linarith [h.k10, h.k20]
  have hs' : k2 + k1 ≠ 0 := by linarith [h.k10, h.k20]
  rw [diag_block h.cos1 hk1, diag_block h.cos2 hk2, cross_block h.cos1 h.cos2 h.sin1 h.sin2 hd hs,
    cross_block h.cos2 h.cos1 h.sin2 h.sin1 hd' hs']
  unfold gD gX
  have h3 : k2 ^ 2 - k1 ^ 2 = -(k1 ^ 2 - k2 ^ 2) := by ring
  have h4 : k1 ^ 2 - k2 ^ 2 ≠ 0 := by
    rw [show k1 ^ 2 - k2 ^ 2 = (k1 - k2) * (k1 + k2) by ring]; exact mul_ne_zero hd hs
  rw [h3]
  field_simp
  ring

/-- `acR` at `0`: the squared norm `A (c1^2 + c2^2)` (orthogonality of Dirichlet cosines). -/
theorem acR_bandV_zero : acR (bandV A k1 k2 c1 c2) 0 = A * (c1 ^ 2 + c2 ^ 2) := by
  rw [acR_bandV h c1 c2 le_rfl (by linarith [h.A0])]
  unfold gD gX
  simp
  ring

end


/-! ## Part E: the Lorentzian terms in closed form -/

lemma integral_exp_cos {k β T : ℝ} (hD : 0 < β ^ 2 + k ^ 2) (hc : Real.cos (k * T) = -1)
    (hs : Real.sin (k * T) = 0) :
    ∫ y in (0 : ℝ)..T, Real.exp (-β * y) * Real.cos (k * y) = β * (1 + Real.exp (-β * T)) / (β ^ 2 + k ^ 2) := by
  have key : ∀ y : ℝ, HasDerivAt (fun y => Real.exp (-β * y) * (k * Real.sin (k * y) - β * Real.cos (k * y)) / (β ^ 2 + k ^ 2))
      (Real.exp (-β * y) * Real.cos (k * y)) y := by
    intro y
    have e1 : HasDerivAt (fun y => Real.exp (-β * y)) (Real.exp (-β * y) * (-β * 1)) y :=
      ((hasDerivAt_id y).const_mul (-β)).exp
    have s1 : HasDerivAt (fun y => Real.sin (k * y)) (Real.cos (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).sin
    have c1 : HasDerivAt (fun y => Real.cos (k * y)) (-Real.sin (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).cos
    have := ((e1.mul ((s1.const_mul k).sub (c1.const_mul β))).div_const (β ^ 2 + k ^ 2))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => key y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, hc, hs]
  field_simp
  ring

lemma integral_exp_sin {k β T : ℝ} (hD : 0 < β ^ 2 + k ^ 2) (hc : Real.cos (k * T) = -1)
    (hs : Real.sin (k * T) = 0) :
    ∫ y in (0 : ℝ)..T, Real.exp (-β * y) * Real.sin (k * y) = k * (1 + Real.exp (-β * T)) / (β ^ 2 + k ^ 2) := by
  have key : ∀ y : ℝ, HasDerivAt (fun y => -(Real.exp (-β * y) * (β * Real.sin (k * y) + k * Real.cos (k * y))) / (β ^ 2 + k ^ 2))
      (Real.exp (-β * y) * Real.sin (k * y)) y := by
    intro y
    have e1 : HasDerivAt (fun y => Real.exp (-β * y)) (Real.exp (-β * y) * (-β * 1)) y :=
      ((hasDerivAt_id y).const_mul (-β)).exp
    have s1 : HasDerivAt (fun y => Real.sin (k * y)) (Real.cos (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).sin
    have c1 : HasDerivAt (fun y => Real.cos (k * y)) (-Real.sin (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).cos
    have := ((e1.mul ((s1.const_mul β).add (c1.const_mul k))).neg.div_const (β ^ 2 + k ^ 2))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => key y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, hc, hs]
  field_simp
  ring

lemma integral_y_exp_cos {k β T : ℝ} (hD : 0 < β ^ 2 + k ^ 2) (hc : Real.cos (k * T) = -1)
    (hs : Real.sin (k * T) = 0) :
    ∫ y in (0 : ℝ)..T, y * (Real.exp (-β * y) * Real.cos (k * y))
      = T * Real.exp (-β * T) * β / (β ^ 2 + k ^ 2)
        + (β ^ 2 - k ^ 2) * (1 + Real.exp (-β * T)) / (β ^ 2 + k ^ 2) ^ 2 := by
  have key : ∀ y : ℝ, HasDerivAt (fun y => y * (Real.exp (-β * y) * (k * Real.sin (k * y) - β * Real.cos (k * y))) / (β ^ 2 + k ^ 2)
        + Real.exp (-β * y) * (2 * k * β * Real.sin (k * y) + (k ^ 2 - β ^ 2) * Real.cos (k * y)) / (β ^ 2 + k ^ 2) ^ 2)
      (y * (Real.exp (-β * y) * Real.cos (k * y))) y := by
    intro y
    have e1 : HasDerivAt (fun y => Real.exp (-β * y)) (Real.exp (-β * y) * (-β * 1)) y :=
      ((hasDerivAt_id y).const_mul (-β)).exp
    have s1 : HasDerivAt (fun y => Real.sin (k * y)) (Real.cos (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).sin
    have c1 : HasDerivAt (fun y => Real.cos (k * y)) (-Real.sin (k * y) * (k * 1)) y :=
      ((hasDerivAt_id y).const_mul k).cos
    have d1 := (((hasDerivAt_id y).mul (e1.mul ((s1.const_mul k).sub (c1.const_mul β)))).div_const (β ^ 2 + k ^ 2))
    have d2 := ((e1.mul ((s1.const_mul (2 * k * β)).add (c1.const_mul (k ^ 2 - β ^ 2)))).div_const ((β ^ 2 + k ^ 2) ^ 2))
    refine (d1.add d2).congr_deriv ?_
    simp only [id, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => key y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, zero_mul, Real.exp_zero, Real.sin_zero, Real.cos_zero, hc, hs]
  field_simp
  ring


/-! ## Part F: the band test's frequency data and its Lorentzian terms -/

/-- `J_ii(b) = 2A 2b/(4b^2 + k^2) + 2k^2 (1 + e^{-4bA})/(4b^2 + k^2)^2`. -/
def Jd (A k b : ℝ) : ℝ :=
  2 * A * (2 * b) / (4 * b ^ 2 + k ^ 2) + 2 * k ^ 2 * (1 + Real.exp (-(2 * b) * (2 * A))) / (4 * b ^ 2 + k ^ 2) ^ 2

/-- `J_12(b) = 2 s1 s2 k1 k2 (1 + e^{-4bA})/((4b^2 + k1^2)(4b^2 + k2^2))`. -/
def Jx (A k1 k2 s1 s2 b : ℝ) : ℝ :=
  2 * s1 * s2 * k1 * k2 * (1 + Real.exp (-(2 * b) * (2 * A))) / ((4 * b ^ 2 + k1 ^ 2) * (4 * b ^ 2 + k2 ^ 2))

section
variable {A k1 k2 s1 s2 : ℝ} (h : PairHyp A k1 k2 s1 s2) (c1 c2 : ℝ)
include h

lemma PairHyp.abs_s1 : |s1| ≤ 1 := by rw [← h.sin1]; exact Real.abs_sin_le_one _
lemma PairHyp.abs_s2 : |s2| ≤ 1 := by rw [← h.sin2]; exact Real.abs_sin_le_one _

/-- The band test satisfies the frequency-side hypotheses (continuity, evenness, support in
`[-A, A]`, `C/(1+r^2)` transform decay). -/
theorem bandV_freqData : FreqData (bandV A k1 k2 c1 c2) A
    (|c1| * (2 * A * (1 + 4 * k1 ^ 2) + 16 * k1 / 3) + |c2| * (2 * A * (1 + 4 * k2 ^ 2) + 16 * k2 / 3)) where
  cont := continuous_bandV c1 c2
  even := bandV_even h c1 c2
  supp := tsupport_bandV h c1 c2
  K0 := by
    have := h.A0; have := h.k10; have := h.k20
    positivity
  decay := fun r => norm_paperFT_bandV_le h c1 c2 r h.abs_s1 h.abs_s2

omit h in
lemma cos_two_kA {k : ℝ} (hc : Real.cos (k * A) = 0) : Real.cos (k * (2 * A)) = -1 := by
  rw [show k * (2 * A) = 2 * (k * A) by ring, Real.cos_two_mul, hc]; ring

omit h in
lemma sin_two_kA {k : ℝ} (hc : Real.cos (k * A) = 0) : Real.sin (k * (2 * A)) = 0 := by
  rw [show k * (2 * A) = 2 * (k * A) by ring, Real.sin_two_mul, hc]; ring

/-- The `j`-th Lorentzian term of the band test in closed form. -/
theorem lorTerm_bandV (j : ℕ) :
    lorTerm (bandV A k1 k2 c1 c2) j
      = c1 ^ 2 * Jd A k1 ((j : ℝ) + 1 / 4) + 2 * c1 * c2 * Jx A k1 k2 s1 s2 ((j : ℝ) + 1 / 4)
        + c2 ^ 2 * Jd A k2 ((j : ℝ) + 1 / 4) := by
  have hv := bandV_freqData h c1 c2
  have hA := h.A0
  set b : ℝ := (j : ℝ) + 1 / 4 with hb
  have hb0 : 0 < b := by positivity
  unfold lorTerm
  rw [← hb]
  -- step 1: evenness
  have e1 : (fun y => acR (bandV A k1 k2 c1 c2) y * Real.exp (-2 * b * |y|))
      = fun y => (fun t => acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t)) |y| := by
    funext y
    simp only
    rcases abs_choice y with hy | hy
    · rw [hy]; ring_nf
    · rw [hy, hv.acR_neg]; ring_nf
  rw [e1, integral_comp_abs (f := fun t => acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t))]
  -- step 2: restrict to (0, 2A]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (2 * A) ⊆ Ioi 0) (fun t ht => by
      simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and_or, not_le] at ht
      rcases ht.2 with h1 | h1
      · exact absurd ht.1 (not_lt.mpr (le_of_lt (lt_of_le_of_lt (le_refl t) (by linarith))))
      · rw [hv.acR_eq_zero (by rw [abs_of_pos ht.1]; exact h1.le), zero_mul])]
  rw [← intervalIntegral.integral_of_le (by linarith)]
  -- step 3: the closed form on [0, 2A], as a linear combination of six basic integrands
  set E1 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.cos (k1 * t) with hE1
  set Y1 : ℝ → ℝ := fun t => t * (Real.exp (-(2 * b) * t) * Real.cos (k1 * t)) with hY1
  set S1 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.sin (k1 * t) with hS1
  set E2 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.cos (k2 * t) with hE2
  set Y2 : ℝ → ℝ := fun t => t * (Real.exp (-(2 * b) * t) * Real.cos (k2 * t)) with hY2
  set S2 : ℝ → ℝ := fun t => Real.exp (-(2 * b) * t) * Real.sin (k2 * t) with hS2
  have hk1 : k1 ≠ 0 := h.k10.ne'
  have hk2 : k2 ≠ 0 := h.k20.ne'
  have h4 : k1 ^ 2 - k2 ^ 2 ≠ 0 := by
    rw [show k1 ^ 2 - k2 ^ 2 = (k1 - k2) * (k1 + k2) by ring]
    exact mul_ne_zero (by linarith [h.k12]) (by linarith [h.k10, h.k20])
  set a1 : ℝ := c1 ^ 2 * A with ha1
  set a2 : ℝ := -(c1 ^ 2 / 2) with ha2
  set a3 : ℝ := c1 ^ 2 / (2 * k1) - 2 * c1 * c2 * (s1 * s2 / (k1 ^ 2 - k2 ^ 2)) * k2 with ha3
  set a4 : ℝ := c2 ^ 2 * A with ha4
  set a5 : ℝ := -(c2 ^ 2 / 2) with ha5
  set a6 : ℝ := c2 ^ 2 / (2 * k2) + 2 * c1 * c2 * (s1 * s2 / (k1 ^ 2 - k2 ^ 2)) * k1 with ha6
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) (2 * A),
      acR (bandV A k1 k2 c1 c2) t * Real.exp (-(2 * b) * t)
        = a1 * E1 t + a2 * Y1 t + a3 * S1 t + a4 * E2 t + a5 * Y2 t + a6 * S2 t := by
    intro t ht
    rw [uIcc_of_le (by linarith), mem_Icc] at ht
    rw [acR_bandV h c1 c2 ht.1 ht.2]
    simp only [hE1, hY1, hS1, hE2, hY2, hS2, ha1, ha2, ha3, ha4, ha5, ha6]
    unfold gD gX
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have iE : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 (2 * A) :=
    fun f hf => hf.intervalIntegrable _ _
  have cE1 : Continuous E1 := by rw [hE1]; fun_prop
  have cY1 : Continuous Y1 := by rw [hY1]; fun_prop
  have cS1 : Continuous S1 := by rw [hS1]; fun_prop
  have cE2 : Continuous E2 := by rw [hE2]; fun_prop
  have cY2 : Continuous Y2 := by rw [hY2]; fun_prop
  have cS2 : Continuous S2 := by rw [hS2]; fun_prop
  have hlin : ∫ t in (0 : ℝ)..(2 * A), (a1 * E1 t + a2 * Y1 t + a3 * S1 t + a4 * E2 t + a5 * Y2 t + a6 * S2 t)
      = a1 * (∫ t in (0 : ℝ)..(2 * A), E1 t) + a2 * (∫ t in (0 : ℝ)..(2 * A), Y1 t)
        + a3 * (∫ t in (0 : ℝ)..(2 * A), S1 t) + a4 * (∫ t in (0 : ℝ)..(2 * A), E2 t)
        + a5 * (∫ t in (0 : ℝ)..(2 * A), Y2 t) + a6 * (∫ t in (0 : ℝ)..(2 * A), S2 t) := by
    rw [intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_add (iE _ (by fun_prop)) (iE _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hlin]
  have hD1 : 0 < (2 * b) ^ 2 + k1 ^ 2 := by positivity
  have hD2 : 0 < (2 * b) ^ 2 + k2 ^ 2 := by positivity
  have ic1 : ∫ t in (0 : ℝ)..(2 * A), E1 t = _ := integral_exp_cos hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have ic2 : ∫ t in (0 : ℝ)..(2 * A), E2 t = _ := integral_exp_cos hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  have is1 : ∫ t in (0 : ℝ)..(2 * A), S1 t = _ := integral_exp_sin hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have is2 : ∫ t in (0 : ℝ)..(2 * A), S2 t = _ := integral_exp_sin hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  have iy1 : ∫ t in (0 : ℝ)..(2 * A), Y1 t = _ := integral_y_exp_cos hD1 (cos_two_kA h.cos1) (sin_two_kA h.cos1)
  have iy2 : ∫ t in (0 : ℝ)..(2 * A), Y2 t = _ := integral_y_exp_cos hD2 (cos_two_kA h.cos2) (sin_two_kA h.cos2)
  rw [ic1, ic2, is1, is2, iy1, iy2]
  simp only [ha1, ha2, ha3, ha4, ha5, ha6]
  unfold Jd Jx
  have e4 : ∀ k : ℝ, 4 * b ^ 2 + k ^ 2 = (2 * b) ^ 2 + k ^ 2 := fun k => by ring
  rw [e4 k1, e4 k2]
  generalize Real.exp (-(2 * b) * (2 * A)) = E
  field_simp
  ring
end


open Finset

end Crux3
