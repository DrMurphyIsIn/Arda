/- LOW-HEIGHT ZERO BOX (li_positivity island, brief LI_FACE_BRIEF_2026-09-21 section 4).

   Two hypothesis-free localisation facts for the nontrivial zeros of `riemannZeta`, in Mathlib
   vocabulary only:

     Box 1  `zeta_zero_im_ge`      : a zero `s` with `0 < Re s < 1` has  `sqrt 3 / 2 ≤ |Im s|`;
     Box 2  `zeta_zero_confined`   : such a zero satisfies  `(Re s - 1/2)^2 ≤ (Im s)^2 / 3 - 1/4`.

   ROUTE (a) of the brief: the island already carries the UNCONDITIONAL fractional-part
   representation (StripReprAssembled, `ZeroFreeBridge.zeta_fract_repr`)

       zeta(s) = s/(s-1) - s * J(s),   J(s) = ∫_{x>1} {x} x^{-(s+1)} dx     (Re s > 0, s ≠ 1),

   but only the crude bound |J(s)| ≤ 1/Re s (`zeta_repr_integral_bound`), which localises nothing
   (it gives |Im s|^2 ≥ |2 Re s - 1|, empty at Re s = 1/2).  The new input here is the SHARP bound

       |J(s)| ≤ ∫_{x>1} {x} x^{-(σ+1)} dx ≤ 1/(2σ)          (σ = Re s > 0),

   proved by cutting [1, ∞) into the unit cells [n+1, n+2) and, on each cell with midpoint
   c = n + 3/2, using the pointwise sign inequality (x - c)(x^{-σ-1} - c^{-σ-1}) ≤ 0 (the kernel is
   decreasing) together with ∫_cell (x - c) dx = 0.  No integration by parts and no continuity of
   {x} is needed.  A zero then forces 2σ ≤ |s - 1|; the functional equation (Λ(1-s) = Λ(s), with
   Gammaℝ s ≠ 0 for Re s > 0) makes 1 - s a zero too, forcing 2(1-σ) ≤ |s|; adding the squares
   gives Box 2, and Box 2 gives Box 1.

   Nothing here proves, or bears on, whether RH holds: the box is an unconditional finite
   localisation (no zeros below height sqrt 3 / 2 ~ 0.866; the first zero is at ~ 14.13).
   conjecture1_proved = False.
-/
import Mathlib
import StripReprAssembled

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace LowHeightBox

/-! ## The sharp fractional-part integral bound, real exponent. -/

/-- The unit cell `[n+1, n+2)`. -/
def cell (n : ℕ) : Set ℝ := Ico ((n : ℝ) + 1) ((n : ℝ) + 2)

/-- The unit cells `[n+1, n+2)`, `n : ℕ`, cover `[1, ∞)`. -/
theorem Ici_one_eq_iUnion_cell : Ici (1 : ℝ) = ⋃ n : ℕ, cell n := by
  ext x
  simp only [cell, mem_Ici, mem_iUnion, mem_Ico]
  constructor
  · intro hx
    refine ⟨⌊x - 1⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (show (0 : ℝ) ≤ x - 1 by linarith)
      linarith
    · have := Nat.lt_floor_add_one (x - 1)
      linarith
  · rintro ⟨n, hn, -⟩
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The unit cells are pairwise disjoint. -/
theorem pairwise_disjoint_cells : Pairwise (Function.onFun Disjoint cell) := by
  intro m n hmn
  simp only [Function.onFun, cell]
  rw [Set.disjoint_left]
  intro x hxm hxn
  simp only [mem_Ico] at hxm hxn
  apply hmn
  have h1 : (m : ℝ) < n + 1 := by linarith
  have h2 : (n : ℝ) < m + 1 := by linarith
  have h1' : m < n + 1 := by exact_mod_cast h1
  have h2' : n < m + 1 := by exact_mod_cast h2
  omega

/-- On the cell `[n+1, n+2)` the fractional part is `x - (n+1)`. -/
theorem fract_eq_on_cell {n : ℕ} {x : ℝ} (hx : x ∈ Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) :
    Int.fract x = x - ((n : ℝ) + 1) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith [hx.1], by linarith [hx.2], ⟨(n : ℤ) + 1, ?_⟩⟩
  push_cast; ring

/-- The pointwise sign inequality on a cell: for the decreasing kernel `g x = x^(-(σ+1))` and the
    cell midpoint `c`, `(x - c) * g x ≤ (x - c) * g c` for every `x > 0`. -/
theorem sub_mul_rpow_le {σ c x : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hx : 0 < x) :
    (x - c) * x ^ (-(σ + 1)) ≤ (x - c) * c ^ (-(σ + 1)) := by
  have hexp : -(σ + 1) ≤ 0 := by linarith
  rcases le_or_gt x c with h | h
  · -- x ≤ c : x - c ≤ 0 and g x ≥ g c
    have hg : c ^ (-(σ + 1)) ≤ x ^ (-(σ + 1)) := Real.rpow_le_rpow_of_nonpos hx h hexp
    nlinarith
  · -- c < x : x - c ≥ 0 and g x ≤ g c
    have hg : x ^ (-(σ + 1)) ≤ c ^ (-(σ + 1)) := Real.rpow_le_rpow_of_nonpos hc h.le hexp
    nlinarith

/-- The centred moment of a cell vanishes: `∫_{[n+1,n+2)} (x - (n + 3/2)) dx = 0`. -/
theorem integral_cell_centred (n : ℕ) :
    ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x - ((n : ℝ) + 3 / 2)) = 0 := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Continuity of the kernel `x ^ (-(σ+1))` on a cell (all points positive). -/
theorem continuousOn_kernel_cell (σ : ℝ) (n : ℕ) :
    ContinuousOn (fun x : ℝ => x ^ (-(σ + 1))) (Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
  refine continuousOn_id.rpow_const ?_
  intro x hx
  left
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (1 : ℝ) ≤ x := by linarith [hx.1]
  simp only [id]
  exact ne_of_gt (by linarith)

/-- Per-cell inequality: the fractional-part integral over a cell is at most half the kernel
    integral over the cell. -/
theorem cell_fract_integral_le {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∫ x in cell n, Int.fract x * x ^ (-(σ + 1))
      ≤ ∫ x in cell n, (1 / 2 : ℝ) * x ^ (-(σ + 1)) := by
  simp only [cell]
  set c : ℝ := (n : ℝ) + 3 / 2 with hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcpos : 0 < c := by rw [hc]; linarith
  have hIco : Ico ((n : ℝ) + 1) ((n : ℝ) + 2) ⊆ Icc ((n : ℝ) + 1) ((n : ℝ) + 2) := Ico_subset_Icc_self
  -- integrability of the pieces on the cell (all continuous on the compact closure)
  have hgc : ContinuousOn (fun x : ℝ => x ^ (-(σ + 1))) (Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) :=
    continuousOn_kernel_cell σ n
  have hint1 : IntegrableOn (fun x : ℝ => (x - c) * x ^ (-(σ + 1)))
      (Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) :=
    ((continuousOn_id.sub continuousOn_const).mul hgc).integrableOn_Icc.mono_set hIco
  have hint2 : IntegrableOn (fun x : ℝ => (x - c) * c ^ (-(σ + 1)))
      (Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) :=
    ((continuousOn_id.sub continuousOn_const).mul continuousOn_const).integrableOn_Icc.mono_set hIco
  have hint3 : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-(σ + 1)))
      (Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) :=
    (continuousOn_const.mul hgc).integrableOn_Icc.mono_set hIco
  -- rewrite the fractional part on the cell
  have hcongr : ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), Int.fract x * x ^ (-(σ + 1))
      = ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2),
          ((x - c) * x ^ (-(σ + 1)) + (1 / 2 : ℝ) * x ^ (-(σ + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ico (fun x hx => ?_)
    rw [fract_eq_on_cell hx, hc]
    ring
  rw [hcongr, integral_add hint1 hint3]
  -- the centred piece is ≤ 0
  have hcent : ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x - c) * x ^ (-(σ + 1)) ≤ 0 := by
    calc ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x - c) * x ^ (-(σ + 1))
        ≤ ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x - c) * c ^ (-(σ + 1)) := by
          refine setIntegral_mono_on hint1 hint2 measurableSet_Ico (fun x hx => ?_)
          have hxpos : 0 < x := by linarith [hx.1]
          exact sub_mul_rpow_le hσ hcpos hxpos
      _ = c ^ (-(σ + 1)) * ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x - c) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ico (fun x _ => ?_)
          ring
      _ = 0 := by rw [hc, integral_cell_centred, mul_zero]
  linarith

/-- Integrability of the fractional-part kernel on `[1, ∞)`. -/
theorem integrableOn_fract_kernel {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => Int.fract x * x ^ (-(σ + 1))) (Ici (1 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hdom : IntegrableOn (fun x : ℝ => x ^ (-(σ + 1))) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Int.fract x * x ^ (-(σ + 1)))
      (volume.restrict (Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    exact Measurable.mul measurable_fract (measurable_id.pow_const _)
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Int.fract_nonneg x) (Real.rpow_nonneg hx0.le _))]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le

/-- Integrability of the half kernel on `[1, ∞)`. -/
theorem integrableOn_half_kernel {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-(σ + 1))) (Ici (1 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _

/-- **The sharp bound**: `∫_{x>1} {x} x^{-(σ+1)} dx ≤ 1/(2σ)` for `σ > 0`. -/
theorem fract_integral_le_half_inv {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(σ + 1)) ≤ 1 / (2 * σ) := by
  have hhalf : ∫ x in Ioi (1 : ℝ), (1 / 2 : ℝ) * x ^ (-(σ + 1)) = 1 / (2 * σ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -(σ + 1) + 1 = -σ by ring, neg_div_neg_eq, one_div_mul_one_div]
  rw [← hhalf, ← integral_Ici_eq_integral_Ioi, ← integral_Ici_eq_integral_Ioi]
  have hU := Ici_one_eq_iUnion_cell
  have hm : ∀ n : ℕ, MeasurableSet (cell n) := fun _ => measurableSet_Ico
  have h1 := hasSum_integral_iUnion (μ := volume) (f := fun x : ℝ => Int.fract x * x ^ (-(σ + 1)))
    hm pairwise_disjoint_cells (hU ▸ integrableOn_fract_kernel hσ)
  have h2 := hasSum_integral_iUnion (μ := volume) (f := fun x : ℝ => (1 / 2 : ℝ) * x ^ (-(σ + 1)))
    hm pairwise_disjoint_cells (hU ▸ integrableOn_half_kernel hσ)
  rw [← hU] at h1 h2
  exact hasSum_le (fun n => cell_fract_integral_le hσ n) h1 h2

/-! ## The complex tail integral. -/

/-- The sharp bound on the complex fractional-part integral: `‖J(s)‖ ≤ 1/(2 Re s)`. -/
theorem norm_fractIntegral_le_half {s : ℂ} (hs : 0 < s.re) :
    ‖ZeroFreeBridge.fractIntegral s‖ ≤ 1 / (2 * s.re) := by
  have hnorm : ∀ x ∈ Ioi (1 : ℝ),
      ‖ZeroFreeBridge.fractIntegrand s x‖ = Int.fract x * x ^ (-(s.re + 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    simp only [ZeroFreeBridge.fractIntegrand]
    rw [norm_div, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.add_re, Complex.one_re, Real.norm_of_nonneg (Int.fract_nonneg x),
      Real.rpow_neg hx0.le, div_eq_mul_inv]
  calc ‖ZeroFreeBridge.fractIntegral s‖
      ≤ ∫ x in Ioi (1 : ℝ), ‖ZeroFreeBridge.fractIntegrand s x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) :=
        setIntegral_congr_fun measurableSet_Ioi hnorm
    _ ≤ 1 / (2 * s.re) := fract_integral_le_half_inv hs

/-! ## Zeros in the strip. -/

/-- A zero of zeta in the open strip is at distance at least `2 Re s` from the pole. -/
theorem two_re_le_norm_sub_one {s : ℂ} (h0 : riemannZeta s = 0) (hre0 : 0 < s.re)
    (hre1 : s.re < 1) : 2 * s.re ≤ ‖s - 1‖ := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hre1; simp at hre1
  have hsD : s ∈ ZeroFreeBridge.stripDomain := ⟨hre0, by simpa using hs1⟩
  have hrepr := ZeroFreeBridge.zeta_fract_repr hsD
  rw [h0] at hrepr
  simp only [ZeroFreeBridge.stripRHS] at hrepr
  have heq : s / (s - 1) = s * ZeroFreeBridge.fractIntegral s := by
    have := hrepr.symm; rwa [sub_eq_zero] at this
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre0; simp at hre0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hs1n : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hJ := norm_fractIntegral_le_half hre0
  have hnormeq : ‖s‖ / ‖s - 1‖ = ‖s‖ * ‖ZeroFreeBridge.fractIntegral s‖ := by
    rw [← norm_div, ← norm_mul, heq]
  have hle : 1 / ‖s - 1‖ ≤ 1 / (2 * s.re) := by
    have h1 : ‖s‖ * (1 / ‖s - 1‖) ≤ ‖s‖ * (1 / (2 * s.re)) := by
      rw [mul_one_div, hnormeq]
      exact mul_le_mul_of_nonneg_left hJ hsn.le
    exact le_of_mul_le_mul_left h1 hsn
  exact (one_div_le_one_div hs1n (by linarith)).mp hle

/-- The functional-equation reflection: a zero `s` in the open strip gives a zero `1 - s`. -/
theorem zeta_one_sub_zero {s : ℂ} (h0 : riemannZeta s = 0) (hre0 : 0 < s.re)
    (hre1 : s.re < 1) : riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre0; simp at hre0
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have : s.re = -(2 * n) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at h0
    exact h0.resolve_right hG
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    have : (1 - s).re = 0 := by rw [h]; simp
    simp at this
    linarith
  rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hΛ, zero_div]

/-- **Box 2** (hypothesis-free): every zero of `riemannZeta` in the open strip satisfies
    `(Re s - 1/2)^2 ≤ (Im s)^2 / 3 - 1/4`. -/
theorem zeta_zero_confined (s : ℂ) (h0 : riemannZeta s = 0) (hre : 0 < s.re ∧ s.re < 1) :
    (s.re - 1 / 2) ^ 2 ≤ s.im ^ 2 / 3 - 1 / 4 := by
  obtain ⟨hre0, hre1⟩ := hre
  -- the zero itself: 2σ ≤ ‖s - 1‖
  have hA := two_re_le_norm_sub_one h0 hre0 hre1
  -- its reflection 1 - s: 2(1-σ) ≤ ‖(1 - s) - 1‖ = ‖s‖
  have h0' := zeta_one_sub_zero h0 hre0 hre1
  have hB := two_re_le_norm_sub_one h0' (by simp; linarith) (by simp; linarith)
  rw [show (1 : ℂ) - s - 1 = -s by ring, norm_neg] at hB
  simp only [Complex.sub_re, Complex.one_re] at hB
  -- square both, expand the norms
  have hA2 : (2 * s.re) ^ 2 ≤ ‖s - 1‖ ^ 2 := by
    have : 0 ≤ 2 * s.re := by linarith
    nlinarith
  have hB2 : (2 * (1 - s.re)) ^ 2 ≤ ‖s‖ ^ 2 := by
    have : 0 ≤ 2 * (1 - s.re) := by linarith
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply] at hA2 hB2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at hA2
  nlinarith

/-- **Box 1** (hypothesis-free): no zero of `riemannZeta` in the open strip has
    `|Im s| < sqrt 3 / 2`. -/
theorem zeta_zero_im_ge (s : ℂ) (h0 : riemannZeta s = 0) (hre : 0 < s.re ∧ s.re < 1) :
    Real.sqrt 3 / 2 ≤ |s.im| := by
  have hbox := zeta_zero_confined s h0 hre
  have hsq : (3 : ℝ) / 4 ≤ s.im ^ 2 := by nlinarith [sq_nonneg (s.re - 1 / 2)]
  have h1 : Real.sqrt (3 / 4) ≤ Real.sqrt (s.im ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h1
  have h2 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
    rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h2] at h1
  exact h1

/-- **Real-axis corollary**: `riemannZeta x ≠ 0` for real `0 < x < 1` (a real zero would have
    `Im = 0 < sqrt 3 / 2`, contradicting Box 1). -/
theorem riemannZeta_ne_zero_of_unit_interval (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro h0
  have h := zeta_zero_im_ge (x : ℂ) h0 (by simpa using ⟨hx0, hx1⟩)
  simp only [Complex.ofReal_im, abs_zero] at h
  have : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  linarith

end LowHeightBox
