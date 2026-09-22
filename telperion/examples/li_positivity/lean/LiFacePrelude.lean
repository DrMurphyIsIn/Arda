/-
LiFacePrelude -- the shared helper pack of the Li face (li_positivity island).

Shapes audit proposal P3 (telperion/docs/SHAPES_AUDIT_48H_2026-09-22.md section 4.2, rows 13-17
of the duplication table; telperion/docs/SHAPES_AUDIT_D_LI_FACE_2026-09-22.md section 5): the same
Mathlib-only facts were proved twice, once per island (li: LiLadderHeight / LiLadderSharp /
LowHeightBox; rvm: E6Bridge28 / E6Bridge29), and several upstream-vocabulary helpers were proved
twice inside this island (LiLadderHeight against LiBoxRungs).  This module holds ONE copy of each
helper; the four consumers import it and keep only their theorems.  Every registry node theorem
stays, with identical statement text, in the module it is linked to (LiLadderHeight,
LiLadderSharp, LowHeightBox, LiBoxRungs); only helper lemmas moved here.  Hand-written (NOT
emitted by telperion, so exempt from the regeneration diff).  Proofs are the ones that already
built on this island, moved verbatim; no `sorry` anywhere.

Part I -- Mathlib only (the portable P3 pack: every statement mentions Mathlib names only, so the
rvm island can consume the same text once the toolchain pins agree):

  1. Lemma A `cosh_mul_cos_le_one`: cosh a * cos b <= 1 whenever |a| <= |b| <= pi/2, by two
     antitonicity passes (f = cosh*cos has f' = sinh*cos - cosh*sin, itself antitone with
     derivative -2 sinh*sin <= 0 on [0, pi]).  Lemma A' `cosh_mul_cos_le_one_of_le_three_pi_div_two`
     (|b| <= 3 pi/2: cos b <= 0 past pi/2, no condition on a) and Lemma A''
     `cosh_mul_cos_le_one_window` (3 pi/2 < |b| <= 2 pi and |a| <= 2 pi - |b|, by reflecting b
     to d = 2 pi - |b| in [0, pi/2)).
  2. The g-inequality `one_div_add_one_div_two_sq_le`: 1/g + 1/(2 g^2) <= 1/(g - 1/2) for g > 1/2.
  3. The geometry of a strip point z = beta + i gamma (0 < beta < 1) through u = 1 - 1/z: the
     algebra of u (`one_sub_inv_ne_zero`, `one_sub_inv_re`, `one_sub_inv_im`,
     `normSq_one_sub_inv`, `normSq_eq_re_sq_add_im_sq`, `normSq_sub_one_eq`, `ne_zero_of_re_pos`),
     the log bound `abs_log_norm_one_sub_inv_le` (|log|u|| <= 1/(2 gamma^2) for gamma <> 0), the
     arctan bound `abs_arctan_le_abs`, and for |gamma| >= 1 the angle identity
     `arg_one_sub_inv_eq` (arg u = arctan(beta/gamma) + arctan((1 - beta)/gamma)), the arg bounds
     `abs_arg_base_le` (|arg u| <= 1/|gamma|) and `one_div_two_abs_im_le_abs_arg`
     (1/(2 |gamma|) <= |arg u|), Lemma B `abs_log_norm_le_abs_arg` (|log|u|| <= |arg u|) and
     Lemma B'' `abs_arg_add_abs_log_le` (|arg u| + |log|u|| <= 1/(|gamma| - 1/2)).
  4. The polar real part `re_pow_add_inv_pow`: Re (u^N + (u^N)⁻¹) = 2 cosh(N log|u|) cos(N arg u)
     for u <> 0.
  5. The sharp fractional-part kernel bound `fract_integral_le_half_inv`:
     ∫_{x>1} {x} x^{-(σ+1)} dx <= 1/(2σ) for σ > 0, with its unit-cell lemmas (cells [n+1, n+2)
     cover [1, ∞), the pointwise sign inequality (x - c)(x^{-σ-1} - c^{-σ-1}) <= 0 against the cell
     midpoint c, the vanishing centred moment, the per-cell inequality, integrability, and the
     `hasSum_integral_iUnion` summation).  This is the midpoint-reflection proof; the rvm island's
     integration-by-parts proof of the same fact is the one the audit retires.
  6. The involution averaging helper `hasSum_involution_average`: from HasSum f S and
     0 <= f x + f (σ x) for every x (σ any equivalence), 0 <= S.  The tsum regrouping of
     E6Bridge28 abstracted; on this island the pairing is built into the upstream
     `liPairedSummand`, so no module here consumes it yet.

Part II -- upstream `LiCriterion` vocabulary (rev 35df682f; li island only, NOT portable to rvm):

  7. The hypothesis-free paired zero sum `taylorCoeff_eq_half_tsum_paired` (composition of the
     upstream order bridges with the weighted genus-one summability, the Hadamard product with
     multiplicity, and the weighted paired-sum formula), its summability
     `summable_weighted_paired`, the real-part form `re_taylorCoeff_eq_half_tsum_re`, and
     `re_taylorCoeff_nonneg_of_termwise` (a termwise sign suffices for the rung).
  8. The pair-term normal forms: `liPairedSummand_eq_two_sub_pow_sub_inv`
     (2 - u^N - (u^N)⁻¹, u = 1 - 1/rho, N = n + 1), `liPairedSummand_eq_w` and
     `liPairedSummand_eq_w_zpow` (w = rho/(rho - 1) = u⁻¹), `liPairedSummand_eq_pow`
     (2 - w^N - v^N with v = (rho - 1)/rho, the LiBoxRungs form), the polar real part
     `re_liPairedSummand_eq` (2 - 2 cosh(N log|u|) cos(N arg u)), and `liPairedSummand_zero_eq`
     (rung 0: 1 / (rho (1 - rho))).

conjecture1_proved = False.  Nothing here proves, or approaches, the Riemann Hypothesis: every
statement is a finite real inequality, a Mathlib-only identity, or a hypothesis-free composition of
upstream theorems; the uniform `forall n` IS RH (upstream `li_criterion_rh_iff`) and is not touched.
-/
import Mathlib
import Lc.LiCriterion.XiOrderBridge

open scoped Real

namespace LiFacePrelude

/-! ## Part I: Mathlib only -/

/-! ### 1. Lemma A: `cosh a * cos b <= 1` for `|a| <= |b| <= pi/2`, and its window variants -/

/-- `g(t) = sinh t cos t - cosh t sin t <= 0` on `[0, pi]` (it vanishes at `0` and
`g' = -2 sinh t sin t <= 0`). -/
lemma sinh_mul_cos_sub_cosh_mul_sin_nonpos {t : ℝ} (h0 : 0 ≤ t) (hπ : t ≤ π) :
    Real.sinh t * Real.cos t - Real.cosh t * Real.sin t ≤ 0 := by
  let g : ℝ → ℝ := fun t => Real.sinh t * Real.cos t - Real.cosh t * Real.sin t
  have hg : ∀ x, HasDerivAt g
      (Real.cosh x * Real.cos x + Real.sinh x * (-Real.sin x)
        - (Real.sinh x * Real.sin x + Real.cosh x * Real.cos x)) x := fun x =>
    ((Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_cos x)).sub
      ((Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_sin x))
  have hanti : AntitoneOn g (Set.Icc 0 π) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 π)
      ((Real.continuous_sinh.mul Real.continuous_cos).sub
        (Real.continuous_cosh.mul Real.continuous_sin)).continuousOn ?_ ?_
    · intro x _
      exact (hg x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hg x).deriv]
      have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx.1.le
      have hsin : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le
      nlinarith [mul_nonneg hs hsin]
  have := hanti ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0, hπ⟩ h0
  simpa [g] using this

/-- `cosh t * cos t <= 1` on `[0, pi]` (equality at `0`, antitone since the derivative is the
nonpositive `g` above). -/
lemma cosh_mul_cos_le_one_of_nonneg_of_le_pi {t : ℝ} (h0 : 0 ≤ t) (hπ : t ≤ π) :
    Real.cosh t * Real.cos t ≤ 1 := by
  let f : ℝ → ℝ := fun t => Real.cosh t * Real.cos t
  have hf : ∀ x, HasDerivAt f (Real.sinh x * Real.cos x + Real.cosh x * (-Real.sin x)) x :=
    fun x => (Real.hasDerivAt_cosh x).mul (Real.hasDerivAt_cos x)
  have hanti : AntitoneOn f (Set.Icc 0 π) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 π)
      (Real.continuous_cosh.mul Real.continuous_cos).continuousOn ?_ ?_
    · intro x _
      exact (hf x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hf x).deriv]
      have := sinh_mul_cos_sub_cosh_mul_sin_nonpos hx.1.le hx.2.le
      linarith
  have := hanti ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0, hπ⟩ h0
  simpa [f] using this

/-- **Lemma A.**  `cosh a * cos b <= 1` whenever `|a| <= |b| <= pi/2`. -/
theorem cosh_mul_cos_le_one {a b : ℝ} (hab : |a| ≤ |b|) (hb : |b| ≤ π / 2) :
    Real.cosh a * Real.cos b ≤ 1 := by
  have hπ : π / 2 ≤ π := by linarith [Real.pi_pos]
  have hcos : Real.cos b ≤ Real.cos a := by
    rw [← Real.cos_abs b, ← Real.cos_abs a]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg a) (hb.trans hπ) hab
  calc Real.cosh a * Real.cos b ≤ Real.cosh a * Real.cos a :=
        mul_le_mul_of_nonneg_left hcos (Real.cosh_pos a).le
    _ = Real.cosh |a| * Real.cos |a| := by rw [Real.cosh_abs, Real.cos_abs]
    _ ≤ 1 := cosh_mul_cos_le_one_of_nonneg_of_le_pi (abs_nonneg a) ((hab.trans hb).trans hπ)

/-- **Lemma A'** (the factor 3).  `cosh a * cos b <= 1` whenever `|a| <= |b| <= 3 pi / 2`: for
`|b| <= pi/2` this is Lemma A; for `pi/2 <= |b| <= 3 pi/2`, `cos b <= 0` and the product is
nonpositive with no condition on `a`. -/
theorem cosh_mul_cos_le_one_of_le_three_pi_div_two {a b : ℝ} (hab : |a| ≤ |b|)
    (hb : |b| ≤ 3 * π / 2) : Real.cosh a * Real.cos b ≤ 1 := by
  rcases le_or_gt |b| (π / 2) with hsmall | hbig
  · exact cosh_mul_cos_le_one hab hsmall
  · have hcos : Real.cos b ≤ 0 := by
      rw [← Real.cos_abs b]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hbig.le (by linarith)
    nlinarith [Real.cosh_pos a]

/-- **Lemma A''.**  If `3 pi/2 < |b| <= 2 pi` and `|a| <= 2 pi - |b|` then `cosh a * cos b <= 1`. -/
theorem cosh_mul_cos_le_one_window {a b : ℝ} (hb1 : 3 * π / 2 < |b|) (hb2 : |b| ≤ 2 * π)
    (ha : |a| ≤ 2 * π - |b|) : Real.cosh a * Real.cos b ≤ 1 := by
  have hd0 : 0 ≤ 2 * π - |b| := by linarith
  have hd : abs (2 * π - |b|) ≤ π / 2 := by
    rw [abs_of_nonneg hd0]; linarith
  have hcos : Real.cos b = Real.cos (2 * π - |b|) := by
    rw [Real.cos_two_pi_sub, Real.cos_abs]
  rw [hcos]
  exact cosh_mul_cos_le_one (ha.trans (le_abs_self _)) hd

/-! ### 2. The g-inequality -/

/-- `1/g + 1/(2 g^2) <= 1/(g - 1/2)` for `g > 1/2` (i.e. `(2g+1)(2g-1) <= 4g^2`). -/
lemma one_div_add_one_div_two_sq_le {g : ℝ} (hg : 1 / 2 < g) :
    1 / g + 1 / (2 * g ^ 2) ≤ 1 / (g - 1 / 2) := by
  have hg0 : 0 < g := by linarith
  have h1 : 1 / g + 1 / (2 * g ^ 2) = (2 * g + 1) / (2 * g ^ 2) := by
    field_simp
  rw [h1, div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-! ### 3. The geometry of a strip point

Throughout, `z = beta + i gamma` is any point of the open strip `0 < beta < 1`, `u = 1 - 1/z`,
`A = |z|^2 = beta^2 + gamma^2`, `B = |z - 1|^2 = (beta - 1)^2 + gamma^2`. -/

/-- The base `u = 1 - 1/z = (z - 1)/z` is nonzero for `z` in the open strip. -/
lemma one_sub_inv_ne_zero (z : ℂ) (h1 : z.re < 1) : (1 : ℂ) - 1 / z ≠ 0 := by
  intro h
  have h' : (1 : ℂ) / z = 1 := by linear_combination -h
  rw [one_div, inv_eq_one] at h'
  rw [h'] at h1
  simp at h1

lemma one_sub_inv_re (z : ℂ) : ((1 : ℂ) - 1 / z).re = 1 - z.re / Complex.normSq z := by
  simp [Complex.sub_re, one_div, Complex.inv_re]

lemma one_sub_inv_im (z : ℂ) : ((1 : ℂ) - 1 / z).im = z.im / Complex.normSq z := by
  simp [Complex.sub_im, one_div, Complex.inv_im, neg_div]

lemma normSq_one_sub_inv (z : ℂ) (hz : z ≠ 0) :
    Complex.normSq ((1 : ℂ) - 1 / z) = Complex.normSq (z - 1) / Complex.normSq z := by
  rw [one_sub_div hz, Complex.normSq_div]

lemma normSq_eq_re_sq_add_im_sq (z : ℂ) : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply]; ring

lemma normSq_sub_one_eq (z : ℂ) : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  ring

lemma ne_zero_of_re_pos {z : ℂ} (h0 : 0 < z.re) : z ≠ 0 := by
  intro h; rw [h] at h0; simp at h0

/-- `log|u| = (log B - log A) / 2`. -/
lemma log_norm_one_sub_inv (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) :
    Real.log ‖(1 : ℂ) - 1 / z‖
      = (Real.log (Complex.normSq (z - 1)) - Real.log (Complex.normSq z)) / 2 := by
  have hz0 : z ≠ 0 := ne_zero_of_re_pos h0
  have hz1 : z - 1 ≠ 0 := by
    intro h; have : z = 1 := sub_eq_zero.mp h; rw [this] at h1; simp at h1
  have h2 : Real.log ‖(1 : ℂ) - 1 / z‖ = Real.log (Complex.normSq ((1 : ℂ) - 1 / z)) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]; push_cast; ring
  rw [h2, normSq_one_sub_inv z hz0,
    Real.log_div (Complex.normSq_pos.mpr hz1).ne' (Complex.normSq_pos.mpr hz0).ne']

/-- `|log|u|| <= 1 / (2 gamma^2)`: from `log(B/A) <= B/A - 1`, `log(A/B) <= A/B - 1`,
`|B - A| = |1 - 2 beta| <= 1` and `A, B >= gamma^2`. -/
lemma abs_log_norm_one_sub_inv_le (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : z.im ≠ 0) :
    |Real.log ‖(1 : ℂ) - 1 / z‖| ≤ 1 / (2 * z.im ^ 2) := by
  rw [log_norm_one_sub_inv z h0 h1, normSq_sub_one_eq, normSq_eq_re_sq_add_im_sq]
  have hγ2 : 0 < z.im ^ 2 := by positivity
  have hApos : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  have hBpos : 0 < (z.re - 1) ^ 2 + z.im ^ 2 := by positivity
  have hAγ : z.im ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith
  have hBγ : z.im ^ 2 ≤ (z.re - 1) ^ 2 + z.im ^ 2 := by nlinarith
  have hup : Real.log ((z.re - 1) ^ 2 + z.im ^ 2) - Real.log (z.re ^ 2 + z.im ^ 2)
      ≤ 1 / z.im ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hBpos hApos)
    rw [Real.log_div hBpos.ne' hApos.ne'] at h
    have h' : ((z.re - 1) ^ 2 + z.im ^ 2) / (z.re ^ 2 + z.im ^ 2) - 1 ≤ 1 / z.im ^ 2 := by
      rw [div_sub_one hApos.ne', div_le_div_iff₀ hApos hγ2]
      nlinarith [mul_pos h0 hγ2]
    linarith
  have hlow : Real.log (z.re ^ 2 + z.im ^ 2) - Real.log ((z.re - 1) ^ 2 + z.im ^ 2)
      ≤ 1 / z.im ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hApos hBpos)
    rw [Real.log_div hApos.ne' hBpos.ne'] at h
    have h' : (z.re ^ 2 + z.im ^ 2) / ((z.re - 1) ^ 2 + z.im ^ 2) - 1 ≤ 1 / z.im ^ 2 := by
      rw [div_sub_one hBpos.ne', div_le_div_iff₀ hBpos hγ2]
      nlinarith [mul_pos (sub_pos.mpr h1) hγ2]
    linarith
  have heq : (1 : ℝ) / (2 * z.im ^ 2) = (1 / z.im ^ 2) / 2 := by
    field_simp
  rw [heq, abs_le]
  constructor <;> linarith

/-- `|arctan x| <= |x|`. -/
lemma abs_arctan_le_abs (x : ℝ) : |Real.arctan x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hx), abs_of_nonneg hx]
    have h := Real.le_tan (Real.arctan_nonneg.mpr hx) (Real.arctan_lt_pi_div_two x)
    rwa [Real.tan_arctan] at h
  · have hx' : 0 ≤ -x := by linarith
    have h := Real.le_tan (Real.arctan_nonneg.mpr hx') (Real.arctan_lt_pi_div_two (-x))
    rw [Real.tan_arctan, Real.arctan_neg] at h
    have hneg : Real.arctan x < 0 := by
      have := Real.arctan_strictMono hx
      simpa [Real.arctan_zero] using this
    rw [abs_of_neg hneg, abs_of_neg hx]
    linarith

/-- **The angle identity.**  For `|Im z| >= 1`, `Re u > 0` and
`arg u = arctan(beta/gamma) + arctan((1 - beta)/gamma)`. -/
lemma arg_one_sub_inv_eq (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : 1 ≤ |z.im|) :
    Complex.arg ((1 : ℂ) - 1 / z)
      = Real.arctan (z.re / z.im) + Real.arctan ((1 - z.re) / z.im) := by
  have hγ2 : 1 ≤ z.im ^ 2 := (one_le_sq_iff_one_le_abs z.im).mpr hγ
  have hγ0 : z.im ≠ 0 := by
    intro h; rw [h] at hγ; norm_num at hγ
  have hγ2' : 0 < z.im ^ 2 := by positivity
  have hD : 0 < z.im ^ 2 - z.re * (1 - z.re) := by nlinarith
  have hApos : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  have hre : 0 < ((1 : ℂ) - 1 / z).re := by
    rw [one_sub_inv_re, normSq_eq_re_sq_add_im_sq, sub_pos, div_lt_one hApos]
    nlinarith
  have hθ : |Complex.arg ((1 : ℂ) - 1 / z)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hD' : z.im ^ 2 - z.re * (1 - z.re) ≠ 0 := hD.ne'
  have htan : Real.tan (Complex.arg ((1 : ℂ) - 1 / z))
      = z.im / (z.im ^ 2 - z.re * (1 - z.re)) := by
    rw [Complex.tan_arg, one_sub_inv_re, one_sub_inv_im, normSq_eq_re_sq_add_im_sq]
    have hden : (1 : ℝ) - z.re / (z.re ^ 2 + z.im ^ 2)
        = (z.im ^ 2 - z.re * (1 - z.re)) / (z.re ^ 2 + z.im ^ 2) := by
      field_simp
      ring
    rw [hden, div_div_div_cancel_right₀ hApos.ne']
  have hxy : z.re / z.im * ((1 - z.re) / z.im) < 1 := by
    rw [div_mul_div_comm, div_lt_one (mul_self_pos.mpr hγ0)]
    nlinarith
  rw [Real.arctan_add hxy]
  have hfrac : (z.re / z.im + (1 - z.re) / z.im) / (1 - z.re / z.im * ((1 - z.re) / z.im))
      = z.im / (z.im ^ 2 - z.re * (1 - z.re)) := by
    field_simp
    ring
  rw [hfrac, ← htan, Real.arctan_tan (abs_lt.mp hθ).1 (abs_lt.mp hθ).2]

/-- **Lemma B, upper half**: `|arg u| <= 1 / |Im z|` for `|Im z| >= 1`
(from `arctan x <= x`). -/
theorem abs_arg_base_le (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : 1 ≤ |z.im|) :
    |Complex.arg ((1 : ℂ) - 1 / z)| ≤ 1 / |z.im| := by
  rw [arg_one_sub_inv_eq z h0 h1 hγ]
  calc |Real.arctan (z.re / z.im) + Real.arctan ((1 - z.re) / z.im)|
      ≤ |Real.arctan (z.re / z.im)| + |Real.arctan ((1 - z.re) / z.im)| := abs_add_le _ _
    _ ≤ |z.re / z.im| + |(1 - z.re) / z.im| :=
        add_le_add (abs_arctan_le_abs _) (abs_arctan_le_abs _)
    _ = z.re / |z.im| + (1 - z.re) / |z.im| := by
        rw [abs_div, abs_div, abs_of_pos h0, abs_of_pos (sub_pos.mpr h1)]
    _ = 1 / |z.im| := by ring

/-- `|arg u| >= 1 / (2 |Im z|)` for `|Im z| >= 1`: `|sin (arg u)| = |Im u| / |u| = |gamma| / sqrt(AB)`
and `AB <= 4 gamma^4`. -/
lemma one_div_two_abs_im_le_abs_arg (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (hγ : 1 ≤ |z.im|) :
    1 / (2 * |z.im|) ≤ |Complex.arg ((1 : ℂ) - 1 / z)| := by
  have hz0 : z ≠ 0 := ne_zero_of_re_pos h0
  have hu : (1 : ℂ) - 1 / z ≠ 0 := one_sub_inv_ne_zero z h1
  have hγ0 : 0 < |z.im| := by linarith
  have hγ2 : 1 ≤ z.im ^ 2 := (one_le_sq_iff_one_le_abs z.im).mpr hγ
  have hApos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hs : 0 < ‖(1 : ℂ) - 1 / z‖ := norm_pos_iff.mpr hu
  have hs2 : ‖(1 : ℂ) - 1 / z‖ ^ 2 = Complex.normSq (z - 1) / Complex.normSq z := by
    rw [← Complex.normSq_eq_norm_sq, normSq_one_sub_inv z hz0]
  -- A * B <= (2 gamma^2)^2
  have hA2 : Complex.normSq z ≤ 2 * z.im ^ 2 := by
    rw [normSq_eq_re_sq_add_im_sq]; nlinarith
  have hB2 : Complex.normSq (z - 1) ≤ 2 * z.im ^ 2 := by
    rw [normSq_sub_one_eq]; nlinarith
  have hAB : Complex.normSq z * Complex.normSq (z - 1) ≤ (2 * z.im ^ 2) ^ 2 := by
    calc Complex.normSq z * Complex.normSq (z - 1) ≤ (2 * z.im ^ 2) * (2 * z.im ^ 2) :=
          mul_le_mul hA2 hB2 (Complex.normSq_nonneg _) (by positivity)
      _ = (2 * z.im ^ 2) ^ 2 := by ring
  -- hence A * |u| <= 2 gamma^2
  have hAs : Complex.normSq z * ‖(1 : ℂ) - 1 / z‖ ≤ 2 * z.im ^ 2 := by
    have hsq : (Complex.normSq z * ‖(1 : ℂ) - 1 / z‖) ^ 2
        = Complex.normSq z * Complex.normSq (z - 1) := by
      rw [mul_pow, hs2]; field_simp
    exact le_of_sq_le_sq (hsq ▸ hAB) (by positivity)
  have hsin : Real.sin (Complex.arg ((1 : ℂ) - 1 / z))
      = z.im / Complex.normSq z / ‖(1 : ℂ) - 1 / z‖ := by
    rw [Complex.sin_arg, one_sub_inv_im]
  have hsq_abs : |z.im| * (2 * |z.im|) = 2 * z.im ^ 2 := by
    have := sq_abs z.im; nlinarith
  calc 1 / (2 * |z.im|) ≤ |z.im| / (Complex.normSq z * ‖(1 : ℂ) - 1 / z‖) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
    _ = |Real.sin (Complex.arg ((1 : ℂ) - 1 / z))| := by
        rw [hsin, abs_div, abs_div, abs_of_pos hApos, abs_of_pos hs, div_div]
    _ ≤ |Complex.arg ((1 : ℂ) - 1 / z)| := Real.abs_sin_le_abs

/-- **Lemma B, lower half**: `|log|u|| <= |arg u|` for `|Im z| >= 1`
(`|log|u|| <= 1/(2 gamma^2) <= 1/(2|gamma|) <= |arg u|`). -/
theorem abs_log_norm_le_abs_arg (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : 1 ≤ |z.im|) :
    |Real.log ‖(1 : ℂ) - 1 / z‖| ≤ |Complex.arg ((1 : ℂ) - 1 / z)| := by
  have hγ0 : z.im ≠ 0 := by
    intro h; rw [h] at hγ; norm_num at hγ
  have hlog := abs_log_norm_one_sub_inv_le z h0 h1 hγ0
  have hlow := one_div_two_abs_im_le_abs_arg z h0 h1 hγ
  have hmid : 1 / (2 * z.im ^ 2) ≤ 1 / (2 * |z.im|) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_abs z.im, abs_nonneg z.im]
  linarith

/-- **Lemma B''.**  For `0 < Re z < 1` and `|Im z| >= 1`, with `u = 1 - 1/z`,
`|arg u| + |log|u|| <= 1/(|Im z| - 1/2)`. -/
theorem abs_arg_add_abs_log_le (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) (hγ : 1 ≤ |z.im|) :
    |Complex.arg ((1 : ℂ) - 1 / z)| + |Real.log ‖(1 : ℂ) - 1 / z‖| ≤ 1 / (|z.im| - 1 / 2) := by
  have hγ0 : z.im ≠ 0 := by
    intro h; rw [h] at hγ; norm_num at hγ
  have harg := abs_arg_base_le z h0 h1 hγ
  have hlog := abs_log_norm_one_sub_inv_le z h0 h1 hγ0
  have hsq : z.im ^ 2 = |z.im| ^ 2 := (sq_abs z.im).symm
  rw [hsq] at hlog
  have halg := one_div_add_one_div_two_sq_le (g := |z.im|) (by linarith)
  linarith

/-! ### 4. The polar real part -/

/-- **Polar real part.**  For `u ≠ 0`, `Re (u^N + (u^N)⁻¹) = 2 cosh(N log|u|) cos(N arg u)`. -/
theorem re_pow_add_inv_pow (u : ℂ) (hu : u ≠ 0) (N : ℕ) :
    (u ^ N + (u ^ N)⁻¹).re
      = 2 * Real.cosh (N * Real.log ‖u‖) * Real.cos (N * Complex.arg u) := by
  have hexp : u ^ N = Complex.exp (N * Complex.log u) := by
    rw [Complex.exp_nat_mul, Complex.exp_log hu]
  have hinv : (u ^ N)⁻¹ = Complex.exp (-(N * Complex.log u)) := by
    rw [Complex.exp_neg, hexp]
  have hre : ((N : ℂ) * Complex.log u).re = N * Real.log ‖u‖ := by
    simp [Complex.log_re]
  have him : ((N : ℂ) * Complex.log u).im = N * Complex.arg u := by
    simp [Complex.log_im]
  rw [Complex.add_re, hinv, hexp, Complex.exp_re, Complex.exp_re, Complex.neg_re, Complex.neg_im,
    hre, him, Real.cos_neg, Real.cosh_eq]
  ring

/-! ### 5. The sharp fractional-part kernel bound, real exponent -/

section Sawtooth

open MeasureTheory Set Filter Topology

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

end Sawtooth

/-! ### 6. The involution averaging helper -/

/-- **Averaging over an involution.**  If `f` sums to `S` and every pair `f x + f (σ x)` is
nonnegative (`σ` any equivalence of the index type, typically the pairing `rho ↦ 1 - conj rho`),
then `S >= 0`.  Reindexing along `σ` gives a second `HasSum` for `S`; adding the two gives
`HasSum (f + f ∘ σ) (2 S)` with nonnegative terms.  Fixed points of `σ` need no special
treatment.  (Abstracts the tsum regrouping of the rvm island's E6Bridge28; not yet consumed on
this island, where the pairing is built into `liPairedSummand`.) -/
theorem hasSum_involution_average {α : Type*} (σ : α ≃ α) {f : α → ℝ} {S : ℝ}
    (hf : HasSum f S) (hpair : ∀ x, 0 ≤ f x + f (σ x)) : 0 ≤ S := by
  have h2 : HasSum (fun x => f (σ x)) S := (σ.hasSum_iff).mpr hf
  have h3 : HasSum (fun x => f x + f (σ x)) (S + S) := hf.add h2
  have h4 : 0 ≤ S + S := by
    rw [← h3.tsum_eq]
    exact tsum_nonneg hpair
  linarith

/-! ## Part II: upstream `LiCriterion` vocabulary (li island only) -/

open LiCriterion

/-! ### 7. The hypothesis-free paired zero sum and the tsum plumbing -/

/-- **The Li coefficient as a paired zero sum, hypothesis-free.**  Composes the upstream order
bridges with the weighted genus-one summability, the Hadamard product with multiplicity, and the
weighted paired-sum formula.  `m(rho) = analyticOrderNatAt riemannXi rho`. -/
theorem taylorCoeff_eq_half_tsum_paired (n : ℕ) :
    taylorCoeff riemannXi n
      = (2⁻¹ : ℂ) * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ :=
  weighted_paired_sum_formula_of_standard_hypotheses
    (xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one)
    (xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder
      xi_order_le_one) n

/-- The weighted paired family is summable (upstream, from the weighted genus-one bound). -/
theorem summable_weighted_paired (n : ℕ) :
    Summable (fun ρ : NontrivialZero =>
      (analyticOrderNatAt riemannXi ρ.val : ℂ) * liPairedSummand n ρ) :=
  summable_weighted_Li_paired_summand_of_weighted_genus
    (xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one) n

/-- **The real part of the Li coefficient is the sum of the real parts**, hypothesis-free:
`Re (taylorCoeff riemannXi n) = (1/2) * sum' rho, m(rho) * Re (liPairedSummand n rho)`.
(The pair term is not real termwise; `Re` passes through the tsum by summability.) -/
theorem re_taylorCoeff_eq_half_tsum_re (n : ℕ) :
    (taylorCoeff riemannXi n).re
      = 2⁻¹ * ∑' ρ : NontrivialZero,
          (analyticOrderNatAt riemannXi ρ.val : ℝ) * (liPairedSummand n ρ).re := by
  rw [taylorCoeff_eq_half_tsum_paired n]
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, Complex.re_ofReal_mul, Complex.re_tsum (summable_weighted_paired n)]
  congr 1
  apply tsum_congr
  intro ρ
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- **Termwise sign suffices.**  If every paired summand of rung `n` has nonnegative real part,
the rung is nonnegative (`m(rho) >= 0` is a natural number). -/
theorem re_taylorCoeff_nonneg_of_termwise (n : ℕ)
    (h : ∀ ρ : NontrivialZero, 0 ≤ (liPairedSummand n ρ).re) :
    0 ≤ (taylorCoeff riemannXi n).re := by
  rw [re_taylorCoeff_eq_half_tsum_re n]
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun ρ => mul_nonneg (Nat.cast_nonneg _) (h ρ))

/-! ### 8. Normal forms of the paired summand -/

/-- **Normal form of the paired summand.**  With `u := 1 - 1/rho` and `N := n + 1`,
`liPairedSummand n rho = 2 - u^N - (u^N)⁻¹`, because `pairedZero rho = 1 - rho` sends `u` to
`u⁻¹`.  No critical-line hypothesis. -/
theorem liPairedSummand_eq_two_sub_pow_sub_inv (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ
      = 2 - (1 - 1 / ρ.val) ^ (n + 1) - ((1 - 1 / ρ.val) ^ (n + 1))⁻¹ := by
  have hρ0 : ρ.val ≠ 0 := NontrivialZero.ne_zero ρ
  have hρ1 : ρ.val ≠ 1 := NontrivialZero.ne_one ρ
  have hρ1' : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h1ρ : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  set w : ℂ := 1 - 1 / ρ.val with hw
  have hwe : w = (ρ.val - 1) / ρ.val := by rw [hw, sub_div, div_self hρ0]
  have hpair : (1 : ℂ) - 1 / (1 - ρ.val) = w⁻¹ := by rw [hwe, inv_div]; field_simp; ring
  have hzp : ∀ x : ℂ, x ^ (-(n + 1 : ℤ)) = (x ^ (n + 1))⁻¹ := by
    intro x; rw [zpow_neg]; congr 1
  have hpair_pow : (w⁻¹) ^ (-(n + 1 : ℤ)) = w ^ (n + 1) := by rw [hzp w⁻¹, inv_pow, inv_inv]
  simp only [liPairedSummand, liSummand, pairedZero_val]
  rw [← hw, hpair, hzp w, hpair_pow]
  ring

/-- The brief's normal form: with `w := rho/(rho - 1) = (1 - 1/rho)⁻¹`,
`liPairedSummand n rho = 2 - w^(n+1) - (w^(n+1))⁻¹`. -/
theorem liPairedSummand_eq_w (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ
      = 2 - (ρ.val / (ρ.val - 1)) ^ (n + 1) - ((ρ.val / (ρ.val - 1)) ^ (n + 1))⁻¹ := by
  rw [liPairedSummand_eq_two_sub_pow_sub_inv]
  have hw : ρ.val / (ρ.val - 1) = (1 - 1 / ρ.val)⁻¹ := by
    rw [one_sub_div (NontrivialZero.ne_zero ρ), inv_div]
  rw [hw, inv_pow, inv_inv]
  ring

/-- The same, with integer exponents `w^(n+1) + w^(-(n+1))` exactly as in the brief. -/
theorem liPairedSummand_eq_w_zpow (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ
      = 2 - (ρ.val / (ρ.val - 1)) ^ ((n + 1 : ℕ) : ℤ)
          - (ρ.val / (ρ.val - 1)) ^ (-((n + 1 : ℕ) : ℤ)) := by
  rw [liPairedSummand_eq_w, zpow_neg, zpow_natCast]

/-- The LiBoxRungs form: `liPairedSummand n rho = 2 - w^(n+1) - v^(n+1)` with `w = rho/(rho-1)`
and `v = (rho-1)/rho = w⁻¹`. -/
theorem liPairedSummand_eq_pow (n : ℕ) (ρ : NontrivialZero) :
    liPairedSummand n ρ
      = 2 - (ρ.val / (ρ.val - 1)) ^ (n + 1) - ((ρ.val - 1) / ρ.val) ^ (n + 1) := by
  rw [liPairedSummand_eq_w, ← inv_pow, inv_div]

/-- **Real part of the paired summand in polar form**:
`Re (liPairedSummand n rho) = 2 - 2 cosh(N log|u|) cos(N arg u)`, `u = 1 - 1/rho`, `N = n+1`. -/
theorem re_liPairedSummand_eq (n : ℕ) (ρ : NontrivialZero) :
    (liPairedSummand n ρ).re
      = 2 - 2 * Real.cosh (((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖)
            * Real.cos (((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)) := by
  rw [liPairedSummand_eq_two_sub_pow_sub_inv,
    ← re_pow_add_inv_pow _ (one_sub_inv_ne_zero ρ.val ρ.property.2.2) (n + 1)]
  have h2 : ((2 : ℂ)).re = 2 := by norm_num
  rw [Complex.sub_re, Complex.sub_re, Complex.add_re, h2]
  ring

/-- `liPairedSummand 0 rho = 1 / (rho (1 - rho))`. -/
theorem liPairedSummand_zero_eq (ρ : NontrivialZero) :
    liPairedSummand 0 ρ = 1 / (ρ.val * (1 - ρ.val)) := by
  rw [liPairedSummand_eq_two_sub_pow_sub_inv]
  have hρ0 : ρ.val ≠ 0 := NontrivialZero.ne_zero ρ
  have h1ρ : (1 : ℂ) - ρ.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (NontrivialZero.ne_one ρ))
  have hρ1 : ρ.val - 1 ≠ 0 := sub_ne_zero.mpr (NontrivialZero.ne_one ρ)
  rw [zero_add, pow_one, one_sub_div hρ0, inv_div]
  field_simp
  ring

end LiFacePrelude
