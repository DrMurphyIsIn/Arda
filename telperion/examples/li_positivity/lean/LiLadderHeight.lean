/-
LiLadderHeight -- the Li ladder priced in HEIGHT.

Campaign brief: telperion/docs/LI_FACE_BRIEF_2026-09-21.md, sections 1-3 (workstream li-rung0).

Hand-written (NOT emitted by telperion, so exempt from the regeneration diff).  Everything here
is stated against the UPSTREAM vocabulary of the pinned package `LiCriterion` (rev 35df682f):
`NontrivialZero`, `pairedZero`, `liSummand`, `liPairedSummand`, `taylorCoeff`, `riemannXi`.

What this module proves, all with no `sorry` and no hypothesis unless named in the statement:

  1. `taylorCoeff_eq_half_tsum_paired` -- the hypothesis-free paired zero sum
        taylorCoeff riemannXi n = (1/2) * sum' rho, m(rho) * liPairedSummand n rho,
     obtained by composing the upstream order bridges (`xi_hasFiniteOrder`, `xi_order_le_one`)
     with the multiplicity-aware genus-one summability, the Hadamard product, and the
     weighted paired-sum formula.  Purely a composition of upstream theorems.
  2. `liPairedSummand_eq_two_sub_pow_sub_inv` / `liPairedSummand_eq_w` -- the normal forms
        liPairedSummand n rho = 2 - u^N - u^(-N),  u = 1 - 1/rho,  N = n + 1
     (equivalently with w = rho/(rho - 1) = u^(-1)), and `re_liPairedSummand_eq`, its real part
        2 - 2 cosh(N log|u|) cos(N arg u).
  3. Lemma A `cosh_mul_cos_le_one`: cosh a * cos b <= 1 whenever |a| <= |b| <= pi/2.  Proved by
     two antitonicity passes (f = cosh*cos has f' = sinh*cos - cosh*sin, itself antitone with
     derivative -2 sinh*sin <= 0 on [0, pi]).  Lemma A' `cosh_mul_cos_le_one_of_le_three_pi_div_two`
     extends the window to |b| <= 3 pi / 2: on [pi/2, 3 pi/2] cos b <= 0, so the product is <= 0
     with no condition on a at all (the survey's factor 3).
  4. Lemma B, the geometry of a zero with |Im rho| >= 1 (stated for any z in the open strip):
     `abs_log_norm_le_abs_arg` (|log|u|| <= |arg u|) and `abs_arg_base_le` (|arg u| <= 1/|Im z|).
     The angle identity arg u = arctan(beta/gamma) + arctan((1-beta)/gamma) is
     `arg_one_sub_inv_eq`; the lower bound on |arg u| goes through sin(arg u) = Im u / |u|.
  5. Theorem C `re_liPairedSummand_nonneg_of_height`: every zero with
     |Im rho| >= max(1, 2(n+1)/(3 pi)) contributes a nonnegative term to rung n, ON OR OFF the
     line (|N log|u|| <= |N arg u| <= N/|Im rho| <= 3 pi/2, then Lemma A').
  6. Theorem D `li_rung_of_zeros_on_line_below`: if every nontrivial zero with |Im rho| <= T
     (T >= 1) has real part 1/2, then 0 <= Re(taylorCoeff riemannXi n) for all
     n + 1 <= 3 pi T / 2.  The exchange rate of the Li face: height T buys the first
     floor(3 pi T / 2) rungs.  (T >= 1 is what Lemma B needs; a smaller floor would be vacuous.)
  7. Rung 0 with NO hypothesis: `li_rung0_kernel` (registry node RH_li_rung0_kernel), from
     liPairedSummand 0 rho = 1 / (rho (1 - rho)), whose real part is
     (beta (1 - beta) + gamma^2) / |rho (1 - rho)|^2 >= 0 for every zero.
  8. The height-4000 composition, stated against the CONCLUSION shape of
     `AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands`
     (`forall rho, riemannZeta rho = 0 -> 0 < rho.im -> rho.im <= 4000 -> rho.re = 1/2`).  That
     conclusion says nothing about negative Im (handled by `riemannZeta_conj`) nor about a real
     zero in (0,1) (which would make every even rung's pair term negative, so it cannot be waved
     away).  `li_rungs_of_bands_4000_of_noRealZero` carries the latter as the explicit named
     hypothesis `NoRealZeroInStrip`; `noRealZeroInStrip` DISCHARGES it from the li-box module's
     hypothesis-free `LowHeightBox.riemannZeta_ne_zero_of_unit_interval` (a corollary of Box 1,
     every zero in the strip has |Im| >= sqrt 3 / 2), so `li_rungs_of_bands_4000` needs only
     the capstone conclusion.
     Rungs 0..18848 follow (`li_rungs_of_bands_4000_upto`; 6000 pi > 18849).

Design note (tsum): the pair term is NOT real termwise (its imaginary part is
-(r^N - r^(-N)) sin(N theta)); we take the real part per term and pass Re through the tsum with
`Complex.re_tsum`, whose summability input is the upstream
`summable_weighted_Li_paired_summand_of_weighted_genus` (`re_taylorCoeff_eq_half_tsum_re`).
The ladder consumes zero localisation; it produces none.

conjecture1_proved = False.  Nothing here proves, or approaches, the Riemann Hypothesis: every
theorem is a hypothesis-free identity, a finite real inequality, or an implication from a named
zero-localisation hypothesis, and the uniform `forall n` IS RH (upstream `li_criterion_rh_iff`).
-/
import Mathlib
import Lc.LiCriterion.XiOrderBridge
import LowHeightBox

open scoped Real

namespace LiLadderHeight

open LiCriterion

/-! ### 1. The hypothesis-free paired zero sum -/

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

/-! ### 2. Normal forms of the paired summand -/

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

/-! ### 3. Lemma A: `cosh a * cos b <= 1` for `|a| <= |b| <= pi/2` -/

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

/-! ### 4. Lemma B: the geometry of a zero with `|Im| >= 1`

Throughout, `z = beta + i gamma` is any point of the open strip `0 < beta < 1`, `u = 1 - 1/z`,
`A = |z|^2 = beta^2 + gamma^2`, `B = |z - 1|^2 = (beta - 1)^2 + gamma^2`. -/

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

/-! ### 5. Theorem C: termwise nonnegativity at height -/

/-- **Theorem C.**  A nontrivial zero with `|Im rho| >= max 1 (2(n+1)/(3 pi))` contributes a
nonnegative term to rung `n`, whether or not it lies on the critical line:
`|N log|u|| <= |N arg u| <= N/|Im rho| <= 3 pi/2`, then Lemma A'. -/
theorem re_liPairedSummand_nonneg_of_height (n : ℕ) (ρ : NontrivialZero)
    (h : max 1 (2 * ((n : ℝ) + 1) / (3 * π)) ≤ |ρ.val.im|) :
    0 ≤ (liPairedSummand n ρ).re := by
  rw [re_liPairedSummand_eq]
  have h1 : 1 ≤ |ρ.val.im| := (le_max_left _ _).trans h
  have h2 : 2 * ((n : ℝ) + 1) / (3 * π) ≤ |ρ.val.im| := (le_max_right _ _).trans h
  have h3π : (0 : ℝ) < 3 * π := by positivity
  have hγ0 : 0 < |ρ.val.im| := by linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hab := abs_log_norm_le_abs_arg ρ.val ρ.property.2.1 ρ.property.2.2 h1
  have hθ := abs_arg_base_le ρ.val ρ.property.2.1 ρ.property.2.2 h1
  have hNθ : |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| ≤ 3 * π / 2 := by
    rw [abs_mul, abs_of_pos hNpos]
    calc ((n + 1 : ℕ) : ℝ) * |Complex.arg ((1 : ℂ) - 1 / ρ.val)|
        ≤ ((n + 1 : ℕ) : ℝ) * (1 / |ρ.val.im|) := mul_le_mul_of_nonneg_left hθ hNpos.le
      _ ≤ 3 * π / 2 := by
        rw [mul_one_div, div_le_iff₀ hγ0]
        rw [div_le_iff₀ h3π] at h2
        rw [hNn]
        linarith
  have hNa : |((n + 1 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - 1 / ρ.val‖|
      ≤ |((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val)| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have := cosh_mul_cos_le_one_of_le_three_pi_div_two hNa hNθ
  linarith

/-- On-line zeros contribute nonnegatively: `|u| = 1`, so the term is `2 (1 - cos(N arg u))`. -/
theorem re_liPairedSummand_nonneg_of_onLine (n : ℕ) (ρ : NontrivialZero)
    (hρ : ρ.val.re = 1 / 2) : 0 ≤ (liPairedSummand n ρ).re := by
  rw [re_liPairedSummand_eq,
    modulus_one_minus_one_div_on_critical_line ρ.val (NontrivialZero.ne_zero ρ) hρ,
    Real.log_one, mul_zero, Real.cosh_zero, mul_one]
  linarith [Real.cos_le_one (((n + 1 : ℕ) : ℝ) * Complex.arg ((1 : ℂ) - 1 / ρ.val))]

/-! ### 6. The tsum plumbing and Theorem D -/

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

/-- **Theorem D: the Li ladder priced in height.**  Let `T >= 1`.  If every nontrivial zero with
`|Im rho| <= T` has real part `1/2`, then `0 <= Re (taylorCoeff riemannXi n)` for every rung
`n` with `n + 1 <= 3 pi T / 2`.  Zeros below `T` are on the line (the term is `2(1 - cos)`);
zeros above `T` have `|Im| >= T >= max 1 (2(n+1)/(3 pi))` (Theorem C).  The line hypothesis
quantifies over ALL zeros with `|Im| <= T`, real ones included.  Conditional; proves nothing
about RH. -/
theorem li_rung_of_zeros_on_line_below (T : ℝ) (hT : 1 ≤ T)
    (hline : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ.re = 1 / 2)
    (n : ℕ) (hn : (n + 1 : ℝ) ≤ 3 * π * T / 2) :
    0 ≤ (taylorCoeff riemannXi n).re := by
  apply re_taylorCoeff_nonneg_of_termwise
  intro ρ
  rcases le_or_gt |ρ.val.im| T with hle | hlt
  · exact re_liPairedSummand_nonneg_of_onLine n ρ
      (hline ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2 hle)
  · apply re_liPairedSummand_nonneg_of_height
    apply max_le
    · linarith
    · have : 2 * ((n : ℝ) + 1) / (3 * π) ≤ T := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith

/-! ### 7. Rung 0 with no hypothesis -/

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

/-- Rung 0 is termwise nonnegative for EVERY nontrivial zero:
`Re (1 / (rho (1 - rho))) = (beta (1 - beta) + gamma^2) / |rho (1 - rho)|^2 >= 0`. -/
theorem re_liPairedSummand_zero_nonneg (ρ : NontrivialZero) :
    0 ≤ (liPairedSummand 0 ρ).re := by
  rw [liPairedSummand_zero_eq, one_div, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    zero_sub, mul_neg, sub_neg_eq_add]
  have h0 := ρ.property.2.1
  have h1 := ρ.property.2.2
  nlinarith [sq_nonneg ρ.val.im, mul_pos h0 (sub_pos.mpr h1)]

/-! ### 8. Composition with the height-4000 capstone

`AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands` concludes, from its 89 band /
segment hypotheses and `hγ`,

    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2.

That conclusion covers only `0 < Im rho`.  Negative `Im` follows by conjugation; `Im rho = 0`
(a real zero in `(0,1)`) is the residual `NoRealZeroInStrip`, carried explicitly in the
`_of_noRealZero` form and DISCHARGED by the li-box module's Box 1 in the main form. -/

/-- **Named residual**: zeta has no real zero in `(0,1)`.  Stated as a `Prop` so the composition
can be read with or without its discharge. -/
def NoRealZeroInStrip : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → riemannZeta x ≠ 0

/-- **The residual is discharged** by the li-box module (hypothesis-free):
`LowHeightBox.riemannZeta_ne_zero_of_unit_interval`, itself a corollary of Box 1
(`LowHeightBox.zeta_zero_im_ge`: a real zero would have `|Im| = 0 < sqrt 3 / 2`). -/
theorem noRealZeroInStrip : NoRealZeroInStrip :=
  fun x hx0 hx1 => LowHeightBox.riemannZeta_ne_zero_of_unit_interval x hx0 hx1

/-- From an upper-half-plane line certificate (the capstone's conclusion shape) and the
no-real-zero residual, the two-sided line hypothesis of Theorem D. -/
theorem line_hyp_of_upper_half (T : ℝ)
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ T → ρ.re = 1 / 2)
    (hreal : NoRealZeroInStrip) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T → ρ.re = 1 / 2 := by
  intro ρ hz h0 h1 hT
  rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
  · have hzc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hz, map_zero]
    have him : 0 < ((starRingEnd ℂ) ρ).im := by
      rw [Complex.conj_im]; linarith
    have hleT : ((starRingEnd ℂ) ρ).im ≤ T := by
      rw [Complex.conj_im]; rw [abs_of_neg hneg] at hT; exact hT
    have := hall _ hzc him hleT
    rwa [Complex.conj_re] at this
  · have hρ : ρ = (ρ.re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact hzero)
    exact absurd hz (by rw [hρ]; exact hreal ρ.re h0 h1)
  · rw [abs_of_pos hpos] at hT
    exact hall ρ hz hpos hT

/-- **The height-4000 Li ladder, residual explicit.**  Under the CONCLUSION of the height-4000
capstone (`hall`, verbatim in its shape) and the named no-real-zero residual, every rung
`n + 1 <= 6000 pi` is nonnegative.  Conditional; proves nothing about RH. -/
theorem li_rungs_of_bands_4000_of_noRealZero
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2)
    (hreal : NoRealZeroInStrip) :
    ∀ n : ℕ, (n + 1 : ℝ) ≤ 3 * π * 4000 / 2 → 0 ≤ (taylorCoeff riemannXi n).re :=
  fun n hn => li_rung_of_zeros_on_line_below 4000 (by norm_num)
    (line_hyp_of_upper_half 4000 hall hreal) n hn

/-- **The height-4000 Li ladder.**  Under the capstone's conclusion alone (the real-zero
residual discharged by Box 1), every rung `n + 1 <= 6000 pi` is nonnegative.  Conditional on
`hall`; proves nothing about RH. -/
theorem li_rungs_of_bands_4000
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, (n + 1 : ℝ) ≤ 3 * π * 4000 / 2 → 0 ≤ (taylorCoeff riemannXi n).re :=
  li_rungs_of_bands_4000_of_noRealZero hall noRealZeroInStrip

/-- Concretely: rungs `0 .. 18848` (`6000 pi > 18849`). -/
theorem li_rungs_of_bands_4000_upto
    (hall : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2) :
    ∀ n : ℕ, n ≤ 18848 → 0 ≤ (taylorCoeff riemannXi n).re := by
  intro n hn
  apply li_rungs_of_bands_4000 hall n
  have hπ := Real.pi_gt_d4
  have hn' : (n : ℝ) ≤ 18848 := by exact_mod_cast hn
  linarith

end LiLadderHeight

/-- **Registry node `RH_li_rung0_kernel`** (roadmap B2), hypothesis-free: Li's `lambda_1 >= 0`
with the Arb enclosure hypothesis of the emitted rung DISCHARGED.  Statement verbatim from
`missions/rh/lean/Statements/RH_li_rung0_kernel.lean`.  conjecture1_proved = False. -/
theorem li_rung0_kernel :
    0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi 0).re :=
  LiLadderHeight.re_taylorCoeff_nonneg_of_termwise 0 LiLadderHeight.re_liPairedSummand_zero_nonneg
