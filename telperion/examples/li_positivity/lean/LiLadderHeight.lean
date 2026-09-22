/-
LiLadderHeight -- the Li ladder priced in HEIGHT.

Campaign brief: telperion/docs/LI_FACE_BRIEF_2026-09-21.md, sections 1-3 (workstream li-rung0).

Hand-written (NOT emitted by telperion, so exempt from the regeneration diff).  Everything here
is stated against the UPSTREAM vocabulary of the pinned package `LiCriterion` (rev 35df682f):
`NontrivialZero`, `pairedZero`, `liSummand`, `liPairedSummand`, `taylorCoeff`, `riemannXi`.

The helper lemmas this module used to carry now live in the shared pack `LiFacePrelude` (shapes
audit P3, 2026-09-22), one copy for the whole Li face: the hypothesis-free paired zero sum
`taylorCoeff_eq_half_tsum_paired` (a composition of the upstream order bridges
`xi_hasFiniteOrder`, `xi_order_le_one` with the weighted genus-one summability, the Hadamard
product, and the weighted paired-sum formula), the pair-term normal forms
`liPairedSummand_eq_two_sub_pow_sub_inv` / `liPairedSummand_eq_w` (u = 1 - 1/rho, N = n + 1,
liPairedSummand n rho = 2 - u^N - u^(-N)) and the polar real part `re_liPairedSummand_eq`
(2 - 2 cosh(N log|u|) cos(N arg u)), Lemma A `cosh_mul_cos_le_one` (cosh a * cos b <= 1 for
|a| <= |b| <= pi/2, two antitonicity passes) and Lemma A'
`cosh_mul_cos_le_one_of_le_three_pi_div_two` (the factor 3: cos b <= 0 on [pi/2, 3 pi/2]),
Lemma B `abs_log_norm_le_abs_arg` (|log|u|| <= |arg u|) and `abs_arg_base_le`
(|arg u| <= 1/|Im z|) with the angle identity `arg_one_sub_inv_eq`, the tsum plumbing
`re_taylorCoeff_eq_half_tsum_re` / `re_taylorCoeff_nonneg_of_termwise`, and
`liPairedSummand_zero_eq`.  Their statements are unchanged; the rvm island's duplicates of the
Mathlib-only ones are retired against that one copy.

What this module proves, all with no `sorry` and no hypothesis unless named in the statement:

  1. Theorem C `re_liPairedSummand_nonneg_of_height`: every zero with
     |Im rho| >= max(1, 2(n+1)/(3 pi)) contributes a nonnegative term to rung n, ON OR OFF the
     line (|N log|u|| <= |N arg u| <= N/|Im rho| <= 3 pi/2, then Lemma A').  On-line zeros
     contribute nonnegatively at every rung (`re_liPairedSummand_nonneg_of_onLine`: |u| = 1, the
     term is 2(1 - cos)).
  2. Theorem D `li_rung_of_zeros_on_line_below` (registry node RH_li_ladder_height): if every
     nontrivial zero with |Im rho| <= T (T >= 1) has real part 1/2, then
     0 <= Re(taylorCoeff riemannXi n) for all n + 1 <= 3 pi T / 2.  The exchange rate of the Li
     face: height T buys the first floor(3 pi T / 2) rungs.  (T >= 1 is what Lemma B needs; a
     smaller floor would be vacuous.)
  3. Rung 0 with NO hypothesis: `li_rung0_kernel` (registry node RH_li_rung0_kernel), from
     liPairedSummand 0 rho = 1 / (rho (1 - rho)), whose real part is
     (beta (1 - beta) + gamma^2) / |rho (1 - rho)|^2 >= 0 for every zero.
  4. The height-4000 composition, stated against the CONCLUSION shape of
     `AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands`
     (`forall rho, riemannZeta rho = 0 -> 0 < rho.im -> rho.im <= 4000 -> rho.re = 1/2`).  That
     conclusion says nothing about negative Im (handled by `riemannZeta_conj`) nor about a real
     zero in (0,1) (which would make every even rung's pair term negative, so it cannot be waved
     away).  `li_rungs_of_bands_4000_of_noRealZero` carries the latter as the explicit named
     hypothesis `NoRealZeroInStrip`; `noRealZeroInStrip` DISCHARGES it from the li-box module's
     hypothesis-free `LowHeightBox.riemannZeta_ne_zero_of_unit_interval` (a corollary of Box 1,
     every zero in the strip has |Im| >= sqrt 3 / 2), so `li_rungs_of_bands_4000` needs only
     the capstone conclusion.
     Rungs 0..18848 follow (`li_rungs_of_bands_4000_upto`, registry node
     RH_li_rungs_of_height_4000; 6000 pi > 18849).

Design note (tsum): the pair term is NOT real termwise (its imaginary part is
-(r^N - r^(-N)) sin(N theta)); the prelude takes the real part per term and passes Re through the
tsum with `Complex.re_tsum`, whose summability input is the upstream
`summable_weighted_Li_paired_summand_of_weighted_genus`
(`LiFacePrelude.re_taylorCoeff_eq_half_tsum_re`).  The ladder consumes zero localisation; it
produces none.

conjecture1_proved = False.  Nothing here proves, or approaches, the Riemann Hypothesis: every
theorem is a hypothesis-free identity, a finite real inequality, or an implication from a named
zero-localisation hypothesis, and the uniform `forall n` IS RH (upstream `li_criterion_rh_iff`).
-/
import Mathlib
import Lc.LiCriterion.XiOrderBridge
import LowHeightBox
import LiFacePrelude

open scoped Real

namespace LiLadderHeight

open LiCriterion
open LiFacePrelude

/-! ### 1. Theorem C: termwise nonnegativity at height -/

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

/-! ### 2. Theorem D -/

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

/-! ### 3. Rung 0 with no hypothesis -/

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

/-! ### 4. Composition with the height-4000 capstone

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
  LiFacePrelude.re_taylorCoeff_nonneg_of_termwise 0 LiLadderHeight.re_liPairedSummand_zero_nonneg
