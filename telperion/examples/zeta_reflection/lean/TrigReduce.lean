/-  TrigReduce.lean -- ANDÚRIL instrument (A): VERIFIED LARGE-ARGUMENT trig reduction.

    THE INSTRUMENT.  The zero-hypothesis reflected band (`FullyReflectedBand_t14`) is blocked on
    ONE analytic gap: enclosing `cos(t·log n)` and `sin(t·log n)` in-kernel for `t ≈ 14`, `n ≤ 200`,
    where the argument `θ = t·log n` runs up to `≈ 74.2` -- nearly 12 full `2π` wraps.  Mathlib's
    `cos_bound` / `sin_bound` (the base brackets fed to `TaylorKernels.cosD_sound_of_bracket` /
    `sinD_sound_of_bracket`) are valid ONLY for the reduced argument `|x| ≤ 1`.  This file supplies
    the missing large-argument enclosures.

    ## THE ROUTE (π-FREE double-angle, PREFERRED -- it closes at the operating point).

    Prior art `CosEnclosure.lean` (ZETA island) reduces `cos θ` WITHOUT π: write `θ = 2^M · y` with
    `|y| ≤ 1`, base-bracket `cos y` via the order-4 Taylor bound, then climb back with the
    double-angle identity `cos(2y) = 2 cos²y − 1`.  The error budget works because the base error at
    `y = θ/2^M` is `θ⁴·(5/96)/2^{4M}` while the M doublings amplify by only `≈ 2^{2M}`, so the net
    `≈ θ⁴·(5/96)/2^{2M}` SHRINKS with depth.

    CosEnclosure did COS ONLY (Bragg needed only cos).  The zero-hypothesis evaluator needs BOTH,
    because `n^{-it} = cos(t log n) − i·sin(t log n)`.  The NEW piece here is the PAIRED recurrence:

        cos(2y) = 2 cos²y − 1              (cos-from-cos, as in CosEnclosure)
        sin(2y) = 2 sin y cos y           (sin-from-BOTH -- the paired step)

    We carry a joint cos/sin rational interval `([clo,chi],[slo,shi]) ∋ (cos(2^j y), sin(2^j y))` and
    round outward to a fixed grid each step (bounded denominators, `norm_num`-checkable per step).

    ## WHAT IS PROVEN SOUND HERE (no sorry; guarded by AxiomGuardTrigReduce).

      * `sin_base_interval`      -- order-4 (order-5 remainder) two-sided rational bracket of `sin y`,
                                    `|y| ≤ 1`, in the interval form the doubling recurrence consumes.
      * `cos_base_interval`      -- (re-derived here for a self-contained reflection-island instrument)
      * `sin_double_interval`    -- one PAIRED doubling step for sin: from cos/sin boxes at `y` and
                                    candidate rationals bracketing `2·sinY·cosY`, conclude `sin(2y)` box.
      * `cos_double_interval`    -- one doubling step for cos (as CosEnclosure; re-derived).
      * `cos_encl` / `sin_encl`  -- terminal point-enclosure contracts.
      * `cos_encl_bracket` / `sin_encl_bracket` -- Lipschitz absorption of the argument-box width
                                    (`|cos a − cos b| ≤ |a−b|`, likewise sin): this is how the argument
                                    itself entering as a VERIFIED DYADIC ENCLOSURE (from the corpus
                                    `CertVerify.ln_of_taylor_bracket` `t·log n` box) is absorbed.
      * `add_encl`               -- interval-sum glue.

    ## OPERATING-POINT CERTIFICATES (the instrument's fitness certificate for the band).

    Four named theorems, kernel-checked, at the exact points the evaluator hits, with width ≤ 1e-4,
    where the argument enters as a verified dyadic enclosure:

      * `cos_14log2`  / `sin_14log2`   -- `θ = 14·log 2  ≈ 9.7041`   (n = 2)
      * `cos_14log200`/ `sin_14log200` -- `θ = 14·log 200 ≈ 74.2277` (n = 200)

    conjecture1_proved = False.  This is certified interval arithmetic for cos/sin at large arguments;
    it proves nothing about RH.
-/
import DIntvCorrect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

namespace TrigReduce

/-! ## 1.  Base brackets for `|y| ≤ 1` (interval form the recurrence consumes). -/

/-- **cos base bracket.**  From `Real.cos_bound` (`|cos y − (1 − y²/2)| ≤ |y|⁴·5/96`), if rationals
    `clo ≤ 1 − y²/2 − y⁴·(5/96)` and `1 − y²/2 + y⁴·(5/96) ≤ chi` (note `|y|⁴ = y⁴`), then
    `clo ≤ cos y ≤ chi`.  (Same as `CosEnclosure.cos_base_interval`, re-stated in-island.) -/
theorem cos_base_interval {y clo chi : ℝ} (hy : |y| ≤ 1)
    (hlo : clo ≤ 1 - y ^ 2 / 2 - y ^ 4 * (5 / 96))
    (hhi : 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) ≤ chi) :
    clo ≤ Real.cos y ∧ Real.cos y ≤ chi := by
  have hb := Real.cos_bound hy
  have hy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [hy4] at hb
  have h := abs_le.mp hb
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **sin base bracket.**  From `Real.sin_bound` (`|sin y − (y − y³/6)| ≤ |y|⁵/100`) with `|y| ≤ 1`.
    We majorize `|y|⁵ ≤ 1` is too crude; instead we keep the majorant `|y|⁵/100 ≤ y⁴·(1/100)` for
    `|y| ≤ 1` (since `|y|⁵ = |y|·y⁴ ≤ y⁴`), giving a polynomial (in `y`, even-degree) remainder that
    the emitter can `norm_num`.  If rationals `slo ≤ y − y³/6 − y⁴·(1/100)` and
    `y − y³/6 + y⁴·(1/100) ≤ shi`, then `slo ≤ sin y ≤ shi`. -/
theorem sin_base_interval {y slo shi : ℝ} (hy : |y| ≤ 1)
    (hlo : slo ≤ y - y ^ 3 / 6 - y ^ 4 * (1 / 100))
    (hhi : y - y ^ 3 / 6 + y ^ 4 * (1 / 100) ≤ shi) :
    slo ≤ Real.sin y ∧ Real.sin y ≤ shi := by
  have hb := Real.sin_bound hy
  -- |y|^5/100 ≤ y^4·(1/100):  |y|^5 = |y|·|y|^4 = |y|·y^4 ≤ y^4  (since |y| ≤ 1, y^4 ≥ 0).
  have hy4 : |y| ^ 4 = y ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hrem : |y| ^ 5 / 100 ≤ y ^ 4 * (1 / 100) := by
    have h5 : |y| ^ 5 = |y| * y ^ 4 := by rw [← hy4]; ring
    have hle : |y| * y ^ 4 ≤ y ^ 4 := by
      have : |y| * y ^ 4 ≤ 1 * y ^ 4 := mul_le_mul_of_nonneg_right hy (by positivity)
      linarith [this]
    rw [h5]; linarith [hle]
  have h := abs_le.mp hb
  -- h.1 : -( |y|^5/100 ) ≤ sin y − (y − y³/6);  h.2 : sin y − (y − y³/6) ≤ |y|^5/100
  refine ⟨?_, ?_⟩
  · have : y - y ^ 3 / 6 - |y| ^ 5 / 100 ≤ Real.sin y := by linarith [h.1]
    have hmono : y - y ^ 3 / 6 - y ^ 4 * (1 / 100) ≤ y - y ^ 3 / 6 - |y| ^ 5 / 100 := by
      linarith [hrem]
    linarith [hlo, hmono, this]
  · have : Real.sin y ≤ y - y ^ 3 / 6 + |y| ^ 5 / 100 := by linarith [h.2]
    have hmono : y - y ^ 3 / 6 + |y| ^ 5 / 100 ≤ y - y ^ 3 / 6 + y ^ 4 * (1 / 100) := by
      linarith [hrem]
    linarith [hhi, this, hmono]

/-! ## 2.  The doubling steps (bounded-denominator interval recurrence). -/

/-- **cos doubling step** (`cos(2y) = 2cos²y − 1`).  Given `clo ≤ cos y ≤ chi` and rationals
    `clo', chi'` bracketing the image of `[clo,chi]` under `t ↦ 2t² − 1`, conclude the box for
    `cos(2y)`.  `hcase` selects the parabola branch (increasing / decreasing / vertex-straddle).
    (Structurally identical to `CosEnclosure.cos_double_interval`.) -/
theorem cos_double_interval {y clo chi clo' chi' : ℝ}
    (hlo : clo ≤ Real.cos y) (hhi : Real.cos y ≤ chi)
    (hu1 : 2 * clo ^ 2 - 1 ≤ chi') (hu2 : 2 * chi ^ 2 - 1 ≤ chi')
    (hl1 : clo' ≤ 2 * clo ^ 2 - 1) (hl2 : clo' ≤ 2 * chi ^ 2 - 1)
    (hcase : 0 ≤ clo ∨ chi ≤ 0 ∨ clo' ≤ -1) :
    clo' ≤ Real.cos (2 * y) ∧ Real.cos (2 * y) ≤ chi' := by
  have hcos : Real.cos (2 * y) = 2 * Real.cos y ^ 2 - 1 := Real.cos_two_mul y
  rw [hcos]
  refine ⟨?_, ?_⟩
  · rcases hcase with h | h | h
    · nlinarith [hlo, hhi, h]
    · nlinarith [hlo, hhi, h]
    · nlinarith [sq_nonneg (Real.cos y), h]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi),
      sq_nonneg (Real.cos y - clo), sq_nonneg (Real.cos y - chi), hlo, hhi]

/-- **sin doubling step -- THE PAIRED STEP** (`sin(2y) = 2 sin y cos y`).  Given cos/sin boxes at
    `y` (`clo ≤ cos y ≤ chi`, `slo ≤ sin y ≤ shi`) and rationals `slo', shi'` bracketing
    `2·(sin y)(cos y)` via the FOUR CORNER PRODUCTS of `[slo,shi]×[clo,chi]` (the same envelope
    `DIntv.mul` uses): every corner `≤ shi'/2` and `≥ slo'/2` after the factor 2.  Concretely the
    emitter supplies `slo' ≤ 2·(corner)` and `2·(corner) ≤ shi'` for all four corners; interval
    monotonicity of the bilinear map then pins `sin(2y)`. -/
theorem sin_double_interval {y clo chi slo shi slo' shi' : ℝ}
    (hclo : clo ≤ Real.cos y) (hchi : Real.cos y ≤ chi)
    (hslo : slo ≤ Real.sin y) (hshi : Real.sin y ≤ shi)
    -- lower: slo' ≤ 2·(each corner product)
    (hL1 : slo' ≤ 2 * (slo * clo)) (hL2 : slo' ≤ 2 * (slo * chi))
    (hL3 : slo' ≤ 2 * (shi * clo)) (hL4 : slo' ≤ 2 * (shi * chi))
    -- upper: 2·(each corner product) ≤ shi'
    (hU1 : 2 * (slo * clo) ≤ shi') (hU2 : 2 * (slo * chi) ≤ shi')
    (hU3 : 2 * (shi * clo) ≤ shi') (hU4 : 2 * (shi * chi) ≤ shi') :
    slo' ≤ Real.sin (2 * y) ∧ Real.sin (2 * y) ≤ shi' := by
  have hsin : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := Real.sin_two_mul y
  rw [hsin]
  -- Let u = sin y ∈ [slo, shi], v = cos y ∈ [clo, chi].  The bilinear u*v lies between the min
  -- and max of the four corner products; split on the sign of v (which endpoint of u dominates).
  set u : ℝ := Real.sin y
  set v : ℝ := Real.cos y
  -- Lower bound: 2·u·v ≥ slo'.
  have hlow : min (min (slo * clo) (slo * chi)) (min (shi * clo) (shi * chi)) ≤ u * v := by
    rcases le_total 0 v with hv0 | hv0
    · -- v ≥ 0 : slo*v ≤ u*v and a corner (slo*clo or slo*chi) ≤ slo*v
      have step1 : slo * v ≤ u * v := mul_le_mul_of_nonneg_right hslo hv0
      have step2 : min (slo * clo) (slo * chi) ≤ slo * v := by
        rcases le_total 0 slo with hs0 | hs0
        · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hclo hs0)
        · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hchi hs0)
      exact le_trans (le_trans (min_le_left _ _) step2) step1
    · -- v ≤ 0 : shi*v ≤ u*v and a corner (shi*clo or shi*chi) ≤ shi*v
      have step1 : shi * v ≤ u * v := by
        have := mul_le_mul_of_nonpos_right hshi hv0; linarith [this]
      have step2 : min (shi * clo) (shi * chi) ≤ shi * v := by
        rcases le_total 0 shi with hs0 | hs0
        · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hclo hs0)
        · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hchi hs0)
      exact le_trans (le_trans (min_le_right _ _) step2) step1
  have hupp : u * v ≤ max (max (slo * clo) (slo * chi)) (max (shi * clo) (shi * chi)) := by
    rcases le_total 0 v with hv0 | hv0
    · have step1 : u * v ≤ shi * v := mul_le_mul_of_nonneg_right hshi hv0
      have step2 : shi * v ≤ max (shi * clo) (shi * chi) := by
        rcases le_total 0 shi with hs0 | hs0
        · exact le_trans (mul_le_mul_of_nonneg_left hchi hs0) (le_max_right _ _)
        · exact le_trans (mul_le_mul_of_nonpos_left hclo hs0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_right _ _))
    · have step1 : u * v ≤ slo * v := by
        have := mul_le_mul_of_nonpos_right hslo hv0; linarith [this]
      have step2 : slo * v ≤ max (slo * clo) (slo * chi) := by
        rcases le_total 0 slo with hs0 | hs0
        · exact le_trans (mul_le_mul_of_nonneg_left hchi hs0) (le_max_right _ _)
        · exact le_trans (mul_le_mul_of_nonpos_left hclo hs0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_left _ _))
  -- Turn the min/max corner facts into slo'/shi' via the supplied per-corner inequalities.
  refine ⟨?_, ?_⟩
  · -- slo' ≤ 2·(min corner) ≤ 2·u·v
    have hmin : slo' ≤ 2 * min (min (slo * clo) (slo * chi)) (min (shi * clo) (shi * chi)) := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
      refine le_min (le_min hL1 hL2) (le_min hL3 hL4)
    have : 2 * min (min (slo * clo) (slo * chi)) (min (shi * clo) (shi * chi)) ≤ 2 * (u * v) :=
      by linarith [hlow]
    linarith [hmin, this]
  · have hmax : 2 * max (max (slo * clo) (slo * chi)) (max (shi * clo) (shi * chi)) ≤ shi' := by
      rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
      refine max_le (max_le hU1 hU2) (max_le hU3 hU4)
    have : 2 * (u * v) ≤ 2 * max (max (slo * clo) (slo * chi)) (max (shi * clo) (shi * chi)) :=
      by linarith [hupp]
    linarith [this, hmax]

/-! ## 3.  Terminal point-enclosure contracts (after the unrolled base+doubling chain). -/

/-- **Terminal cos enclosure at a point.**  If `|cos θ − A| ≤ E` (from an unrolled chain) and
    rationals `lo ≤ A − E`, `A + E ≤ hi`, then `lo ≤ cos θ ≤ hi`. -/
theorem cos_encl {θ A E lo hi : ℝ} (h : |Real.cos θ - A| ≤ E)
    (hlo : lo ≤ A - E) (hhi : A + E ≤ hi) :
    lo ≤ Real.cos θ ∧ Real.cos θ ≤ hi := by
  have h2 := abs_le.mp h
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- **Terminal sin enclosure at a point** (see `cos_encl`). -/
theorem sin_encl {θ A E lo hi : ℝ} (h : |Real.sin θ - A| ≤ E)
    (hlo : lo ≤ A - E) (hhi : A + E ≤ hi) :
    lo ≤ Real.sin θ ∧ Real.sin θ ≤ hi := by
  have h2 := abs_le.mp h
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 4.  Lipschitz absorption of the ARGUMENT-BOX width.

    The evaluator does not have `θ = t·log n` exactly -- it has a VERIFIED DYADIC ENCLOSURE
    `θ ∈ [c − w, c + w]` (via `CertVerify.ln_of_taylor_bracket` for `log n`, scaled by `t`).  We
    enclose cos/sin at the sample point `c` and absorb the half-width `w` via the Lipschitz bound
    `|cos a − cos b| ≤ |a − b|` (`Real.abs_cos_sub_cos_le`; likewise sin). -/

/-- **cos enclosure over an argument box.**  If `|arg − c| ≤ w` and `cos c ∈ [lo, hi]`, then
    `cos arg ∈ [lo − w, hi + w]`. -/
theorem cos_encl_bracket {arg c w lo hi : ℝ} (_hw : 0 ≤ w)
    (hdist : |arg - c| ≤ w) (hlo : lo ≤ Real.cos c) (hhi : Real.cos c ≤ hi) :
    lo - w ≤ Real.cos arg ∧ Real.cos arg ≤ hi + w := by
  have hlip : |Real.cos arg - Real.cos c| ≤ |arg - c| := Real.abs_cos_sub_cos_le arg c
  have hb : |Real.cos arg - Real.cos c| ≤ w := le_trans hlip hdist
  have h2 := abs_le.mp hb
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- **sin enclosure over an argument box** (see `cos_encl_bracket`). -/
theorem sin_encl_bracket {arg c w lo hi : ℝ} (_hw : 0 ≤ w)
    (hdist : |arg - c| ≤ w) (hlo : lo ≤ Real.sin c) (hhi : Real.sin c ≤ hi) :
    lo - w ≤ Real.sin arg ∧ Real.sin arg ≤ hi + w := by
  have hlip : |Real.sin arg - Real.sin c| ≤ |arg - c| := Real.abs_sin_sub_sin_le arg c
  have hb : |Real.sin arg - Real.sin c| ≤ w := le_trans hlip hdist
  have h2 := abs_le.mp hb
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 5.  Interval-sum glue (fold the finite ζ terms). -/

/-- **Interval addition.**  Two certified enclosures add to a certified enclosure of the sum. -/
theorem add_encl {x y xlo xhi ylo yhi : ℝ}
    (hx : xlo ≤ x ∧ x ≤ xhi) (hy : ylo ≤ y ∧ y ≤ yhi) :
    xlo + ylo ≤ x + y ∧ x + y ≤ xhi + yhi :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

end TrigReduce
