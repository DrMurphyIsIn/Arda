/- CONFINEMENT (kernel): every nontrivial zeta zero up to height T lies in the band [a, 1-a].

   This is the "confinement" half of the "all zeros up to height T are on the line" project:
   box-localization (all zeros IN a box on the line, PR #312) + confinement (all zeros ARE in the
   box, this file).  We prove the confinement:

     `zero_in_band` :  a nontrivial zero `ρ` (`ζ ρ = 0`, `0 < ρ.im ≤ T`) with `a ≤ dlvpRateC/log T`
                       satisfies  `a ≤ ρ.re ≤ 1 - a`.

   Both edges come from the SELF-CONTAINED effective de la Vallée Poussin zero-free region
   `ZeroFreeBridge.riemannZeta_ne_zero_region` (PR #318 -- no multiplicity input, β≥3/4 discharged
   internally): `ζ(β+iγ) ≠ 0` for `|γ| ≥ 55/16` and `β > 1 - dlvpRateC/log|γ|`.

   - RIGHT edge `ρ.re ≤ 1-a`:  contrapositive of the region at `ρ` gives `ρ.re ≤ 1 - dlvpRateC/log|γ|`,
     and `dlvpRateC/log|γ| ≥ dlvpRateC/log T ≥ a` (log monotone, `|γ| = ρ.im ≤ T`; `dlvpRateC > 0`).
   - LEFT edge `a ≤ ρ.re`:  reflect through the functional equation.  `ζ ρ = 0` ⟹ `Λ ρ = 0`
     (unconditional strip bridge: `ρ.im ≠ 0` ⟹ `Gammaℝ ρ ≠ 0`) ⟹ `Λ (1-ρ) = 0`
     (`completedRiemannZeta_one_sub`) ⟹ `ζ (1-ρ) = 0` (strip bridge again, `(1-ρ).im = -ρ.im ≠ 0`).
     The reflected zero has real part `1-ρ.re`, height `-ρ.im`, `|-ρ.im| = |ρ.im| ≥ 55/16`.  The
     region contrapositive on it gives `1-ρ.re ≤ 1 - dlvpRateC/log|γ| ≤ 1 - a`, i.e. `ρ.re ≥ a`.

   RESIDUAL (documented, honest -- a genuine Mathlib gap, NOT a fake).  Mathlib has no "no zeta
   zeros with `|Im| < 14`" fact (the first nontrivial zero is at height ~14.13 > 55/16 ~ 3.44), so
   the region's height-floor hypothesis `55/16 ≤ |ρ.im|` is carried as an ADDED hypothesis `hγ` on
   `zero_in_band`.  It is a small classical fact, discharged at the concrete T=100 instantiation
   from the on-line sweep (all 29 zeros up to 100 have height ≥ 14 > 55/16).  No multiplicity input,
   no `β ≥ 3/4` casework, no `0 < ρ.re` strip hypothesis (the FE strip bridge here is unconditional
   for `ρ.im ≠ 0`).

   conjecture1_proved = False (a kernel-verified reduction of confinement to the effective dVP
   region + the functional equation, NOT a proof of RH).
-/
import Mathlib
import DlvpZetaZeroFree

open Complex

namespace ZetaZeroConfinement

/-- **Unconditional strip bridge for off-real points.**  For `ρ.im ≠ 0` the Archimedean factor
    `Gammaℝ ρ` is nonzero (its only zeros are the non-positive even integers, all real), so
    `riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0`. -/
theorem zeta_zero_iff_completed_zero_of_im_ne {ρ : ℂ} (him : ρ.im ≠ 0) :
    riemannZeta ρ = 0 ↔ completedRiemannZeta ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; apply him; rw [h]; simp
  have hGne : Gammaℝ ρ ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply him
    rw [hn]
    simp
  rw [riemannZeta_def_of_ne_zero hρ0, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hGne
  · intro h; exact Or.inl h

/-- **The functional-equation reflection of an off-real zeta zero.**  `ζ ρ = 0` with `ρ.im ≠ 0`
    forces `ζ (1 - ρ) = 0`. -/
theorem zeta_zero_reflect {ρ : ℂ} (him : ρ.im ≠ 0) (hzero : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 := by
  have hΛ : completedRiemannZeta ρ = 0 := (zeta_zero_iff_completed_zero_of_im_ne him).1 hzero
  have hΛ' : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub]; exact hΛ
  have him' : (1 - ρ).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]; exact him
  exact (zeta_zero_iff_completed_zero_of_im_ne him').2 hΛ'

/-- **CONFINEMENT.**  Every nontrivial zeta zero up to height `T` lies in the band `[a, 1-a]`.

    Over real `a, T` with `a ≤ dlvpRateC / log T`, `0 < a`, `100 ≤ T`, a zero `ρ` with `ζ ρ = 0`,
    `0 < ρ.im ≤ T`, and height at least the region floor `55/16 ≤ |ρ.im|` (documented residual --
    see the module header) satisfies `a ≤ ρ.re ∧ ρ.re ≤ 1 - a`.  Both edges are derived from the
    self-contained effective dVP zero-free region + the functional equation. -/
theorem zero_in_band (a T : ℝ) (haC : a ≤ ZeroFreeBridge.dlvpRateC / Real.log T)
    (ha0 : 0 < a) (hT : 100 ≤ T)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (him0 : 0 < ρ.im) (himT : ρ.im ≤ T)
    (hγ : 55 / 16 ≤ |ρ.im|) :
    a ≤ ρ.re ∧ ρ.re ≤ 1 - a := by
  -- Positivity of the two logarithms and the rate constant.
  have hcpos := ZeroFreeBridge.dlvpRateC_pos
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have habs : |ρ.im| = ρ.im := abs_of_pos him0
  have hlogγpos : 0 < Real.log |ρ.im| := by
    rw [habs]; exact Real.log_pos (by rw [habs] at hγ; linarith)
  -- `dlvpRateC / log|ρ.im| ≥ dlvpRateC / log T ≥ a` (log monotone, `|ρ.im| = ρ.im ≤ T`).
  have hlogmono : Real.log |ρ.im| ≤ Real.log T := by
    rw [habs]; exact Real.log_le_log him0 himT
  have hdiv_ge : a ≤ ZeroFreeBridge.dlvpRateC / Real.log |ρ.im| := by
    refine le_trans haC ?_
    exact div_le_div_of_nonneg_left (le_of_lt hcpos) hlogγpos hlogmono
  -- Rewrite `ρ` in the `(re) + (im)*I` form the region theorem expects.
  have hρ : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * I := (Complex.re_add_im ρ).symm
  refine ⟨?_, ?_⟩
  · -- LEFT edge `a ≤ ρ.re`: reflect through the FE, then apply the region to `1 - ρ`.
    have him_ne : ρ.im ≠ 0 := ne_of_gt him0
    have hrefl : riemannZeta (1 - ρ) = 0 := zeta_zero_reflect him_ne hzero
    -- `1 - ρ = ((1 - ρ.re) : ℂ) + ((-ρ.im) : ℂ) * I`.
    have hsub : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) + ((-ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hγ' : 55 / 16 ≤ |(-ρ.im)| := by rwa [abs_neg]
    -- Contrapositive of the region on the reflected zero.
    by_contra hlt
    have hlt' : ρ.re < a := not_le.mp hlt
    have hβlow : 1 - ZeroFreeBridge.dlvpRateC / Real.log |(-ρ.im)| < 1 - ρ.re := by
      rw [abs_neg]
      -- from `a ≤ dlvpRateC/log|ρ.im|` and `ρ.re < a`.
      linarith [hdiv_ge, hlt']
    have hne :=
      ZeroFreeBridge.riemannZeta_ne_zero_region (1 - ρ.re) (-ρ.im) hγ' hβlow
    rw [← hsub] at hne
    exact hne hrefl
  · -- RIGHT edge `ρ.re ≤ 1 - a`: contrapositive of the region on `ρ` itself.
    by_contra hgt
    have hgt' : 1 - a < ρ.re := not_le.mp hgt
    have hβlow : 1 - ZeroFreeBridge.dlvpRateC / Real.log |ρ.im| < ρ.re := by
      linarith [hdiv_ge, hgt']
    have hne :=
      ZeroFreeBridge.riemannZeta_ne_zero_region ρ.re ρ.im hγ hβlow
    rw [← hρ] at hne
    exact hne hzero

end ZetaZeroConfinement
