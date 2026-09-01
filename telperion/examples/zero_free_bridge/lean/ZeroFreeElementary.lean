/- ELEMENTARY UNCONDITIONAL ZERO-FREE REGION (polynomial rate) -- the Hadamard-free route.

   The classical de la Vallee Poussin region needs `|ζ| ≪ log|t|` (the sharp near-line bound),
   which requires the Hadamard factorization of ξ (Jensen's formula, canonical products, the ζ'/ζ
   partial fraction -- ALL absent from Mathlib v4.32.0).  But a GENUINE UNCONDITIONAL region with a
   POLYNOMIAL rate is reachable from elementary tools ALONE:

     - the product inequality `|ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1`  (Mathlib nonvanishing machinery,
       `norm_LFunction_product_ge_one`, specialized to ζ),
     - the CRUDE strip growth bound `|ζ(σ+it)| ≤ C·|t|`             (Phase 2, `zeta_strip_bound`),
     - the pole `|ζ(σ)| ≤ C/(σ-1)` near `s = 1`                     (Mathlib residue),
     - Cauchy's derivative estimate `|ζ'| ≤ C·|t|` on a disk        (Mathlib) => near a zero `β+iγ`,
       `|ζ(σ+iγ)| = |ζ(σ+iγ) - ζ(β+iγ)| ≤ (σ-β)·sup|ζ'|`.

   Choosing `σ = 2 - β` (so `σ-1 = 1-β` and `σ-β = 2(1-β)`) makes the estimate PURELY INTEGER-POWER:
   the product bound reads `1 ≤ 16 c₁³ c₂ c₄⁴ (1-β) γ⁵`, giving

       β ≤ 1 - 1/(16 c₁³ c₂ c₄⁴ |γ|⁵),   i.e. a zero-free region  Re s > 1 - c/|t|⁵.

   Weaker than de la Vallee Poussin's `1 - c/log|t|` (the crude `|t|` growth, not `log|t|`, is what
   costs the rate), but a REAL, UNCONDITIONAL zero-free region -- and every input is elementary,
   sidestepping the Hadamard wall entirely.  This file is the ASSEMBLY (four bounds -> region);
   discharging the four bounds (all reachable) is the follow-on.  conjecture1_proved = False.
-/
import ZeroFreeBridge

namespace ZeroFreeBridge

/-- ELEMENTARY ZERO-FREE REGION ASSEMBLY.  At `σ = 2 - β` and height `γ ≥ 1`, given the four
    elementary bounds on the zeta magnitudes `Zσ = |ζ(2-β)|`, `Zσt = |ζ((2-β)+iγ)|`,
    `Zσ2t = |ζ((2-β)+2iγ)|` -- the product inequality, the pole bound, the crude strip growth
    bound, and the Cauchy-derivative bound at the zero -- the zero at `β+iγ` is pushed left of the
    1-line by an explicit polynomial gap `1/(16 c₁³ c₂ c₄⁴ γ⁵) ≤ 1 - β`. -/
theorem zeta_zero_free_poly_of {β γ c₁ c₂ c₄ Zσ Zσt Zσ2t : ℝ}
    (hβ1 : β < 1) (hγ : 1 ≤ γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₄ : 0 < c₄)
    (hZσ : 0 ≤ Zσ) (hZσt : 0 ≤ Zσt) (hZσ2t : 0 ≤ Zσ2t)
    (hprod : 1 ≤ Zσ ^ 3 * Zσt ^ 4 * Zσ2t)
    (hpole : Zσ ≤ c₁ / (1 - β))
    (hstrip : Zσ2t ≤ c₂ * γ)
    (hcauchy : Zσt ≤ 2 * (1 - β) * c₄ * γ) :
    1 / (16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * γ ^ 5) ≤ 1 - β := by
  have hη : 0 < 1 - β := by linarith
  have hγ0 : 0 < γ := by linarith
  -- Bound the product of magnitudes by the product of the four elementary bounds (all ≥ 0).
  have hub : Zσ ^ 3 * Zσt ^ 4 * Zσ2t
      ≤ (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * γ) := by
    gcongr
  -- The `(1-β)³` in the pole cube cancels three of the four `(1-β)` powers from the Cauchy 4th power.
  have hsimp : (c₁ / (1 - β)) ^ 3 * (2 * (1 - β) * c₄ * γ) ^ 4 * (c₂ * γ)
      = 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 5 := by
    field_simp
    ring
  rw [hsimp] at hub
  have h1 : (1 : ℝ) ≤ 16 * c₁ ^ 3 * c₂ * c₄ ^ 4 * (1 - β) * γ ^ 5 := le_trans hprod hub
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h1]

/-- DISCHARGE of `hprod` for `riemannZeta`: the 3-4-1 product inequality
    `|ζ(1+x)|³ |ζ(1+x+iy)|⁴ |ζ(1+x+2iy)| ≥ 1` for `x > 0`, specialized from Mathlib's Dirichlet
    nonvanishing machinery (`DirichletCharacter.norm_LFunction_product_ge_one` at modulus `1`, where
    `LFunction_modOne_eq` sends every mod-1 character's L-function to `riemannZeta`). -/
theorem zeta_norm_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + Complex.I * y)‖ ^ 4
        * ‖riemannZeta (1 + x + 2 * Complex.I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one
    (χ := (1 : DirichletCharacter ℂ 1)) hx y
  rw [ge_iff_le] at h
  -- `LFunctionTrivChar 1 = riemannZeta` (the mod-1 trivial character) and every mod-1
  -- character's L-function is `riemannZeta` (`LFunction_modOne_eq`, a `@[simp]` lemma).
  have htriv : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq
  rw [htriv] at h
  simp only [DirichletCharacter.LFunction_modOne_eq, norm_mul, norm_pow] at h
  exact h

end ZeroFreeBridge
