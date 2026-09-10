/-
RvMLiFrontierA — the ξ version of the explicit formula: adding the Γℝ archimedean
piece (and the pole) to the ζ explicit formula.

FRONTIER ITEM (a).  Our finite explicit formula (`li_finite_explicit_formula`,
Stratum 3) is stated for `ζ`.  The Li coefficients live on `ξ = ½·s(s−1)·Λ`, whose
log-derivative decomposes as

  `(log ξ)' = 1/s + 1/(s−1) + (log ζ)' + (log Γℝ)'`.

So the ξ-weighted zero-sum is the ζ-weighted sum PLUS the archimedean part
`(log Γℝ)'` PLUS the pole part `1/s + 1/(s−1)`.  This file lands that split, both
pointwise and as a boundary-integrand identity — the exact content of "add the Γℝ
archimedean piece":

  * `logDeriv_xiTele_four_split` — the pointwise four-way split of `(log ξ)'`.
  * `xiTele_weighted_integrand_split` — the weighted boundary integrand
    `g·(log ξ)' = g/s + g/(s−1) + g·(log ζ)' + g·(log Γℝ)'`, so any boundary
    integral of `g·(log ξ)'` splits into the ζ explicit-formula term (primes, via
    `li_finite_explicit_formula`), the archimedean `Γℝ` term, and the two pole terms.

The archimedean term `∮ g·(log Γℝ)'` is the piece whose `T→∞` boundary asymptotics
give the Li main term `~(n/2)log n` — that limit/extraction is frontier (b)+(c),
NOT built here.  This file makes the *algebraic* augmentation precise and
kernel-checked.  conjecture1_proved = False.
-/
import RvMDiffractionCore

namespace DiffractionCore

open Complex

/-- **The four-way split of `(log ξ)'`** (frontier (a), pointwise).  For `s ∉ {0,1}`
    with `ζ(s) ≠ 0` and `Γℝ(s) ≠ 0`:

      `logDeriv ξ s = 1/s + 1/(s−1) + logDeriv ζ s + logDeriv Γℝ s`.

    The ξ log-derivative is the ζ one plus the archimedean `Γℝ` piece plus the pole
    `1/s + 1/(s−1)`.  Immediate from `logDeriv_xiTele_split` (ξ = pole + Λ) and
    `logDeriv_zeta_add_gammaR` (Λ = ζ · Γℝ). -/
theorem logDeriv_xiTele_four_split {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    logDeriv xiTele s
      = s⁻¹ + (s - 1)⁻¹ + logDeriv riemannZeta s + logDeriv Gammaℝ s := by
  rw [logDeriv_xiTele_split hs0 hs1 hζ hG, logDeriv_zeta_add_gammaR hs0 hs1 hζ hG]
  ring

/-- **The weighted boundary integrand split** (frontier (a), integrated form).  For
    any weight `g` and a strip point (`s ∉ {0,1}`, `ζ ≠ 0`, `Γℝ ≠ 0`):

      `g·(log ξ)' = g/s + g/(s−1) + g·(log ζ)' + g·(log Γℝ)'`.

    Integrating this over the box boundary decomposes the ξ-weighted winding into:
    the ζ explicit-formula term (which `li_finite_explicit_formula` resolves to the
    von Mangoldt prime sum), the archimedean `Γℝ` term, and the two pole terms.
    This is exactly "the ξ version = the ζ version + the Γℝ archimedean piece". -/
theorem xiTele_weighted_integrand_split (g : ℂ → ℂ) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    g s * logDeriv xiTele s
      = g s * s⁻¹ + g s * (s - 1)⁻¹ + g s * logDeriv riemannZeta s + g s * logDeriv Gammaℝ s := by
  rw [logDeriv_xiTele_four_split hs0 hs1 hζ hG]
  ring

end DiffractionCore
