/-  Corner- and count-generic RH-in-box counting core.

    `conjecture1_proved = False`.  This is a verification of the STRUCTURE of the
    counting argument for arbitrary box corners and an arbitrary Finset of on-line
    zeros.  It is NOT a proof of the Riemann Hypothesis.

    The key reuse: `BoxLocalization.exhaustion_by_count` (already generic in `s`, `T`,
    `d`, and `n`) is applied with `n := T.card` and `hTcard := rfl`.  The fixed literal
    corners and the hard-coded 5-tuple `z1..z5` from `box_localization_core` are
    replaced by real-valued corner VARIABLES `sigma0 sigma1 T0 T1` and an abstract
    Finset `T` of any cardinality. -/
import Mathlib
import BoxLocalization   -- reuse exhaustion_by_count

open Complex

namespace RHInBoxCore

/-- **Counting capstone, corner- and count-generic.**

    Let `s` be a finite support, `d : C -> Z` a multiplicity, `T subset s` a sub-Finset
    of on-line zeros (i.e. every `z in T` satisfies `z.re = 1/2`), and
    `sigma0 sigma1 T0 T1 : R` arbitrary box corners.  Hypotheses:
    * `hd1`      : `d rho >= 1` for every `rho in s`;
    * `hTsub`    : `T subset s`;
    * `hTline`   : every `z in T` has `z.re = 1/2`;
    * `hcount`   : `sum_{rho in s} d rho = T.card` (the total divisor equals the
                   number of on-line zeros; `T.card` replaces the fixed `5`);
    * `hzero_in` : every zeta zero in the box `[sigma0,sigma1] x [T0,T1]` lies in `s`.
    Conclusion: every such zeta zero has `re = 1/2`.

    `conjecture1_proved = False`. -/
theorem rh_in_box_core
    (sigma0 sigma1 T0 T1 : ℝ)
    (s T : Finset ℂ) (d : ℂ → ℤ)
    (hd1 : ∀ ρ ∈ s, (1 : ℤ) ≤ d ρ)
    (hTsub : T ⊆ s)
    (hTline : ∀ z ∈ T, z.re = 1 / 2)
    (hcount : (∑ ρ ∈ s, d ρ) = (T.card : ℤ))
    (hzero_in : ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ ∈ s) :
    ∀ ρ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  obtain ⟨hsT, _⟩ := BoxLocalization.exhaustion_by_count hTsub rfl hd1 hcount
  intro ρ hre him hρ0
  have hρs : ρ ∈ s := hzero_in ρ hre him hρ0
  rw [hsT] at hρs
  exact hTline ρ hρs

end RHInBoxCore
