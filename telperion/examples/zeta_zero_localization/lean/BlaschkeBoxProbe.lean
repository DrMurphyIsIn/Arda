/- STAGE 2B FEASIBILITY PROBE (THROWAWAY -- NOT CI-WIRED).

   Question: is the LOCAL Blaschke split of `Λ = completedRiemannZeta` over a strip box
     `Λ'/Λ z = Σ_{ρ ∈ B} (divisor Λ ρ)/(z - ρ) + E z`,  with  E holomorphic on cl(B),
   derivable in Lean/Mathlib (GO), or must it be carried as a hypothesis (NO-GO)?

   This file is a TOY REDUCTION on an explicit finite product of factors
     `f z = ∏_{i} (z - u i) ^ (d i)`
   (the `Finset`-form that Mathlib's `∏ᶠ u, (· - u) ^ (divisor f U u)` collapses to via
   `finprod_eq_prod_of_mulSupport_subset` once the divisor support is finite).  It proves the
   log-derivative expansion
     `logDeriv f z = Σ_i (d i) / (z - u i) + logDeriv g z`     (here g = 1, `logDeriv g = 0`)
   at any box point `z` avoiding the roots, using ONLY Mathlib lemmas that exist in v4.32.0:
     - `logDeriv_prod`      (finite-product log-derivative sum)
     - `logDeriv_fun_zpow`  (`logDeriv (h ·^n) = n * logDeriv h`)
     - `deriv_sub_const` / `logDeriv_apply`  (`logDeriv (·-u) z = 1/(z-u)`)

   The point: E = `logDeriv g` is manifestly holomorphic on the region where `g` is analytic and
   zero-free, which is exactly the output of Mathlib `MeromorphicOn.extract_zeros_poles`.  So the
   real-thing chain is CONCRETE and BOUNDED -- see ZETA_BOX_STAGE2B_PROBE.md.  GO.

   conjecture1_proved = False (NOT a proof of RH).

   NOTE: not imported by any built target; not in any lakefile `defaultTargets`.
-/
import Mathlib

open Complex

namespace BlaschkeBoxProbe

/-- `logDeriv (fun z => z - u) z = 1 / (z - u)` off the root `u`.  Elementary building block. -/
theorem logDeriv_sub_const {u z : ℂ} (_hzu : z - u ≠ 0) :
    logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
  rw [logDeriv_apply]
  have hderiv : deriv (fun w : ℂ => w - u) z = 1 := by
    simp [deriv_sub_const (f := fun w : ℂ => w) u (x := z)]
  rw [hderiv]

/-- `logDeriv (fun z => (z - u) ^ d) z = d / (z - u)` off the root `u`. -/
theorem logDeriv_factor {u z : ℂ} (d : ℤ) (hzu : z - u ≠ 0) :
    logDeriv (fun w : ℂ => (w - u) ^ d) z = (d : ℂ) / (z - u) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
  rw [logDeriv_fun_zpow hdiff d, logDeriv_sub_const hzu]
  ring

/-- **Toy Stage-2B split.**  For a finite index set `s` of DISTINCT roots `u i` with integer
    multiplicities `d i`, the factorized rational `f z = ∏_{i∈s} (z - u i) ^ (d i)` has
    `logDeriv f z = Σ_{i∈s} (d i)/(z - u i) + logDeriv g z`, with `g = 1` (so `logDeriv g = 0`),
    at any `z` avoiding every root.  E := `logDeriv g` is holomorphic everywhere -- the box case
    below is the special case where `s` is `divisor Λ U` restricted to `B` and `g` is the analytic
    zero-free remainder from `MeromorphicOn.extract_zeros_poles`. -/
theorem toy_blaschke_split {s : Finset ℂ} (d : ℂ → ℤ)
    (z : ℂ) (hz : ∀ u ∈ s, z - u ≠ 0) :
    logDeriv (fun w : ℂ => ∏ u ∈ s, (w - u) ^ (d u)) z
      = (∑ u ∈ s, (d u : ℂ) / (z - u)) + (0 : ℂ) := by
  -- logDeriv of a finite product is the sum of log-derivatives (each factor nonzero at z).
  have hne : ∀ u ∈ s, ((fun w : ℂ => (w - u) ^ (d u)) z) ≠ 0 := by
    intro u hu
    exact zpow_ne_zero _ (hz u hu)
  have hdiff : ∀ u ∈ s, DifferentiableAt ℂ (fun w : ℂ => (w - u) ^ (d u)) z := by
    intro u hu
    have hbase : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
    exact (differentiableAt_zpow.2 (Or.inl (hz u hu))).comp z hbase
  rw [add_zero]
  -- Name the per-root factor functions and rewrite the product-of-values as the pointwise Finset
  -- product `fun w => ∏ u ∈ s, F u w`, so Mathlib `logDeriv_prod` applies.
  set F : ℂ → ℂ → ℂ := fun u w => (w - u) ^ (d u) with hF
  have hfun : (fun w : ℂ => ∏ u ∈ s, (w - u) ^ (d u)) = fun w : ℂ => ∏ u ∈ s, F u w := rfl
  rw [hfun]
  rw [logDeriv_prod (s := s) (f := F) (x := z) hne hdiff]
  apply Finset.sum_congr rfl
  intro u hu
  exact logDeriv_factor (d u) (hz u hu)

/-!
## Real-thing shape (documentation only, stated as the Task-7 target).

The capstone box is `B = [2/5, 3/5] × [10, 35]` (rational corners, `0 < 2/5 < 1/2 < 3/5 < 1`,
`T0 = 10 > 0`).  Because `T0 > 0` and `σ1 = 3/5 < 1`, the box EXCLUDES Λ's poles `s = 0, s = 1`
and the trivial zeros, so on an open neighborhood `U` of `cl(B)` avoiding `{0, 1}`, Λ is analytic
(`differentiableAt_completedZeta`), hence `MeromorphicOn`, and its only zeros in `U` are the
nontrivial ones.

The GO chain (all Mathlib v4.32.0 lemmas confirmed to exist; see ZETA_BOX_STAGE2B_PROBE.md):

  1. `Λ` analytic on `cl(B) ⊆ U` open  ⇒  `hΛ : MeromorphicOn Λ U`  and
     `divisor_support_finite_of_subset` (on the compact `cl(B)`) ⇒ `(divisor Λ U).support.Finite`.
  2. `MeromorphicOn.extract_zeros_poles hΛ _ _`  ⇒  `∃ g, AnalyticOnNhd ℂ g U ∧ (∀ u:U, g u ≠ 0) ∧
       Λ =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ (divisor Λ U u)) • g`.
  3. `finprod_eq_prod_of_mulSupport_subset` (finite support) turns the `∏ᶠ` into the `Finset`
     product handled by `toy_blaschke_split` above, giving the principal-part sum.
  4. `logDeriv_congr_of_codiscrete` (in-repo `DlvpTransfer`, function-agnostic) transfers the
     log-derivative across the codiscrete equality on preconnected open `U`.
  5. `logDeriv_mul` + step 3  ⇒
       `logDeriv Λ z = Σ_{ρ ∈ B} (divisor Λ U ρ)/(z - ρ) + logDeriv g z`,
     and `E := logDeriv g` is holomorphic on `U ⊇ cl(B)` because `g` is analytic and zero-free
     there (`AnalyticAt.logDeriv`-style; `logDeriv g = deriv g / g` with `g ≠ 0`).

  Verdict: GO.  No unbuilt Mathlib machinery is required; E-holomorphicity is `logDeriv` of the
  analytic zero-free remainder `g`, strictly simpler than the in-repo disk Blaschke split (which
  additionally carries the bounded `-conj u/(R² - conj u · z)` correction needed only for the
  Herglotz positivity on a disk; the box localization does NOT need positivity).
-/

end BlaschkeBoxProbe
