/-
  RvMDischarge.lean — the DISCHARGE of `RvMUnboundedMeanDensity zetaOrdinates`.

  Wires the kernel-clean distinct-bridge (`RvMDistinctBridge.lean`,
  `rvm_unbounded_mean_density_of_selberg`) to the PORTED superlinear-distinct
  theorem `HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline`
  (from cc-chen-tech/riemann-pnt-lean4 @ 6d07f7371, ported to v4.32).

  Result: `rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates`,
  sorry-free.  conjecture1_proved = False.
-/
import RvMDistinctBridge
import HardyTheorem.SelbergStrictCancellationZeroCover

open RvMGlue

namespace RvMGlue

/-- `criticalLineOddZerosFinset` elements are genuine nontrivial zeros with
`re = 1/2`, `0 ≤ im ≤ T` — exactly the `hZmem` interface of the bridge.
`riemannZeta ρ = 0` comes from `RiemannHypothesis.IsNontrivialZero`. -/
theorem oddFinset_mem
    (T : ℝ) (ρ : ℂ) (hρ : ρ ∈ HardyTheorem.criticalLineOddZerosFinset T) :
    riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T := by
  -- ρ is in the odd-order filter of criticalLineZerosFinset
  have hmem : ρ ∈ HardyTheorem.criticalLineZerosFinset T :=
    (Finset.mem_filter.mp hρ).1
  obtain ⟨hnt, hre, him0, himT⟩ :=
    HardyTheorem.mem_criticalLineZerosFinset.mp hmem
  exact ⟨hnt.1, hre, him0, himT⟩

/-- **DISCHARGE.**  The ordinates of the nontrivial zeta zeros have unbounded
windowed mean density — unconditionally, kernel-clean. -/
theorem rvm_unbounded_mean_density :
    RvMUnboundedMeanDensity zetaOrdinates := by
  apply rvm_unbounded_mean_density_of_selberg
    (zerosFinset := HardyTheorem.criticalLineOddZerosFinset)
    (oddCount := HardyTheorem.criticalLineOddZeroCount)
  · -- hZcard : oddCount T = (zerosFinset T).card
    intro T
    rfl
  · -- hZmem
    intro T ρ hρ
    exact oddFinset_mem T ρ hρ
  · -- hSelberg : ∃ c>0, ∃ T0, ∀ T≥T0, (oddCount T:ℝ) ≥ c*(T/(2π)*log T)
    obtain ⟨c, hc, T0, hT⟩ :=
      HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline
    exact ⟨c, hc, T0, hT⟩

end RvMGlue
