/-
RvMNTLadder — Arc A (effective RvM), PR A5: the ladder interlock — `hζne` collapses to one point.

The effective RvM bound (PR A2) carries the segment hypothesis `hζne` (`ζ ≠ 0` on `[1/2,2]+iT`).
The tiled Turing ladder proves (from its certified per-band winding bundles) that every nontrivial
zero up to height `4000` lies ON the critical line.  Those two facts interlock: for `T ≤ 4000`, a
zero at `x + iT` with `x > 1/2` would contradict the ladder, so the whole segment hypothesis
collapses to the SINGLE point `ζ(1/2 + iT) ≠ 0` — the "`T` is not a zero-ordinate" caveat becomes
literally one point.

  * `zeta_segment_ne_zero_of_ladder` — ladder conclusion + the single-point nonvanishing ⟹ `hζne`.
  * `nt_effective_bound_of_ladder` — the effective RvM bound with the trust-shrunk hypothesis set.

The ladder conclusion enters as an explicit hypothesis `hladder` (exactly the statement proved by
`AllZeros_h4000.all_nontrivial_zeros_up_to_height_4000_of_bands` from its certified Arb bundles,
ported onto this island), so this file states the pure interlock; instantiation with the ladder's
bundles is the ported corollary.  Honesty: nothing here bears on RH — the ladder is a finite
verification, the count is classical, and the single-point caveat is genuine (S(T) jumps at zero
ordinates).  conjecture1_proved = False.
-/
import Mathlib
import RvMNTEffective

open Complex Real MeasureTheory DiffractionCore

namespace Backlund

/-- **The segment hypothesis collapses to one point under the ladder.**  If every nontrivial zero
up to height `4000` is on the critical line, and `ζ(1/2 + iT) ≠ 0`, then `ζ ≠ 0` on the whole
segment `[1/2,2] + iT` (for `0 < T ≤ 4000`): a zero at `x + iT` with `x > 1/2` would be a
nontrivial zero off the line.  conjecture1_proved = False. -/
theorem zeta_segment_ne_zero_of_ladder {T : ℝ} (hT : 0 < T) (hT4 : T ≤ 4000)
    (hladder : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2)
    (hhalf : riemannZeta (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) ≠ 0) :
    ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · rw [← heq]; exact hhalf
  · intro h0
    have him : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
    have hre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
    have := hladder _ h0 (by rw [him]; exact hT) (by rw [him]; exact hT4)
    rw [hre] at this
    linarith

/-- **The effective RvM bound under the ladder — the trust-shrunk form.**  For `4 ≤ T ≤ 4000`,
with the ladder conclusion `hladder`, the box-edge ξ-nonvanishings, the boundary winding `= 2πiN`,
and the SINGLE-POINT caveat `ζ(1/2 + iT) ≠ 0` (in place of the whole-segment `hζne`):

  `|N − 1 − θ(T)/π| ≤ log((4T+19)/(2 − π²/6)) / log(7/6) + 2`.

The two RH tracks interlock in one kernel statement: the ladder's on-line verification supplies
the analytic input the counting formula's error term needs, shrinking the classical caveat to a
point.  conjecture1_proved = False. -/
theorem nt_effective_bound_of_ladder (T : ℝ) (hT : 4 ≤ T) (hT4 : T ≤ 4000) (N : ℤ)
    (hladder : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ 4000 → ρ.re = 1 / 2)
    (hhalf : riemannZeta (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzBot : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ)) ≠ 0)
    (hnzTop : ∀ x ∈ Set.Icc (-1:ℝ) 2, xiTele ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hnzL : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((-1:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hnzR : ∀ y ∈ Set.Icc (0:ℝ) T, xiTele (((2:ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hwind : (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((0:ℝ) : ℂ) * I))
        - (∫ x in (-1:ℝ)..2, logDeriv xiTele (↑x + ((T:ℝ) : ℂ) * I))
        + I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((2:ℝ) : ℂ) + ↑y * I))
        - I • (∫ y in (0:ℝ)..T, logDeriv xiTele (((-1:ℝ) : ℂ) + ↑y * I))
      = 2 * ↑π * I * (N : ℂ)) :
    |(N : ℝ) - 1 - ZeroFreeBridge.riemannSiegelTheta T / π|
      ≤ Real.log ((4 * T + 19) / (2 - Real.pi ^ 2 / 6)) / Real.log (7 / 6) + 2 :=
  nt_effective_bound T hT N hnzBot hnzTop hnzL hnzR
    (zeta_segment_ne_zero_of_ladder (by linarith) hT4 hladder hhalf) hwind

end Backlund
