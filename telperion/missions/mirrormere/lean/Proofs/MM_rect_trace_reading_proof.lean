/-
  Proofs.MM_rect_trace_reading_proof -- AUTHORED proof of node
  MM_rect_trace_reading (D1: the trace reading of the Bragg bridge).

  Content: a finite algebraic REPACKAGING of the kernel theorem
  `DiffractionCore.rect_explicit_formula_bragg`
  (telperion/examples/li_positivity/lean/RvMBraggBridge.lean:123, rh/million-turing
  @ 5762a2b8c). Same hypotheses; the divisor count is isolated on the left and the
  bridge RHS divided through by 2πi. The single nontrivial step is dividing the
  identity `(2πi)·S = RHS` by the nonzero scalar 2πi (2πi ≠ 0 from
  Real.pi_ne_zero, Complex.I_ne_zero), then cancelling.

  BUILD/VERIFICATION STATUS (zero-drift honesty): this module imports the REAL
  li-positivity island (RvMBraggBridge, RvMRHInBox), whose toolchain is
  leanprover/lean4:v4.34.0-rc1 and whose Mathlib/LiCriterion dependency chain was
  NOT built in the routes-node-proofs worktree (no v4.34 Mathlib olean available;
  the host disk was at capacity, so a cold island build was not run). The
  ALGEBRAIC REARRANGEMENT proof below was kernel-checked on the v4.32.0 toolchain
  against a byte-for-byte mirror of `rect_explicit_formula_bragg`'s signature
  (an `axiom` with the identical statement, using the real MMDefs braggTerm /
  RHInBoxAnalytic.zeroFinset vocabulary): the tactic block closes with the source
  theorem as its ONLY non-standard axiom, confirming it composes. When built in
  the li-positivity island (CI or a full-island worktree) the `import`s below make
  `rect_explicit_formula_bragg` a proved theorem, not an axiom, and this module's
  closure is [propext, Classical.choice, Quot.sound]. conjecture1_proved = False.

  Provenance of reused lemma: rect_explicit_formula_bragg -- verbatim source
  RvMBraggBridge.lean:123 (li_positivity island, rh/million-turing). braggTerm --
  RvMDiffractionCore. RHInBoxAnalytic.zeroFinset -- RvMRHInBox.
-/
import Mathlib
import RvMBraggBridge
import RvMRHInBox

open Complex MeasureTheory Real DiffractionCore
open scoped Topology

theorem rect_trace_reading
    (sigma0 sigma1 T0 T1 : ℝ) (hsig : sigma0 ≤ sigma1) (hT : T0 ≤ T1) (hσ1 : 1 < sigma1)
    (c : ℂ) (R : ℝ)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R)
    (hnzb : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T0 : ℂ) * I) ≠ 0)
    (hnzt : ∀ x ∈ Set.uIcc sigma0 sigma1, riemannZeta (↑x + (T1 : ℂ) * I) ≠ 0)
    (hnzl : ∀ y ∈ Set.uIcc T0 T1, riemannZeta ((sigma0 : ℂ) + ↑y * I) ≠ 0)
    (hins : ∀ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
      sigma0 < ρ.re ∧ ρ.re < sigma1 ∧ T0 < ρ.im ∧ ρ.im < T1) :
    ∑ ρ ∈ RHInBoxAnalytic.zeroFinset c R hs1,
        ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ)
      = (1 / (2 * ↑π * I)) *
        ((∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T0 : ℂ) * I))
          - (∫ x in sigma0..sigma1, logDeriv riemannZeta (↑x + (T1 : ℂ) * I))
          - I • (∑' n : ℕ, braggTerm sigma1 T0 T1 n)
          - I • (∫ y in T0..T1, logDeriv riemannZeta ((sigma0 : ℂ) + ↑y * I))) := by
  have hbridge := rect_explicit_formula_bragg sigma0 sigma1 T0 T1 hsig hT hσ1 c R
    hbox_ball hs1 hnzb hnzt hnzl hins
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    simp [h2, hp, hI]
  -- from  (2πi)·S = RHS  derive  S = (1/(2πi))·RHS
  rw [← hbridge, one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
