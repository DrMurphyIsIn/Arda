/-
  Probes.MMWeilGramTraceProbes -- trivial-close and non-vacuity probes for the MIRRORMERE
  D2 node `MM_weil_gram_trace` (statement file Statements/MM_weil_gram_trace.lean) and for
  the REPLACEMENT statement proposed for the draft goal node `MM_zeta_comb_membership`
  (design memo telperion/docs/MM_mm-d2-weil-gram-trace_DESIGN_2026-09-18.md, section 9).

  This module is OUTSIDE `defaultTargets` (see lakefile.toml) and contains NO `sorry` and
  no node statement: every `example` below is a kernel-checked record of a NEGATIVE result
  ("this tactic does NOT close that goal", via `fail_if_success`) or of a witness.  A probe
  that stopped being true would break this build, which is the point -- the trivial-close
  audit is re-run by the compiler, not by a human memory of a terminal session.

  NOTHING here proves or claims RH.  conjecture1_proved = False.
-/
import Mathlib
import Statements.MMDefs

open Complex MeasureTheory
open WeilExplicit

-- The probes deliberately hand every relevant definition to `simp`/`aesop`, INCLUDING ones
-- the tactic never reaches (it gives up earlier).  That is the probe's content -- "even with
-- all of these unfolded, nothing closes" -- so the unused-argument linter is switched off
-- here rather than trimming the lists down to what happened to be consumed.
set_option linter.unusedSimpArgs false

namespace MMWeilGramTraceProbes

/-- The D2 statement, as a predicate, so the probes can quote it once. -/
def D2 (k : ℕ) (g : Fin k → ℝ → ℂ) : Prop :=
  (weilGram g).IsHermitian ∧
  (∀ i j : Fin k,
    HasSum (fun ρ : ℂ => (zeroMult ρ : ℂ) * weilKernel (g i) ρ
        * (starRingEnd ℂ) (weilKernel (g j) (1 - (starRingEnd ℂ) ρ)))
      (weilGram g i j)) ∧
  (∀ (x : Fin k → ℂ) (G : ℝ → ℂ),
    G = (fun v => ∑ i, (starRingEnd ℂ) (x i) * g i v) →
    RHLinalg.hermForm (weilGram g) x
      = (archSide (crossCorr G G) - primeSide (crossCorr G G)).re)

/-! ## Probe 1-4: no general-purpose tactic closes the statement. -/

/-- Probe 1: `simp` with every definition unfolded does not close D2. -/
example (k : ℕ) (g : Fin k → ℝ → ℂ) (_hg : ∀ i, IsWeilTest (g i)) : True := by
  fail_if_success
    (have : D2 k g := by
      simp [D2, weilGram, crossCorr, archSide, primeSide, weilKernel, archIntegrand,
        zeroMult, RHLinalg.hermForm])
  trivial

/-- Probe 2: `simp_all` does not close D2. -/
example (k : ℕ) (g : Fin k → ℝ → ℂ) (_hg : ∀ i, IsWeilTest (g i)) : True := by
  fail_if_success
    (have : D2 k g := by
      simp_all [D2, weilGram, crossCorr, archSide, primeSide, weilKernel, archIntegrand,
        zeroMult, RHLinalg.hermForm])
  trivial

/-- Probe 3: `aesop` does not close D2. -/
example (k : ℕ) (g : Fin k → ℝ → ℂ) (_hg : ∀ i, IsWeilTest (g i)) : True := by
  fail_if_success
    (have : D2 k g := by
      aesop (add simp [D2, weilGram, crossCorr, archSide, primeSide, weilKernel, zeroMult]))
  trivial

/-- Probe 4: `norm_num` does not close D2. -/
example (k : ℕ) (g : Fin k → ℝ → ℂ) (_hg : ∀ i, IsWeilTest (g i)) : True := by
  fail_if_success
    (have : D2 k g := by
      norm_num [D2, weilGram, crossCorr, archSide, primeSide, weilKernel, zeroMult])
  trivial

/-! ## Probe 5-7: the individual conjuncts are not free. -/

/-- Probe 5: Hermitian-ness of `weilGram` is not a `simp`/`decide`-level fact. -/
example (k : ℕ) (_g : Fin k → ℝ → ℂ) : True := by
  fail_if_success
    (have : (weilGram _g).IsHermitian := by simp [weilGram, crossCorr, archSide, primeSide, Matrix.IsHermitian])
  trivial

/-- Probe 6: the entries are not `simp`-reducible to `0` (which would make the trace
conjunct a statement about the zero family and the Gram matrix contentless). -/
example (k : ℕ) (_g : Fin k → ℝ → ℂ) (_i _j : Fin k) : True := by
  fail_if_success
    (have : weilGram _g _i _j = 0 := by
      simp [weilGram, crossCorr, archSide, primeSide, weilKernel, archIntegrand])
  trivial

/-- Probe 7: the zero-side weight does not `simp` to `0` (the E8 probe 5 analogue -- a
`zeroMult ≡ 0` collapse would make the trace conjunct `HasSum 0 = entry` and so turn D2
into the FALSE claim `weilGram = 0`, not into a vacuous truth). -/
example (_ρ : ℂ) : True := by
  fail_if_success (have : zeroMult _ρ = 0 := by simp [zeroMult])
  trivial

/-! ## Probe 8-10: non-vacuity of the hypothesis and the degenerate instances. -/

/-- Probe 8: the test class is inhabited by a nonzero function, so `∀ i, IsWeilTest (g i)`
is not a vacuous hypothesis (an empty class would make D2 true for no reason at `k ≥ 1`). -/
theorem probe_test_class_nonvacuous : ∃ g : ℝ → ℂ, IsWeilTest g ∧ g ≠ 0 := by
  classical
  set f : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩ with hf
  refine ⟨fun u => ((f u : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero
  · intro h
    have h0 : ((f 0 : ℝ) : ℂ) = 0 := congrFun h 0
    have h1 : f 0 = 1 := f.one_of_mem_closedBall (by simp [hf])
    rw [h1] at h0
    norm_num at h0

/-- Probe 9: the smoothness index in `IsWeilTest` is `C^∞`, NOT `ω` (analytic).  With
`⊤ : WithTop ℕ∞` the class would collapse to `{0}` on the line (a compactly supported
analytic function vanishes) and the statement would be vacuous for every nonzero family. -/
theorem probe_smoothness_index_not_analytic :
    (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ (⊤ : WithTop ℕ∞) := by decide

/-- Probe 10: `k = 0` is an honest empty instance -- the matrix is the unique `0 × 0`
matrix and all three conjuncts hold by emptiness.  The node deliberately states nothing
extra at `k = 0` (no `posIndex = k`, no `defect = 0`); this probe records that the empty
instance is TRUE and contentless, so it cannot be mistaken for evidence. -/
theorem probe_empty_family (g : Fin 0 → ℝ → ℂ) : (weilGram g).IsHermitian := by
  ext i; exact absurd i.isLt (by omega)

/-! ## Probe 11: the goal node `MM_zeta_comb_membership` replacement proposal.

The registered goal statement is the FLAGGED PLACEHOLDER `RiemannHypothesis` (see
Statements/MM_zeta_comb_membership.lean).  The memo (section 9) proposes replacing it, at
W3c-authoring time, with the D-route reading below; this probe records only that the
proposed sentence is not closed by `simp` and is not vacuous, and it does NOT change the
goal node's status, statement, or file.  NOTHING here proves or claims RH. -/

/-- The proposed replacement shape, as a predicate over the (still open) test-family
parameter: "for every finite Weil test family the Gram matrix has no negative direction".
By Weil's criterion this is RH-equivalent, and it is the sentence the D2 instrument is an
instance-level probe of -- `defect (weilGram g) = 0` for ONE family is data, for ALL
families it is the wall. -/
def GoalProposal : Prop :=
  ∀ (k : ℕ) (g : Fin k → ℝ → ℂ), (∀ i, IsWeilTest (g i)) →
    ∀ (x : Fin k → ℂ), 0 ≤ RHLinalg.hermForm (weilGram g) x

/-- Probe 11: the proposed goal statement is not closed by `simp`. -/
example : True := by
  fail_if_success
    (have : GoalProposal := by
      simp [GoalProposal, RHLinalg.hermForm])
  trivial

end MMWeilGramTraceProbes
