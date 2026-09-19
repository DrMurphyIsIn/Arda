/-  RecurrenceDeficit -- MIRRORMERE node `MM_recurrence_deficit_eq_excess` (Routes-roadmap E4a).

    THE DICTIONARY ROW, Face 4 (Bagchi recurrence) <-> Face 1 (Weil/Bragg defect).  QC_RECURRENCE
    section 2 row (a) derives, for a synthetic off-line pair at displacement `delta`, the two
    one-sided clearances `g+(delta) = e^delta - 1` (outer mirror factor) and
    `g-(delta) = 1 - e^(-delta)` (inner transported-zero factor), and identifies their PRODUCT --
    the two-sided clearance a recurrence shift must bridge -- as the recurrence deficit

        recurrenceDeficit delta = (e^delta - 1) * (1 - e^(-delta)) .

    This file proves that this deficit is, at the certified displacement `delta = 1/10` of the
    `BraggDefect` configuration (`beta = 3/5`, `gamma0 = 50`), EXACTLY the Bragg amplification
    `excess = Aoff - Aon = e^(1/10) + e^(-1/10) - 2`, and that it is strictly positive at every
    positive displacement.  The two instruments -- the dynamical clearance and the diffraction
    amplitude excess -- read the same off-line signal off the same number.

    HONEST SCOPE.  The content is a ONE-RELATION ring identity in `Real.exp` (the relation being
    `e^delta * e^(-delta) = 1`) plus a two-factor positivity.  It is a DICTIONARY ROW, not an
    analytic theorem: it says the Face-4 and Face-1 bookkeeping agree, and nothing about zeta.
    Nothing here is conditional on, nor evidence for, the Riemann Hypothesis -- the memo is
    explicit that certifying one recurrence instance is not progress toward RH, and that the
    UNIFORM Bagchi recurrence IS RH and is untouched.  conjecture1_proved = False.

    VOCABULARY.  `recurrenceDeficit` is AUTHORED in the registry's vocabulary mirror
    `telperion/missions/mirrormere/lean/Statements/MMDefs.lean` (lines 61-62); it is mirrored here
    BYTE-IDENTICALLY, in the same namespace `Quasicrystal`, exactly as the `rvm_bridge` E6Bridge
    modules mirror their MMDefs vocabulary.  `excess` is verbatim island vocabulary from
    `BraggDefect.lean` (line 60).  Any drift between this def and MMDefs is a grant-gate failure.

    CERTIFICATE PROVENANCE.  The algebraic core is the emitted Telperion certificate
    `ExpLaurentDeficit.expLaurent_recurrence_deficit` (kind `exp_laurent_identity`, generator
    `telperion/examples/exp_laurent_deficit/generate.py`): the identity is certified in sympy as an
    exact reduction modulo the single relation `y * z = 1` with the LOAD-BEARING cofactor `-1`, and
    the emitted Lean discharges it by `linear_combination` against that cofactor.  This file
    consumes the emitted general-delta identity and specializes it.
-/
import Mathlib
import BraggDefect
import ExpLaurentDeficit

namespace Quasicrystal

/-- The recurrence deficit of an off-line displacement `delta` (QC_RECURRENCE section 4.2 / W3d).
MIRROR of `telperion/missions/mirrormere/lean/Statements/MMDefs.lean` lines 61-62, byte-identical;
the registry's vocabulary is authoritative. -/
noncomputable def recurrenceDeficit (δ : ℝ) : ℝ :=
  (Real.exp δ - 1) * (1 - Real.exp (-δ))

open Quasicrystal BraggDefect

/-- **`recurrence_deficit_eq_excess`** -- the MIRRORMERE node `MM_recurrence_deficit_eq_excess`,
stated verbatim.  At the certified displacement `delta = 1/10` the recurrence deficit equals the
Bragg amplification excess `Aoff - Aon`, and the deficit is strictly positive at every positive
displacement.  Unconditional; the exp-Laurent identity is the emitted Telperion certificate
`ExpLaurentDeficit.expLaurent_recurrence_deficit`.  conjecture1_proved = False. -/
theorem recurrence_deficit_eq_excess :
    recurrenceDeficit (1 / 10) = excess ∧
    ∀ δ : ℝ, 0 < δ → 0 < recurrenceDeficit δ := by
  refine ⟨?_, ?_⟩
  · -- the exp-Laurent row: (e^d - 1)(1 - e^(-d)) = e^d + e^(-d) - 2, at d = 1/10
    unfold recurrenceDeficit excess Aoff Aon
    exact ExpLaurentDeficit.expLaurent_recurrence_deficit (1 / 10)
  · -- both clearances are strictly positive at a positive displacement
    intro δ hδ
    unfold recurrenceDeficit
    exact mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hδ))
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

/-- Companion (NOT a registry node; QC_RECURRENCE section 4 item 2 names it): the SQUARED
recurrence deficit at `delta = 1/10` is the magnitude of the Bragg defect functional.  This is the
"second-order (Weil-energy) form" of the same dictionary row -- one power of the linear clearance
for each of the two evaluation-vector legs of the pair block -- and it is immediate from the
identity above plus `defectFunctional d = -(d^2)`. -/
theorem recurrence_deficit_sq_eq_abs_defect :
    recurrenceDeficit (1 / 10) ^ 2 = |defectFunctional excess| := by
  have h := recurrence_deficit_eq_excess.1
  have hpos : (0 : ℝ) ≤ excess ^ 2 := sq_nonneg _
  rw [h, defectFunctional, abs_neg, abs_of_nonneg hpos]

end Quasicrystal
