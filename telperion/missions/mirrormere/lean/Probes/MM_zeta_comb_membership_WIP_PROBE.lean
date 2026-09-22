/-
  MM_zeta_comb_membership -- W3c GOAL PROBE FILE (WIP; NOT a registry statement, NOT built by
  the Statements default target, NOT covered by any axiom guard).

  This file records the trivial-close probe battery and the vocabulary content checks run while
  authoring the W3c concrete goal statement on 2026-09-18 (design memo
  telperion/docs/MM_w3c_goal_weil_membership_DESIGN_2026-09-18.md).  It is compiled by hand with

      cd telperion/missions/mirrormere/lean && lake env lean Probes/MM_zeta_comb_membership_WIP_PROBE.lean

  and is deliberately OUTSIDE `Statements.lean` (the lake default target), so nothing here can
  reach a registry build or a grant gate.

  The goal node itself is `Statements/MM_zeta_comb_membership.lean`: RH-EQUIVALENT (Weil 1952;
  Bombieri 2000 on C_c^infinity), kind = goal, status = draft permanently, never attempted, its
  decomposition refused (RH_ROUTES_ROADMAP A5).  NOTHING in this file proves, approaches or
  claims RH.  conjecture1_proved = False.

  WHAT IS HERE
    section 1  the goal statement restated as `MMGoal`, with `sorry` -- the WIP marker, so the
               battery below has something to attack.  It is NOT a theorem and is NOT exported.
    section 2  the four trivial-close probes (simp / simp_all / aesop / norm_num + positivity).
               Each is recorded as a COMMENT with the verbatim compiler output; leaving them
               live would make this file fail to compile, which is the point of a probe.
    section 3  the checks that SUCCEED, and are therefore live code here: the class is
               non-vacuous, the smoothness index is not the analytic one, the degenerate witness
               g = 0 gives a contentless 0, and two genuine unconditional facts about the
               AUTHORED vocabulary (`autocorr` is Hermitian, and its value at 0 is >= 0).
    section 4  the instantiation of the emitted Weil-form faces (telperion emitter kind
               `weil_form_enclosure`, examples/weil_form_enclosure/lean/WeilFormEnclosure.lean)
               at this registry's vocabulary -- with the analytic evaluation and Weil's
               criterion carried as EXPLICIT, UNDISCHARGED hypotheses.
-/
import Mathlib
import Statements.MMDefs

open WeilExplicit MeasureTheory

namespace MMWeilProbe

/- ===== 1. the goal statement (WIP; the registry copy is the authoritative one) ===== -/

/-- The W3c membership goal, restated here so the probe battery has a target.  RH-equivalent;
    NEVER attempted.  `sorry` is the honest WIP marker -- this file is outside every build
    target and every axiom guard. -/
theorem mm_goal_wip :
    ∀ g : ℝ → ℂ, IsWeilTest g → 0 ≤ (weilForm (autocorr g)).re := by
  sorry

/- ===== 2. trivial-close probes: NONE of these closes the goal =====

  Run 2026-09-18 against this island (leanprover/lean4:v4.32.0, Mathlib v4.32.0), each as a
  standalone file; verbatim results:

  probe 1  `simp [MMGoal, IsWeilTest, weilForm, archSide, primeSide, autocorr, weilKernel,
            archIntegrand]`
             -> error: unsolved goals; the goal is displayed fully unfolded, with the prime
                tsum on the left and the two Bochner integrals plus the digamma integral on
                the right.
  probe 2  `simp_all [same set]`                       -> error: unsolved goals (same display)
  probe 3  `aesop (add simp [same set])`               -> warning: aesop: failed to prove the
                                                          goal after exhaustive search;
                                                          error: unsolved goals
  probe 4  `intro g hg; norm_num [weilForm, archSide, primeSide, autocorr, weilKernel,
            archIntegrand]`                            -> error: unsolved goals
  probe 5  `intro g hg; positivity`                    -> error: failed to prove
                                                          positivity/nonnegativity/nonzeroness
  probe 6  `example (f : ℝ → ℂ) : weilForm f = 0 := by simp [...]`
                                                       -> error: unsolved goals (the right side
                                                          is NOT simp-trivial: the statement is
                                                          not the sentence `0 ≤ 0`)
  probe 7  `example (g : ℝ → ℂ) : autocorr g = 0 := by simp [autocorr]`
                                                       -> error: `simp` made no progress (the
                                                          autocorrelation is not junk-zero)

  Nothing closed the statement, and the statement was not changed by the battery.
-/

/- ===== 3. checks that SUCCEED (live code) ===== -/

/-- Non-vacuity of the test class: it contains a nonzero function, so the goal's `∀` is not
    vacuously true.  (A smooth bump; `ContDiffBump` supplies both clauses.) -/
theorem test_class_nonvacuous : ∃ g : ℝ → ℂ, IsWeilTest g ∧ g ≠ 0 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨fun x => ((f x : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  · intro h
    have h0 : f 0 = 1 := f.one_of_mem_closedBall (by simp [f.rIn_pos.le])
    have hx := congrFun h 0
    rw [h0] at hx
    simp at hx

/-- The smoothness index of `IsWeilTest` is `C^∞`, NOT the analytic index: writing
    `ContDiff ℝ ⊤` would mean analytic and, with compact support, collapse the class to `{0}`,
    making the goal vacuous. -/
theorem smoothness_index_is_not_analytic : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ⊤ := by decide

/-- The degenerate witness: `g = 0` satisfies the goal's conclusion, and contentlessly so --
    every term of the functional vanishes.  A statement true ONLY here would be worthless; the
    numeric read-back (design memo section 6) shows the value is `≈ 1.5708` at a test function
    centred on the first zeta ordinate. -/
theorem degenerate_witness_is_contentless : (weilForm (autocorr (0 : ℝ → ℂ))).re = 0 := by
  simp [weilForm, autocorr, archSide, primeSide, weilKernel, archIntegrand]

/-- AUTHORED-vocabulary content check: `autocorr g` is HERMITIAN, `f(-u) = conj (f u)`.  This is
    what makes the Weil form real and is the reason the goal takes `.re` rather than proving an
    imaginary-part lemma.  Unconditional, sorry-free. -/
theorem autocorr_hermitian (g : ℝ → ℂ) (u : ℝ) :
    autocorr g (-u) = (starRingEnd ℂ) (autocorr g u) := by
  simp only [autocorr, ← integral_conj, map_mul, RingHomCompTriple.comp_apply,
    RingHom.id_apply]
  rw [← integral_add_right_eq_self (fun v : ℝ => (starRingEnd ℂ) (g v) * g (v - u)) u]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [sub_neg_eq_add, add_sub_cancel_right]
  ring

/-- AUTHORED-vocabulary content check: `autocorr g 0 = ∫ ‖g‖²  ≥ 0`, the positive-definiteness
    seed of the Weil-criterion shape.  Unconditional, sorry-free. -/
theorem autocorr_zero_nonneg (g : ℝ → ℂ) : 0 ≤ (autocorr g 0).re := by
  have h : ∀ v : ℝ, g v * (starRingEnd ℂ) (g v) = ((Complex.normSq (g v) : ℝ) : ℂ) :=
    fun v => Complex.mul_conj (g v)
  simp only [autocorr, sub_zero]
  rw [integral_congr_ae (.of_forall h), integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun v => Complex.normSq_nonneg (g v)

/- ===== 4. the emitted Weil-form faces, instantiated at this vocabulary =====

  `telperion/examples/weil_form_enclosure/lean/WeilFormEnclosure.lean` (emitter kind
  `weil_form_enclosure`, backend `telperion.weil_gauss`) certifies rational enclosures of
  `W = Re (weilForm (autocorr g))` at explicit Gaussian test functions, together with two
  abstract faces.  Instantiated here, both faces read:

    * a certified positive value at ONE g gives the goal's conclusion AT THAT g -- and the
      quantifier over the class remains untouched (roadmap section 1: no finite family of test
      functions approaches a wall form);
    * a certified strictly NEGATIVE value at an admissible g would refute RH, GIVEN Weil's
      criterion in the forward direction (`hcrit`), which is classical, is not in Mathlib, and
      is NOT proved here.

  `heval` -- that the certified rational number IS this functional's value at this g -- is the
  analytic evaluation step; it is UNDISCHARGED and is the content of the D2/D3 finite faces.
-/

/-- One certified positive enclosure gives the goal's conclusion at that single test function.
    The universal statement is the wall; this is one point of it. -/
theorem instance_of_enclosure (g : ℝ → ℂ) (lo W : ℝ)
    (heval : (weilForm (autocorr g)).re = W) (hpos : 0 < lo) (hlo : lo ≤ W) :
    0 ≤ (weilForm (autocorr g)).re := by
  rw [heval]
  exact le_trans hpos.le hlo

/-- The falsifiability face at this vocabulary: a certified strictly negative Weil form at an
    admissible test function refutes RH, through the UNDISCHARGED classical criterion `hcrit`
    (Weil 1952; Bombieri 2000).  Not expected to fire: every certified instance is positive and
    agrees with the independently computed zero-side sum to 18 digits. -/
theorem neg_enclosure_refutes_rh (g : ℝ → ℂ) (W : ℝ)
    (hcrit : RiemannHypothesis → ∀ f : ℝ → ℂ, IsWeilTest f → 0 ≤ (weilForm (autocorr f)).re)
    (hg : IsWeilTest g) (heval : (weilForm (autocorr g)).re = W) (hneg : W < 0) :
    ¬ RiemannHypothesis := by
  intro hrh
  exact absurd (heval ▸ hcrit hrh g hg) (not_le.mpr hneg)

end MMWeilProbe
