/-
  AxiomGuard — CI kernel-axiom guard for the Brualdi–Goldwasser formalization.

  This file is NOT part of the `R3Cert` library (it is a top-level module, not
  root-imported and not matched by any lakefile glob). CI runs it explicitly with

      lake env lean AxiomGuard.lean

  AFTER `lake build`, and fails the build if any listed `#print axioms` output
  mentions `sorryAx` — i.e. if a guarded theorem secretly depends on a `sorry`.

  `#print axioms` is the authoritative, false-positive-free detector: a grep for
  the string `sorry` over `.lean` sources cannot distinguish a real proof gap from
  docstring prose like "no `sorry`", but the kernel's axiom trace can.

  A clean proof reports exactly `[propext, Classical.choice, Quot.sound]`.

  Anchors (the theorems whose integrity actually matters):
    * R3Cert.Step3.conjecture1_of_layers  — the R7' top capstone (conditional on
      the two open layers Hnorm/Hdom); guarding it guards its entire dependency cone.
    * R3Cert.phi_le_one                    — the Φ ≤ 1 analytic crux.
    * R3Cert.CappedJointConfig.gstep_le_one_achievable — the g-step / master ineq crux.

  Additive SUBACTION ceiling (2026-09-03, branch bg/scl-on-main) — the current live
  line for the classical branch ceiling `∀ b, bell b ≤ 0`, after the multiplicative
  capped-product step `Le1Step` was REFUTED (BG_LE1STEP_REFUTED_20260902.md).  The
  ceiling reduces to the single obligation `IsSubaction ρwit`; guarding the reduction
  chain + each discharged per-cell family member keeps the "kernel-green, axiom-clean"
  claim machine-enforced as the family grows.
    * R3Cert.BGSCL.ceiling_of_subaction — the additive bridge (ρ≥0 ∧ IsSubaction ρ → ceiling).
    * R3Cert.BGSCL.ρwit_nonneg          — the witness nonnegativity leg (discharged).
    * R3Cert.BGSCL.ceiling_of_witness   — ceiling ⟸ IsSubaction ρwit (the single obligation).
    * R3Cert.BGSCL.subaction_*          — the discharged cells of the IsSubaction ρwit family.
-/
import R3Cert.R47TopCapstone
import R3Cert.PotentialFinal
import R3Cert.CappedJointClosure
import R3Cert.BGSCLSubaction
import R3Cert.BGSCLSubactionDeg3
import R3Cert.BGSCLSubactionDeg3Mid
import R3Cert.BGSCLSubactionD4
import R3Cert.BGSCLSubactionTail
import R3Cert.BGSCLSubactionTailDecouple
import R3Cert.BGSCLSubactionD4Cells
import R3Cert.BGSCLSubactionTailWrap
import R3Cert.BGSCLSubactionDispatch
import R3Cert.BGSCLSCLUncond
import R3Cert.BGSCLAsymptotic
import R3Cert.BGSCLSubactionStrict
import R3Cert.BGSCLHnormPort
import R3Cert.BGSCLObligationA
import R3Cert.BGSCLHdom
import R3Cert.R47HdomBridge
import R3Cert.BGSCLRealizationBridge
import R3Cert.BGSCLObligationB
import R3Cert.BGSCLRealOblACaseA
import R3Cert.BGSCLRealOblACaseAIdentity
import R3Cert.BGSCLRealOblACaseABook
import R3Cert.BGSCLRealOblACaseALift
import R3Cert.BGSCLJointDescent2Step
import R3Cert.BGSCLRealOblBSymBase

#print axioms R3Cert.Step3.conjecture1_of_layers
#print axioms R3Cert.phi_le_one
#print axioms R3Cert.CappedJointConfig.gstep_le_one_achievable

-- RealObligationA Case-A (leaf-path-extension, 92%) Aobj-monotonicity certificate (the F2 closed form).
#print axioms R3Cert.BGSCL.f2_numerator_nonneg
#print axioms R3Cert.BGSCL.f2_aobj_increment_nonneg
-- ...and the STRUCTURAL cavity-model identity making it load-bearing (ΔAobj EQUALS the closed form; monotone).
#print axioms R3Cert.Step3.f2_increment_identity
#print axioms R3Cert.Step3.f2_aobj_monotone
-- Case-A bookkeeping: size preserved + the piece-flip strDefect mechanism (npCount drops by 1 in context).
#print axioms R3Cert.Step3.usize_flp_move_eq
#print axioms R3Cert.Step3.isPiece_flpStem
#print axioms R3Cert.Step3.isPiece_flp_before
#print axioms R3Cert.Step3.npCount_flp_flip

-- Additive SUBACTION reduction chain (the ceiling now rests on `IsSubaction ρwit`).
#print axioms R3Cert.BGSCL.ceiling_of_subaction
#print axioms R3Cert.BGSCL.ρwit_nonneg
#print axioms R3Cert.BGSCL.ceiling_of_witness

-- Tail (deg≥5) DECOUPLE backbone: reduces a mixed-degree tail cell to per-child bound + B(S0)≥0
-- (the counts-exchange dissolution; no discrete convexity).
#print axioms R3Cert.BGSCL.sum_rhowit_ge
#print axioms R3Cert.BGSCL.ρwit_node_high
#print axioms R3Cert.BGSCL.tail_decouple
-- First CLOSED mixed-config tail cell: the d=6 tie (arbitrary children), via tail_decouple.
#print axioms R3Cert.BGSCL.phi_lb_d6
#print axioms R3Cert.BGSCL.subaction_tail_d6
-- The INFINITE tail closed: deg-5 regime, ALL nodes of degree >= 65, arbitrary children.
#print axioms R3Cert.BGSCL.cherry_anchor_ge
#print axioms R3Cert.BGSCL.phi_lb_general
#print axioms R3Cert.BGSCL.subaction_tail_deg5
-- The deg-4 range regime d in [10,61]: tight anchor + per-child min + tail_all_deg4.
#print axioms R3Cert.BGSCL.cherry_anchor_ge_tight
#print axioms R3Cert.BGSCL.phi_lb_deg4
#print axioms R3Cert.BGSCL.subaction_tail_deg4

-- Discharged cells of the `IsSubaction ρwit` per-node family.
#print axioms R3Cert.BGSCL.subaction_nil
#print axioms R3Cert.BGSCL.subaction_cherry
#print axioms R3Cert.BGSCL.subaction_deg2_deg2child
#print axioms R3Cert.BGSCL.subaction_deg2_highchild
#print axioms R3Cert.BGSCL.subaction_broom_d3
#print axioms R3Cert.BGSCL.subaction_deg3_highchildren

-- Degree-3 hub family completed (2026-09-03): the two-deg-2, leaf/deg-2, leaf/deg≥3 profiles,
-- and the redesigned two-slope (deg-2/deg≥3) cell + its new tight_hi atom `log2_sub3fstar`.
#print axioms R3Cert.BGSCL.subaction_deg3_deg2children
#print axioms R3Cert.BGSCL.subaction_deg3_leaf_deg2
#print axioms R3Cert.BGSCL.subaction_deg3_leaf_high
#print axioms R3Cert.BGSCL.log2_sub3fstar

-- Degree-4 enclosure atoms (2026-09-03): the tangent-route generator + representatives spanning the
-- structural cases (log(3/2)-fold present/absent, bound sign).  All 35 `d4_*` go through `tangent_atom`.
#print axioms R3Cert.BGSCL.tangent_atom
#print axioms R3Cert.BGSCL.d4_222
#print axioms R3Cert.BGSCL.d4_333
#print axioms R3Cert.BGSCL.d4_455

-- The deg≥5 tail crux family + the 27·23 = 621 tie identity (2026-09-03).
#print axioms R3Cert.BGSCL.tail_all_deg4
#print axioms R3Cert.BGSCL.tail_all_deg3
#print axioms R3Cert.BGSCL.tail_all_deg2
#print axioms R3Cert.BGSCL.tail_deg2_sum
#print axioms R3Cert.BGSCL.henc_deg2_qp7
#print axioms R3Cert.BGSCL.henc_deg2_q7
#print axioms R3Cert.BGSCL.tie_identity_d6
#print axioms R3Cert.BGSCL.subaction_tail_tie_d6
#print axioms R3Cert.BGSCL.subaction_deg3_deg2_high

-- ===========================================================================================
-- CEILING CLOSED (2026-09-04): `IsSubaction ρwit` fully assembled ⇒ `bell b ≤ 0` for all b.
-- Degree-4 node cells (all 35, wiring the `d4_*` atoms), the 7 tail stragglers + gap-free
-- `tail_wrapper`, the permutation-invariance bridge, the top-level degree dispatch, and the
-- `bg_ceiling` capstone.  These make the classical-branch ceiling machine-checked & axiom-clean.
-- ===========================================================================================
-- Permutation invariance of the SUB predicate (canonicalizes ordered cells to arbitrary orders).
#print axioms R3Cert.BGSCL.subaction_perm
-- Tail stragglers + the unified gap-free tail wrapper (∀ cs, 4 ≤ cs.length → SUB cs).
#print axioms R3Cert.BGSCL.cherry_anchor_le_tight
#print axioms R3Cert.BGSCL.subaction_tail_d9
#print axioms R3Cert.BGSCL.tail_wrapper
-- Degree-4 node cells: representatives across the class spectrum + the canonicalizing dispatchers.
#print axioms R3Cert.BGSCL.subaction_deg4_LLL
#print axioms R3Cert.BGSCL.subaction_deg4_HHH
#print axioms R3Cert.BGSCL.subaction_deg4_L2H
#print axioms R3Cert.BGSCL.subaction_deg4_canon
#print axioms R3Cert.BGSCL.subaction_deg4
-- The single obligation and the capstone: the ceiling now holds unconditionally.
#print axioms R3Cert.BGSCL.isSubaction_ρwit
#print axioms R3Cert.BGSCL.bg_ceiling
-- SCL now UNCONDITIONAL: bg_ceiling fed into scl_of_ceiling discharges HYPOTHESIS(b).
#print axioms R3Cert.BGSCL.scl_holds_uncond
-- Asymptotic BG upper bound F(T) ≤ F* (direct corollary of bg_ceiling).
#print axioms R3Cert.BGSCL.bg_asymptotic_bound
#print axioms R3Cert.BGSCL.btotal_le_rpow
-- Strict master inequality: bell b < 0 off the tie set (unconditional for deg≤4).
#print axioms R3Cert.BGSCL.master_ineq_strict
#print axioms R3Cert.BGSCL.bell_eq_zero_imp_tie
-- Hnorm scoped porting: the straightening context-lift layer (Obligation-A-gated).
#print axioms R3Cert.Step3.straightStep_sized_lift
-- ===========================================================================================
-- WAVE 2 (2026-09-04): conjecture1 research walls. Negative result + reductions to crisp obligations.
-- ===========================================================================================
-- Obligation A is FALSE: kernel-checked counterexamples (pushInto is the wrong, degree-concentrating move).
#print axioms R3Cert.Step3.deephub_obligationA_false
#print axioms R3Cert.Step3.direct_obligationA_false
-- Strict inequality strengthened: bell b < 0 UNCONDITIONALLY off degree-6 hubs; tie ⟹ bcc = 5.
#print axioms R3Cert.BGSCL.master_ineq_strict_off_deg6
#print axioms R3Cert.BGSCL.bcc_eq_five_of_bell_eq_zero
#print axioms R3Cert.BGSCL.strictRootCell_tail
-- Hdom reduced to ONE crisp size-normalized obligation (SharpRateNF); conjecture1 modulo Hnorm+SharpRateNF.
#print axioms R3Cert.Step3.Hdom_of_sharpRate
#print axioms R3Cert.Step3.conjecture1_of_Hnorm_sharpRate
-- Gap-2 realization bridge (loose rate): the analytic ceiling realized on the real permanent ratio.
#print axioms R3Cert.Step3.perm_ratio_le_rate
#print axioms R3Cert.Step3.perm_ratio_backbone_le_rate
-- Obligation B seam: Aobj invariant under a bare address-graph iso (degree side-condition discharged).
#print axioms R3Cert.Step3.Aobj_root_invariant_of_iso
-- Case-B SYMMETRIC BASE CASE (2026-09-04): the two-k-star straightening is Aobj-NEUTRAL, parametric in k.
-- Both sides = (4k+2)/(k+1) exactly; kernel-proves dAobj = 0 for every k ≥ 1.
#print axioms R3Cert.Step3.Ztot_dtSub_kstar
#print axioms R3Cert.Step3.Aobj_before
#print axioms R3Cert.Step3.Aobj_afterB
#print axioms R3Cert.Step3.symmetric_star_neutral
#print axioms R3Cert.Step3.symmetric_star_monotone

-- Case-A DEGREE-CHANGING Aobj CONTEXT-LIFT (2026-09-04): the sole open residual of Case A, closed.
-- The leaf-path-extension acting at a NON-root child (retaining its other children `crest`) is
-- Aobj-monotone in ANY sibling context.  The engine is the any-position degree-changing child
-- replacement; the two child-cavity gains (Ztot up, weighted-Zopen up as udeg drops) are the local
-- certificates.  The literal Book `Prop` (wholesale replacement, crest dropped) is FALSE — witnessed.
#print axioms R3Cert.Step3.Aobj_child_replace_le_deg
#print axioms R3Cert.Step3.Ztot_dtSub_flp_child_le
#print axioms R3Cert.Step3.Zopen_weighted_flp_child_le
#print axioms R3Cert.Step3.aobj_flp_context_lift_crest
#print axioms R3Cert.Step3.flp_context_lift_book_false

-- Straightening-move existence SHARP BOUNDARY (2026-09-04): the triple-3-star (unique n=13 obstruction
-- to the single-SPR/strict-Aobj STRENGTHENING) exact invariants + a StraightStep_sized WITNESS proving
-- the actual Lean obligation StraightProgress_sized HOLDS there.  Does NOT refute the obligation.
#print axioms R3Cert.Step3.Aobj_tripleStar
#print axioms R3Cert.Step3.strDefect_tripleStar
#print axioms R3Cert.Step3.usize_tripleStar
#print axioms R3Cert.Step3.Aobj_cherrySpider6
#print axioms R3Cert.Step3.straightStep_tripleStar_witness
#print axioms R3Cert.Step3.tripleStar_has_straightStep
