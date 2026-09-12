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
import R3Cert.R47BroadenedTieWitness
import R3Cert.R47TieBroadened
import R3Cert.R47R7TwoHubBridge
import R3Cert.R47SingleHub2D
import R3Cert.R47SharpRate
import R3Cert.R47SingleHubResidue
import R3Cert.BGSCLFlpMove
import R3Cert.BGSCLFlpDeepLift
import R3Cert.BGSCLFlpStepAt
import R3Cert.R47R7StuckChar
import R3Cert.R47WPairLift
import R3Cert.R47MHubTelescope
import R3Cert.R47WPair6
import R3Cert.R47PC6Final
import R3Cert.R47TieArgmax
import R3Cert.R47AdjLeafStruct
import R3Cert.R47AdjLeafGains
import R3Cert.R47AdjLeafStep
import R3Cert.R47CoverRelation
import R3Cert.R47RootShift
import R3Cert.R47AlignedMinSize
import R3Cert.R47HnormFalse52
import R3Cert.R47HnormMulti
import R3Cert.R47HwhLeafDecomp
import R3Cert.R47HwhPieceDecomp
import R3Cert.R47HwhAdjDecomp
import R3Cert.R47HwhAdjPieceDecomp
import R3Cert.R47HwhB1Partial
import R3Cert.R47MatchingSum
import R3Cert.R47HwhSymStarCert
import R3Cert.R47HwhSymStar3Cert
import R3Cert.R47HwhSymStarGenCert

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

-- Near-star NON-maximality (2026-09-05): the broadened config (5 load-4 arms + 5 cherries) strictly
-- beats the near-star (5 load-5 arms) at the SAME size 56, so conjecture1/SharpRateNF with the
-- near-star tie is FALSE at this n.  Kernel-verified via singleHub_Aobj_formula + Ztot_armU_four.
#print axioms R3Cert.Step3.nearStar_not_maximal_at_five

-- Broadened tie family M1 (2026-09-06): the corrected per-size tie `tieState K m` (single hub with
-- (K-m) load-5 arms + m load-4 arms + m cherries) and its EXACT closed-form objective value
-- `tie_Aobj_eq_V` = V(K,m), matching the 3-engine-verified broadened_tie_family.py.
#print axioms R3Cert.Step3.tie_trade_factor
#print axioms R3Cert.Step3.tie_Aobj_eq_V
#print axioms R3Cert.Step3.tie_Aobj_factored
#print axioms R3Cert.Step3.tie_trade_le
#print axioms R3Cert.Step3.tie_trade_le_poly
#print axioms R3Cert.Step3.tradeStop_persists
#print axioms R3Cert.Step3.tie_maximal_over_trades

-- Two-hub Aobj-bridge M4 (2026-09-06): the abstract two-hub Positivstellensatz certs
-- `two_hub_gap_pos_c0..c5` wired to `Aobj` -- the stuck two-hub config S2(pA,pB,cA) is dominated by
-- the same-size single-hub downgrade template at every pA,pB>=1, cA in {0..5} (length-2 slice of Hdom).
#print axioms R3Cert.Step3.twoHub_Aobj_eq
#print axioms R3Cert.Step3.twoHub_le_tie

-- Single-hub 2-D envelope, T-AXIS (M3, 2026-09-06): the bulk-swap column `colState K c t` is unimodal
-- in `t` (the `hub_bulk_le` analog of the tie trade machinery); `col_maximal_over_bulk` = each column's
-- t-argmax dominates. 22-digit `bulkStop` poly cross-checked in broadened_tie_2d_envelope.py.
#print axioms R3Cert.Step3.hub_bulk_stop_iff
#print axioms R3Cert.Step3.bulkStopABC_persists
#print axioms R3Cert.Step3.col_maximal_over_bulk

-- Single-hub 2-D envelope, CLEAN REGIME K>=23 (M3 c-envelope, 2026-09-06): the bulk column collapses to
-- its tie edge (col_le_edge_large) and then across cherry counts to the near-star (col_le_nearStar_large)
-- -- every Balanced single hub at aligned size 11K, K>=23, is dominated by tieState K 0.
#print axioms R3Cert.Step3.colStop_zero_large
#print axioms R3Cert.Step3.col_le_edge_large
#print axioms R3Cert.Step3.col_le_nearStar_large
#print axioms R3Cert.Step3.hubState_eq_colState
#print axioms R3Cert.Step3.singleHub_le_tie_large
#print axioms R3Cert.Step3.tie_maximal_general
#print axioms R3Cert.Step3.singleHub_le_tie_ge22
#print axioms R3Cert.Step3.mOf_le_five
#print axioms R3Cert.Step3.singleHub_le_tie_lt22
#print axioms R3Cert.Step3.singleHub_le_tie

-- Hdom length-1 slice at aligned sizes (2026-09-06): a Balanced+Capped single hub reduces (arm-perm to
-- (a,b) counts) to singleHub_le_tie, so it is dominated by alignedTie at its own size -- the length-1
-- case of SharpRateNF/Hdom, discharged by the M3 envelope.
#print axioms R3Cert.Step3.singleHub_dominated
#print axioms R3Cert.Step3.sharpRate_singleHub_aligned

-- Residue-general single-hub atoms (non-aligned-n layer, 2026-09-06): the general cherry-trade step
-- hub_trade_le (114/115, no b=c) + its polynomial hubTradeStop; the shifted tie edge rtieState M r c
-- (per-size maximizer for residue r) and its trade argmax rtie_maximal_over_trades (analog of
-- tie_maximal_over_trades across all 11 residue classes).
#print axioms R3Cert.Step3.hub_trade_le
#print axioms R3Cert.Step3.hub_trade_stop_iff
#print axioms R3Cert.Step3.rtie_maximal_over_trades
#print axioms R3Cert.Step3.rtie_maximal_general
#print axioms R3Cert.Step3.col_maximal_over_bulkR
#print axioms R3Cert.Step3.colStopR_zero_large
#print axioms R3Cert.Step3.col_le_edgeR
#print axioms R3Cert.Step3.singleHubR_le_tie_large
#print axioms R3Cert.Step3.singleHubR_le_tie_edge
#print axioms R3Cert.Step3.rNeg_r6
#print axioms R3Cert.Step3.singleHubR_le_tie_07
#print axioms R3Cert.Step3.neg_maximal_general
#print axioms R3Cert.Step3.neg_bulk_link
#print axioms R3Cert.Step3.singleHubR_le_tie_10
#print axioms R3Cert.Step3.off_maximal_general
#print axioms R3Cert.Step3.singleHubR_le_tie_89
#print axioms R3Cert.Step3.rMOf_le_five
#print axioms R3Cert.Step3.negMOf_le_five
#print axioms R3Cert.Step3.offMOf_le_five
#print axioms R3Cert.Step3.singleHubR_le_tie_small_r1
#print axioms R3Cert.Step3.singleHubR_le_tie_small_r5

-- Open-cores campaign (2026-09-08, branch bg/multihub-hnorm).
-- B-track (Hnorm): the FLP move class -- local step, UNCONDITIONAL deep lift (the per-level
-- Obligation-A debt discharged by the self-propagating cavity-gain pair), and the depth-closed
-- multi-flip class with the generic coverage reduction (Hnorm's open half = a coverage statement).
#print axioms R3Cert.Step3.flp_local_straightStep
#print axioms R3Cert.Step3.dtSub_gains_lift
#print axioms R3Cert.Step3.Aobj_child_replace_of_gains
#print axioms R3Cert.Step3.flp_deep_straightStep
#print axioms R3Cert.Step3.multiFlp_child_stats
#print axioms R3Cert.Step3.FlpStepAt.props
#print axioms R3Cert.Step3.FlpStepAt.straightStep
#print axioms R3Cert.Step3.straightProgress_sized_of_coverage
#print axioms R3Cert.Step3.hnorm_of_coverage
-- A-track (m>=3 Hdom): the stuck-pair characterization; the weak-pair context lift (the
-- endpoint-linearity invariant surviving degree-jumping replacements); the multi-hub telescope
-- reducing Hdom at ANY length to the single named open certificate PairCollapse plus the
-- single-hub tie bound.
#print axioms R3Cert.Step3.stuck_pair_deloaded
#print axioms R3Cert.Step3.stuck_pair_dichotomy
#print axioms R3Cert.Step3.dtSub_wpair_lift
#print axioms R3Cert.Step3.Aobj_child_replace_of_wpair
#print axioms R3Cert.Step3.plugFrames_wpair
#print axioms R3Cert.Step3.backbone_tail_wpair
#print axioms R3Cert.Step3.backbone_tail_aobj
#print axioms R3Cert.Step3.mhub_le_single_of_pairCollapse
#print axioms R3Cert.Step3.hdom_of_pairCollapse_and_singleHubDom

-- A3 v2 (2026-09-08): the CORRECTED 1/6-weighted collapse invariant (v1 PairCollapse falsified
-- by the exact-Fraction de-risk; witness (0,5,1|47,1,1)).  Capped frames carry >= 6 children, so
-- the ancestor weights obey w <= 1/6 and the weighted pair self-propagates.
#print axioms R3Cert.Step3.dtSub_wpair6_lift
#print axioms R3Cert.Step3.Aobj_child_replace_of_wpair6
#print axioms R3Cert.Step3.backbone_tail_wpair6
#print axioms R3Cert.Step3.backbone_tail_aobj6
#print axioms R3Cert.Step3.mhub_le_single_of_pairCollapse6
#print axioms R3Cert.Step3.hdom_of_pairCollapse6_and_singleHubDom

-- A3(2) COMPLETE (2026-09-09): PairCollapse6 is a THEOREM (the m>=3 collapse certificate --
-- 138 polynomial cells + closed-form transport + reductions + the exists-assembly), so the
-- multi-hub Hdom reduces to the single-hub tie bound (hdom_of_singleHubDom).
#print axioms R3Cert.Step3.PC6.pairCollapse6
#print axioms R3Cert.Step3.PC6.hdom_of_singleHubDom

-- TIE-DEFINITION LAYER CLOSED (2026-09-09): a concrete per-size tie `tieArgmax` (the finite argmax
-- single hub of each size) discharges the whole Hdom side; Conjecture 1 now reduces to Hnorm alone.
#print axioms R3Cert.Step3.hdom_capstone
#print axioms R3Cert.Step3.conjecture1_of_Hnorm

-- ADJACENT LEAF StraightStep, structural core (2026-09-10): nB=0 defect-neutrality -> defect-reducing
-- adjacent leaf move forces nB>=1 (the Aobj-safe region N>=N0>=0). Crux (a) of the monomer-dimer program.
#print axioms R3Cert.Step3.strDefect_adjLeaf_nB0

-- ADJACENT LEAF StraightStep, Aobj half (2026-09-10): base cavity gains G1/G2 + the lifted Aobj clause.
#print axioms R3Cert.Step3.adjLeaf_Aobj_le

-- ADJACENT LEAF StraightStep COMPLETE (2026-09-10): the first coverage extension beyond FlpStepAt.
#print axioms R3Cert.Step3.adjLeaf_straightStep

-- COVER RELATION (2026-09-10): CoverR = FlpStepAt + AdjLeafStep refines StraightStep_sized; Hnorm reduces
-- to CoverR coverage (hnorm_of_coverR_coverage). Sole open obligation = coverage.
#print axioms R3Cert.Step3.hnorm_of_coverR_coverage

-- ROOT-SHIFT Aobj-invariance (2026-09-10): the crux enabler for a RerootStep coverage class (no graph-iso).
#print axioms R3Cert.Step3.Aobj_rootShift

-- ALIGNED-N SCOPING (2026-09-11): Balanced+Capped hub-state size >= 46, so capstone Hnorm is unsatisfiable
-- for 0 < n < 46 (small/off-lattice n are a separate residual). Correction 2, kernel-formalized.
#print axioms R3Cert.Step3.no_capped_state_of_size_lt_46

-- HNORM FALSE AT 52 (2026-09-11): the four-core witness T52 (usize 52) strictly exceeds every
-- Balanced+Capped state of size 52, so the capstone Hnorm is genuinely FALSE at aligned multi-hub
-- sizes -- sharpening the residual beyond mere aligned-n scoping. Exact-fraction counterexample.
#print axioms R3Cert.Step3.aobj_T52_eq
#print axioms R3Cert.Step3.tieArgmax_52_lt_T52
#print axioms R3Cert.Step3.r47_hnorm_false_at_52
#print axioms R3Cert.Step3.hnorm_capstone_false

-- BROADENED capstone (2026-09-11): reduce every tree to an ARBITRARY multi-hub cherry-backbone
-- (not just a Balanced+Capped single hub). The n=52 refutation dissolves (T52 witnesses its own
-- HnormMulti clause); the sole open piece is the tree->backbone straightening = open BG structural core.
#print axioms R3Cert.Step3.conjecture1_of_HnormMulti
#print axioms R3Cert.Step3.hnormMulti_of_hnorm
#print axioms R3Cert.Step3.hnormMulti_holds_at_T52
#print axioms R3Cert.Step3.singleHub_refuted_but_multiHub_open

-- HnormMulti is discharged by the pre-existing whole-hub obligation hwh (unrefuted by the n=52
-- counterexample -- hwh feeds only the general-backbone straightening; the refutation killed the
-- SEPARATE general->Balanced+Capped normalization). hwh + HdomMulti => broadened conjecture 1.
#print axioms R3Cert.Step3.hnormMulti_of_wholehub
#print axioms R3Cert.Step3.conjecture1_of_HnormMulti_of_wholehub

-- hwh leaf-move decomposition (2026-09-11): exact identity
-- (AobjAfter-AobjBefore)*a(b+1) = (a+b+1)*B1 + (a-b-1)*B2; B2>=0 from the proven combinatorial bound
-- P11<=(a-1)b*P00; monotone leaf move when B1>=0, that bound, and b+1<=a. B1>=0 under min-degree
-- defect-reducing selection is the open core.
#print axioms R3Cert.Step3.hwh_leaf_decomp
#print axioms R3Cert.Step3.leafB2_nonneg
#print axioms R3Cert.Step3.leaf_move_monotone

-- General piece-relocation decomposition (2026-09-11): extends the leaf decomposition to any rigid
-- piece (leaf/cherry/arm/sub-star) via cavity scalars Z=Ztot(dtSub K), rho=phi/dc. Exact identity +
-- monotonicity-from-RHS. Leaf case (Z=rho=1) recovers R47HwhLeafDecomp's B1/B2 form.
#print axioms R3Cert.Step3.hwh_piece_decomp
#print axioms R3Cert.Step3.piece_move_monotone
#print axioms R3Cert.Step3.hwh_piece_decomp_leaf

-- Adjacent-p,w leaf decomposition (2026-09-11): the p~w case; identity + B2adj>=0 (adjacent counting
-- P11<=(a-2)(b-1)P00) + monotonicity. Open input again B1>=0.
#print axioms R3Cert.Step3.hwh_adj_decomp
#print axioms R3Cert.Step3.B2adj_nonneg
#print axioms R3Cert.Step3.adj_move_monotone

-- Adjacent general-piece decomposition (2026-09-12): completes the grid (leaf/piece x non-adj/adj).
#print axioms R3Cert.Step3.hwh_adj_piece_decomp
#print axioms R3Cert.Step3.adj_piece_move_monotone

-- PARTIAL B1 (2026-09-12): B1>=0 on the P01=0 slice (target has no H-neighbours); the cherry-forming
-- move (leaf onto adjacent sibling leaf) is unconditionally Aobj-monotone. A proven slice of the open core.
#print axioms R3Cert.Step3.B1_nonneg_of_P01_zero
-- g-dominance sufficient condition for the open B1 kernel (2026-09-12): p-neighbours g-dominate
-- w-neighbours => B1>=0. Broader than the P01=0 slice (covers ~69% of moves; sound 106/106).
#print axioms R3Cert.Step3.B1_nonneg_of_gdominance
#print axioms R3Cert.Step3.cherry_forming_monotone

-- Weighted-matching-sum theory (2026-09-12): discharges the ESSENTIAL content of the B2 hypothesis
-- (deletion monotonicity Z(H-S) antitone) from an actual matching theory, not an assumption.
#print axioms R3Cert.Step3.ZsumAvoid_antitone
#print axioms R3Cert.Step3.B2_termwise
#print axioms R3Cert.Step3.B2_bound_of_terms
#print axioms R3Cert.Step3.ZsumAvoid_nonneg
-- B2 bound fully assembled over the matching theory (2026-09-12): P11 <= pairs.card * P00, i.e. the
-- B2 hypothesis of R47HwhLeafDecomp is now a THEOREM (no longer assumed).
#print axioms R3Cert.Step3.B2_bound

-- UNIFORM certificate for the symmetric-multi-star obstruction (2026-09-12): the de-branching move is
-- Aobj-monotone on the WHOLE balanced multi-star family ST(k,m), k>=3,m>=2 (incl. the triple-3-star),
-- via F_num>=0 reduced to two shifted-nonneg-coeff cubic positivities.
#print axioms R3Cert.Step3.symstar_cubicA_nonneg
#print axioms R3Cert.Step3.symstar_cubicF3_nonneg
#print axioms R3Cert.Step3.symstar_move_certificate
-- Non-balanced extension (2026-09-12): general 3-hub multi-star (arbitrary m_i>=2), via all-nonneg-coeff shift.
#print axioms R3Cert.Step3.symstar3_move_certificate
-- k-UNIFORM non-balanced certificate (2026-09-12): de-branching move Aobj-monotone on EVERY multi-star
-- (any k>=3, any hub sizes m_i>=2, any spectators), via coeff_S1>=0, G>=0 (shifted nonneg coeffs) + assembly.
#print axioms R3Cert.Step3.symstar_gen_coeffS1_nonneg
#print axioms R3Cert.Step3.symstar_gen_G_nonneg
#print axioms R3Cert.Step3.symstar_gen_move_monotone
