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

#print axioms R3Cert.Step3.conjecture1_of_layers
#print axioms R3Cert.phi_le_one
#print axioms R3Cert.CappedJointConfig.gstep_le_one_achievable

-- Additive SUBACTION reduction chain (the ceiling now rests on `IsSubaction ρwit`).
#print axioms R3Cert.BGSCL.ceiling_of_subaction
#print axioms R3Cert.BGSCL.ρwit_nonneg
#print axioms R3Cert.BGSCL.ceiling_of_witness

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
#print axioms R3Cert.BGSCL.subaction_deg3_deg2_high
