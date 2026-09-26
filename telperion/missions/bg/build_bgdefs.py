#!/usr/bin/env python3
"""Assemble lean/Statements/BGDefs.lean from VERBATIM extracts of the proof/ R3Cert island.

Run from telperion/missions/bg/.  Every definition is copied by exact line range from its
source module (cited inline); re-running this script and diffing detects mirror drift.
The only non-copied block is the PROVISIONAL hubCount section, clearly marked.
"""
from pathlib import Path

R3 = Path(__file__).resolve().parents[3] / "proof" / "formalization" / "R3Cert"
OUT = Path(__file__).resolve().parent / "lean" / "Statements" / "BGDefs.lean"


def ex(module: str, lo: int, hi: int) -> str:
    lines = (R3 / module).read_text().split("\n")
    return "\n".join(lines[lo - 1:hi])


parts = [
    """/-
  Statements.BGDefs -- vocabulary mirror for the BG missions registry.  NOT a node statement.

  Every definition below is a VERBATIM line-range copy from the proof/ R3Cert island
  (toolchain leanprover/lean4:v4.32.0), source module cited above each block; the copies are
  regenerated/diffed by missions/bg/build_bgdefs.py.  Where the original lives in section
  variables, the section is reproduced verbatim.  This file exists so that node statement
  files elaborate standalone against Mathlib; the *registry statements* are the node files,
  which the verify gate matches against the real proof/ artifacts by normalized containment.

  The PROVISIONAL blocks (hubCount*, cavR/phi11R) are registry-only vocabulary (no proof/
  counterpart) used by draft nodes only; they are NOT part of any proved statement.
-/
import Mathlib

namespace R3Cert
""",
    "-- ===== ExactCruxes.lean:70 =====",
    ex("ExactCruxes.lean", 70, 70),
    "\n-- ===== Sweep.lean:24,26 =====",
    ex("Sweep.lean", 24, 24),
    ex("Sweep.lean", 26, 26),
    "\n-- ===== Potential.lean:33,37-40 =====",
    ex("Potential.lean", 33, 33),
    ex("Potential.lean", 37, 40),
    "\n-- ===== Reach.lean:24-25,27-35,160-178 =====",
    ex("Reach.lean", 24, 25),
    "",
    ex("Reach.lean", 27, 35),
    "",
    ex("Reach.lean", 160, 178),
    "\n-- ===== NearStar.lean:43,46 =====",
    ex("NearStar.lean", 43, 43),
    ex("NearStar.lean", 46, 46),
    "\n-- ===== Plainify.lean:182-189 =====",
    ex("Plainify.lean", 182, 189),
    "\n-- ===== PotentialBound.lean:24-28 =====",
    ex("PotentialBound.lean", 24, 28),
    "\n-- ===== CavityTree.lean:31-49 (RTree + partition functions) =====",
    ex("CavityTree.lean", 31, 49),
    "end RTree",
    "\n-- ===== Matching.lean:57-64 (lapl, in its verbatim section context) =====",
    ex("Matching.lean", 57, 64),
    "end Combinatorial",
    "\nnamespace Step3\n\nopen RTree",
    "\n-- ===== BridgeStep3.lean:85-100 (address realization) =====",
    ex("BridgeStep3.lean", 85, 100),
    "\n-- ===== BridgeStep3e.lean:31,34,47-48,50-52,55,58-70 (address graph) =====",
    ex("BridgeStep3e.lean", 31, 31),
    ex("BridgeStep3e.lean", 34, 34),
    ex("BridgeStep3e.lean", 47, 48),
    ex("BridgeStep3e.lean", 50, 52),
    ex("BridgeStep3e.lean", 55, 55),
    ex("BridgeStep3e.lean", 58, 70),
    "\n-- ===== R47Tree.lean:33-34,37-38,45-57,132 (UTree, realization, Aobj) =====",
    ex("R47Tree.lean", 33, 34),
    "",
    ex("R47Tree.lean", 37, 38),
    "",
    ex("R47Tree.lean", 45, 57),
    "",
    ex("R47Tree.lean", 132, 132),
    "\n-- ===== R47HubState.lean:30,33,36,40-46 (hub states) =====",
    ex("R47HubState.lean", 30, 30),
    ex("R47HubState.lean", 33, 33),
    ex("R47HubState.lean", 36, 36),
    ex("R47HubState.lean", 40, 46),
    "\n-- ===== R47Backbone.lean:24-26 (tailU) =====",
    ex("R47Backbone.lean", 24, 26),
    "\n-- ===== R47StepSize.lean:30-38,83,86 (sizes) =====",
    ex("R47StepSize.lean", 30, 38),
    "",
    ex("R47StepSize.lean", 83, 83),
    ex("R47StepSize.lean", 86, 86),
    "\n-- ===== R47Step.lean:41,45 / R47Capped.lean:39 (families) =====",
    ex("R47Step.lean", 41, 41),
    ex("R47Step.lean", 45, 45),
    ex("R47Capped.lean", 39, 39),
    "\n-- ===== R47OrderedStep.lean:43-58 (the ordered merge relation) =====",
    ex("R47OrderedStep.lean", 43, 58),
    "\n-- ===== R47R7Straighten.lean:36-38,41-44,47-48,51,70-72,74-83 (structural defect) =====",
    ex("R47R7Straighten.lean", 36, 38),
    ex("R47R7Straighten.lean", 41, 44),
    ex("R47R7Straighten.lean", 47, 48),
    ex("R47R7Straighten.lean", 51, 51),
    ex("R47R7Straighten.lean", 70, 72),
    ex("R47R7Straighten.lean", 74, 83),
    "\n-- ===== R47R7Sized.lean:65-66,69-70 (size-preserving straightening) =====",
    ex("R47R7Sized.lean", 65, 66),
    ex("R47R7Sized.lean", 69, 70),
    "\n-- ===== R47BGConjecture.lean:38-39 (the pinned conjecture 1) =====",
    ex("R47BGConjecture.lean", 38, 39),
    """
-- ===== PROVISIONAL (registry-only; no proof/ counterpart; used by the DRAFT/deprecated
-- nodes BG_r2_multihub_maximality [deprecated 2026-09-13] and BG_r2_multihub_ceiling).
-- Hub count of a bare rooted tree: vertices of structural degree >= 3 (root degree =
-- child count; non-root degree = children + parent edge). =====
mutual
def hubCountRoot : UTree → ℕ
  | .node cs => (if 3 ≤ cs.length then 1 else 0) + hubCountList cs
def hubCountSub : UTree → ℕ
  | .node cs => (if 3 ≤ cs.length + 1 then 1 else 0) + hubCountList cs
def hubCountList : List UTree → ℕ
  | [] => 0
  | K :: rest => hubCountSub K + hubCountList rest
end

-- ===== PROVISIONAL (registry-only; no proof/ counterpart; used only by the DRAFT node
-- BG_r2_multihub_ceiling).  The ROOTED branch Phi^11 recursion in exact rationals,
-- mirroring telperion/src/telperion/bg/rooted_phi.py::phi11_rooted line-by-line
-- (cr=0 plain-tree model): at a vertex with child list cs, S = sum of child cavities,
-- d = cs.length + 1 (virtual parent edge), z = 3/(3*d);
--   cavR    = z / (1 + z*S)
--   phi11R  = (64/621) * (1 + z*S)^11 * prod over children of phi11R.
-- The tree invariant is max over roots; a CEILING stated for ALL UTree (all rooted
-- representations) is equivalent to the max-over-roots ceiling on unrooted trees. =====
mutual
def cavR : UTree → ℚ
  | .node cs =>
      let d : ℚ := ((cs.length + 1 : ℕ) : ℚ)
      let z : ℚ := 3 / (3 * d)
      z / (1 + z * cavRList cs)
def cavRList : List UTree → ℚ
  | [] => 0
  | K :: rest => cavR K + cavRList rest
end

mutual
def phi11R : UTree → ℚ
  | .node cs =>
      let d : ℚ := ((cs.length + 1 : ℕ) : ℚ)
      let z : ℚ := 3 / (3 * d)
      (64 / 621) * (1 + z * cavRList cs) ^ 11 * phi11RList cs
def phi11RList : List UTree → ℚ
  | [] => 1
  | K :: rest => phi11R K * phi11RList rest
end

end Step3
end R3Cert

-- ===== GStepCore.lean:25 / CappedJointConfig.lean:33-46 / CappedJointAchievable.lean:30 =====
namespace R3Cert.GStepCore
""",
    ex("GStepCore.lean", 25, 25),
    "end R3Cert.GStepCore",
    "\nnamespace R3Cert.CappedJointConfig\n\nopen R3Cert.GStepCore",
    "",
    ex("CappedJointConfig.lean", 33, 33),
    ex("CappedJointConfig.lean", 36, 36),
    ex("CappedJointConfig.lean", 39, 39),
    ex("CappedJointConfig.lean", 42, 43),
    ex("CappedJointConfig.lean", 46, 46),
    ex("CappedJointAchievable.lean", 30, 30),
    "\nend R3Cert.CappedJointConfig",
    "\n-- ===== BGSCL literal planted matching-sum model =====",
    "-- ===== BGSCLInduction.lean:151-152,154-162,192-193,195-206,236,240 / BGSCLHdom.lean:475,482-483 =====",
    "namespace R3Cert.BGSCL\n",
    ex("BGSCLInduction.lean", 151, 152),
    ex("BGSCLInduction.lean", 154, 162),
    ex("BGSCLInduction.lean", 192, 193),
    ex("BGSCLInduction.lean", 195, 206),
    ex("BGSCLInduction.lean", 236, 236),
    ex("BGSCLInduction.lean", 240, 240),
    ex("BGSCLHdom.lean", 475, 475),
    ex("BGSCLHdom.lean", 482, 483),
    "\nend R3Cert.BGSCL",
]

OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text("\n".join(parts) + "\n")
print(f"wrote {OUT} ({len(OUT.read_text().splitlines())} lines)")
