/-
  BG asymptotic upper bound — the SCL price-flow recursion, RESTATED for the flowed per-hub step.

  Corrects the reduction target.  The single-price per-hub step (`SCLStep μ` / `PSCL := ∀μ∈I …`, BGSCLStep) is
  the WRONG obligation on two counts, both verified in Telperion (`bg/scl-decouple-cert`, PR #194):

    (1) the tangent decouple needs the child IH at the FLOWED price `μ'' = muPP d μ`, not the single price `μ`
        (single-price residual `+0.15..+0.43`, VIOLATES; the flowed step closes over `I` with margin `≥ +0.011`);
    (2) the uniform `∀ b, PSCL b` is FALSE at the bare leaf `node []` (`bV μ (node []) − bV μ cherry
        = (2/3)μ − (log(3/2)−F*) > 0` for `μ > 0.298`, and `I` reaches `3/7`), so `scl_of_step'`'s hypothesis is
        unsatisfiable at `cs = []`.

  This module states the CORRECT reduction: a leaf-EXCLUDING predicate `PSCLne` (the bare leaf is not claimed —
  it is not a hub and never the argmax) and the FLOWED per-hub step `FlowedHubStep` (children at the flowed price).
  `scl_of_flowed_step` reduces the SCL for every non-leaf branch to `FlowedHubStep`, with the bare-leaf base case
  VACUOUS.  `FlowedHubStep` itself is discharged (future work here) by: the concave-log tangent
  (`bell_node_tangent`) + `bY_node`; the child IH at `μ'' ∈ I` (`muPP_mem_I`) for non-leaf children and
  `leaf_le_cherry` (`μ'' ≤ 3/11`, `muPP_le_three_eleven`) for leaf children; the reference-broom leg
  (Telperion `BroomVsCherryOnICertificate`); and the per-hub decouple residual (Telperion
  `PerHubDecoupleResidualCertificate`, 20 `norm_num` atoms — the endpoint reduction of the upward parabola in `S`).

  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLStep

namespace R3Cert
namespace BGSCL

/-- **The leaf-excluding price-carrying SCL predicate.**  The bare leaf `node []` is deliberately NOT claimed:
    it violates `bV μ (node []) ≤ bV μ cherry` for `μ > 0.298` (`bell_leaf = -F*`, `bY_leaf = 1`), and `I`
    reaches `3/7`.  Every NON-leaf branch satisfies the price-carrying SCL on all of `I`.  This is the correct
    top-level object — the uniform `PSCL` (`∀ b`) is unprovable at the bare leaf. -/
def PSCLne (b : Branch) : Prop :=
  b ≠ Branch.node [] → ∀ μ, inI μ → bV μ b ≤ bV μ cherry

/-- **The flowed per-hub step** — the CORRECT per-hub obligation.  A non-empty hub whose children each satisfy the
    leaf-excluding SCL gives the SCL for the hub, on all of `I`.  The child IH is used at the FLOWED price
    `μ'' = muPP d μ ∈ I` (which the discharge instantiates), not the single price `μ`. -/
def FlowedHubStep : Prop :=
  ∀ cs : List Branch, cs ≠ [] → (∀ c ∈ cs, PSCLne c) →
    ∀ μ, inI μ → bV μ (Branch.node cs) ≤ bV μ cherry

/-- **The concrete SCL for every non-leaf branch, from the flowed per-hub step.**  Well-founded recursion on
    `|b|` (as `scl_of_step'`), but with the leaf-excluding predicate: the bare-leaf case is VACUOUS
    (`node [] ≠ node []` is false), so the false leaf obligation never arises; a non-empty hub reduces to
    `FlowedHubStep` with the child IH.  This is the correct reduction of the SCL to the (true, verified) flowed
    per-hub step.  `conjecture1_proved = False`. -/
theorem scl_of_flowed_step (hstep : FlowedHubStep) : ∀ b, PSCLne b := by
  refine scl_of_child_step bsize bchildren PSCLne bchildren_bsize_lt (fun a hIH => ?_)
  cases a with
  | node cs =>
    show Branch.node cs ≠ Branch.node [] → ∀ μ, inI μ → bV μ (Branch.node cs) ≤ bV μ cherry
    intro hne
    have hcs : cs ≠ [] := fun h => hne (by rw [h])
    exact hstep cs hcs (fun c hc => hIH c (by simpa only [bchildren] using hc))

end BGSCL
end R3Cert
