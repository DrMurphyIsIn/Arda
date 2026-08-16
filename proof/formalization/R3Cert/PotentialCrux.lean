/-
  Toward the crux `ValidPotentialPlain Pval` (Potential.lean / PotentialBound.lean): the per-node
  super-solution  `eroot 0 ch <= (Σ_{b∈ch} Pval(cav b)) - Pval(cav (node 0 ch))`  for all plain `ch`.

  This file establishes the two BOUNDARY cases -- the leaf node (`ch = []`) and the arm node
  (`ch = [leaf]`) -- both of which hold with EQUALITY, verifying that `Pval` correctly encodes the folded
  charge (`Pval(1/3)=|omega|`, `Pval(1)=Lval`): `eroot(arm)+Pval(1/3) = Pval(1)` and `eroot(leaf)+Pval(1)=0`.

  The GENERAL case (nodes with structural children) is the residual crux: it requires the convexity
  reduction to equal children, the `m>=3` analytic branch (monotone-`f` on the Lean-verified `lemmaA_arith`),
  and the `m in {1,2}` interval bounds -- a large formalization, not done here.

  Genuine proofs (no `sorry`).
-/
import Mathlib
import R3Cert.Reach
import R3Cert.NearStar
import R3Cert.Potential
import R3Cert.PotentialBound

namespace R3Cert

open Real

/-- `eroot 0 [] = -Lval` (leaf root increment). -/
theorem eroot_nil : eroot 0 ([] : List Branch) = -Lval := by
  have h : logPhi (Branch.node 0 []) = logPhiSum ([] : List Branch) + eroot 0 [] := rfl
  rw [logPhi_leaf] at h
  simp only [logPhiSum] at h
  linarith

/-- `eroot 0 [leaf] = -Lval + log(3/2)` (arm root increment). -/
theorem eroot_arm : eroot 0 [Branch.node 0 []] = -Lval + Real.log (3 / 2) := by
  have h : logPhi armB = logPhiSum [Branch.node 0 []] + eroot 0 [Branch.node 0 []] := rfl
  rw [logPhi_arm] at h
  simp only [logPhiSum, logPhi_leaf] at h
  linarith

/-- **Super-solution at a LEAF node** (`ch = []`), with equality. -/
theorem superSol_nil :
    eroot 0 ([] : List Branch) ≤
      (([] : List Branch).map (fun b => Pval (cav b))).sum - Pval (cav (Branch.node 0 [])) := by
  rw [eroot_nil, cav_leaf, Pval_one]
  simp

/-- **Super-solution at an ARM node** (`ch = [leaf]`), with equality
    (`eroot(arm) + Pval(1/3) = Pval(1)`, i.e. the arm-unit `omega` folded into `Pval`). -/
theorem superSol_arm :
    eroot 0 [Branch.node 0 []] ≤
      ([Branch.node 0 []].map (fun b => Pval (cav b))).sum - Pval (cav armB) := by
  rw [eroot_arm, cav_arm, Pval_third]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, cav_leaf, Pval_one]
  unfold omegaVal
  linarith

end R3Cert
