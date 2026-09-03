/-
  The deg≥5 tail crux family + the 27·23 tie identity (2026-09-03).

  Two pieces of `IsSubaction ρwit` beyond the degree-3/4 core:

  * `tail_all_deg4` — the CRUX of the deg≥5 tail.  For a degree-`d` hub (`d ≥ 1`) whose children are all
    degree-4 at the maximal message `1/4` (`S = (d−1)/4`, `ρwit(node)=0`), the local excess obeys
    `log((5d−1)/(4d)) − F* ≤ (d−1)/1536`.  This is the flattest per-type tail family (`ρ = bY/384`), min
    slack `+0.0057` at `d=18`.  Proof: `log((5d−1)/(4d)) = log(5/4) + log(1 − 1/(5d)) ≤ log(5/4) − 1/(5d)`
    (concavity, `Real.log_le_sub_one_of_pos`), then the atom `log(5/4) − F* ≤ 1/55` reduces it to a rational
    quadratic in `d` with NEGATIVE discriminant (`55d² − 1591d + 16896 > 0`, via `sq_nonneg (110d − 1591)`).

  * `subaction_tail_tie_d6` — the 27·23 = 621 tie.  A degree-6 hub with five cherry children (each deg-2 at
    `bY = 1/3`, `ρwit = 2F*−log(3/2)`; `ρwit(node)=0`) meets `(SUB)` with EXACT equality, because
    `(23/18)·(3/2)⁵ = 621/64`, i.e. `log(23/18) + 5·log(3/2) = 11·F* = log(621/64)`.

  Kernel-checked, no `sorry`.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction
import R3Cert.BGSCLSubaction

namespace R3Cert
namespace BGSCL

open Real

/-! ### The deg≥5 tail crux: the all-degree-4 `d`-family. -/

/-- **`tail_all_deg4`.**  For every real `d ≥ 1`, `log((5d−1)/(4d)) − F* ≤ (d−1)/1536`.  This is the binding
    per-type family of the deg≥5 tail (all children degree-4 at message `1/4`); the slack is convex in `d`
    with a single interior minimum `+0.0057` at `d = 18`. -/
theorem tail_all_deg4 (d : ℝ) (hd : 1 ≤ d) :
    Real.log ((5 * d - 1) / (4 * d)) - FSTAR ≤ (d - 1) / 1536 := by
  have hd0 : (0 : ℝ) < d := by linarith
  have h5d : (0 : ℝ) < 5 * d := by linarith
  -- factor: (5d−1)/(4d) = (5/4)·(1 − 1/(5d))
  have hfact : (5 * d - 1) / (4 * d) = (5 / 4) * (1 - 1 / (5 * d)) := by
    field_simp
  have harg_pos : (0 : ℝ) < 1 - 1 / (5 * d) := by
    have : 1 / (5 * d) < 1 := by rw [div_lt_one h5d]; linarith
    linarith
  have hsplit : Real.log ((5 * d - 1) / (4 * d)) = Real.log (5 / 4) + Real.log (1 - 1 / (5 * d)) := by
    rw [hfact, Real.log_mul (by norm_num) (ne_of_gt harg_pos)]
  -- concavity: log(1 − 1/(5d)) ≤ −1/(5d)
  have hlog1 : Real.log (1 - 1 / (5 * d)) ≤ -(1 / (5 * d)) := by
    have h := Real.log_le_sub_one_of_pos harg_pos
    linarith
  -- the atom log(5/4) − F* ≤ 1/55
  have henc : Real.log (5 / 4) - FSTAR ≤ 1 / 55 := log54_sub_fstar_le'
  -- rational quadratic: 1/55 − 1/(5d) ≤ (d−1)/1536  (discriminant of 55d²−1591d+16896 is < 0)
  have hquad : (1 : ℝ) / 55 - 1 / (5 * d) ≤ (d - 1) / 1536 := by
    rw [← sub_nonneg]
    have hden : (0 : ℝ) < 422400 * d := by positivity
    have hnum : (0 : ℝ) ≤ 275 * d ^ 2 - 7955 * d + 84480 := by
      nlinarith [sq_nonneg (110 * d - 1591)]
    have hid : (d - 1) / 1536 - (1 / 55 - 1 / (5 * d))
        = (275 * d ^ 2 - 7955 * d + 84480) / (422400 * d) := by
      field_simp; ring
    rw [hid]; exact div_nonneg hnum (le_of_lt hden)
  linarith [hsplit, hlog1, henc, hquad]

/-! ### The 27·23 = 621 tie identity (deg-6 hub, five cherry children). -/

/-- The exact tie identity `log(23/18) + 5·log(3/2) = 11·F*`, i.e. `(23/18)·(3/2)⁵ = 621/64`. -/
theorem tie_identity_d6 : Real.log (23 / 18) + 5 * Real.log (3 / 2) = 11 * FSTAR := by
  rw [FSTAR]
  have h : Real.log (23 / 18) + 5 * Real.log (3 / 2) = Real.log (621 / 64) := by
    rw [show (621 / 64 : ℝ) = (23 / 18) * (3 / 2) ^ (5 : ℕ) by norm_num,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h]; ring

/-- **`subaction_tail_tie_d6`** — the 27·23 tie cell.  A degree-6 hub whose five children are all the cherry
    `node [leaf]` (deg-2, `bY = 1/3`, `ρwit = 2F*−log(3/2)`); the hub has `ρwit = 0` (deg ≥ 5).  `(SUB)` holds
    with EXACT equality: `log(23/18) − F* = 5·(2F*−log(3/2))`, the `621 = 27·23` face in the tail. -/
theorem subaction_tail_tie_d6 :
    (Real.log (1 + (([Branch.node [Branch.node []], Branch.node [Branch.node []],
        Branch.node [Branch.node []], Branch.node [Branch.node []],
        Branch.node [Branch.node []]]).map bY).sum
        / ((([Branch.node [Branch.node []], Branch.node [Branch.node []],
            Branch.node [Branch.node []], Branch.node [Branch.node []],
            Branch.node [Branch.node []]] : List Branch).length : ℝ) + 1)) - FSTAR)
      + ρwit (Branch.node [Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []], Branch.node [Branch.node []], Branch.node [Branch.node []]])
      ≤ (([Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []], Branch.node [Branch.node []],
          Branch.node [Branch.node []]]).map ρwit).sum := by
  -- cherry message and ρ (as in subaction_cherry)
  have hbYc : bY (Branch.node [Branch.node []]) = 1 / 3 := by
    rw [bY_node]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, bY_leaf, Nat.cast_one, add_zero, zero_add]
    norm_num
  have hrc : ρwit (Branch.node [Branch.node []]) = 2 * FSTAR - Real.log (3 / 2) := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil, hbYc]; ring
  -- node has bcc = 5 ⇒ ρwit = 0
  have hrnode : ρwit (Branch.node [Branch.node [Branch.node []], Branch.node [Branch.node []],
      Branch.node [Branch.node []], Branch.node [Branch.node []], Branch.node [Branch.node []]]) = 0 := by
    rw [ρwit]; simp only [bcc, List.length_cons, List.length_nil]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, hbYc, hrc, hrnode, add_zero, Nat.reduceAdd, Nat.cast_ofNat]
  rw [show (1 : ℝ) + (1 / 3 + (1 / 3 + (1 / 3 + (1 / 3 + 1 / 3)))) / ((5 : ℝ) + 1) = 23 / 18 by norm_num]
  have hid := tie_identity_d6
  linarith

end BGSCL
end R3Cert
