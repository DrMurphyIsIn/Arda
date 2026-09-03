/-
  The additive SUBACTION bridge + first compact-core cell (2026-09-02).

  Companion to `BGSCLGStepBridge`.  It replaces the (REFUTED) multiplicative capped-product step by the
  ADDITIVE ergodic-optimization SUBACTION.  Since `bell b = Σ_v e_v` telescopes (`bell_node`), a subaction
  `ρ ≥ 0` satisfying the per-vertex inequality  `e_v + ρ(v) ≤ Σ_{child c} ρ(c)`  gives, by strong induction,
  `bell b ≤ −ρ(root) ≤ 0` — the branch ceiling.  Being a SUM (not a product), it structurally CANNOT incur the
  multiplicative overshoot that makes the capped-product step `Le1Step` FALSE
  (see `proof/docs/BG_LE1STEP_REFUTED_20260902.md`, `proof/docs/BG_CEILING_SUBACTION_20260902.md`).

  * `ceiling_of_subaction` — the bridge, sorry-free: `(ρ≥0 ∧ IsSubaction ρ) → ∀ b, bell b ≤ 0`.
  * `subaction_cell_broom_d4` — the FIRST compact-core cell of the empirically-verified affine-per-degree
    witness (`ρ(leaf)=F*`, `ρ(deg≥4)=0`) against the kernel: the degree-4 all-leaf (broom) corner, whose
    `(SUB)` content is `log(7/4) ≤ 4·F*`, discharged by log-monotonicity + `norm_num` on the rational
    `(7/4)^11 ≤ (621/64)^4`.  This is the message-endpoint corner (all children at the maximal message `y=1`).

  This is a WITNESS + a reduction, NOT a closed ceiling: the full per-cell certificate family over the
  compact deg-≤6 core (each an affine-in-μ endpoint check + a `log(1+S/d)` enclosure) and the high-degree tail
  lemma remain to be discharged.  No `sorry` here.  `conjecture1_proved = False`.
-/
import Mathlib
import R3Cert.BGSCLInduction

namespace R3Cert
namespace BGSCL

open Real

/-- **The additive subaction inequality (SUB).**  A function `ρ : Branch → ℝ` is a *subaction* when, at every
    hub `node cs`, the local excess `e = log(1 + (Σ_c y_c)/d) − F*` (`d = |cs|+1`, `y_c = bY c`) plus the hub's
    own `ρ` is dominated by the children's `ρ`-sum.  For `cs = []` this specializes to `−F* + ρ(leaf) ≤ 0`,
    i.e. `ρ(leaf) ≤ F*`.  The `log(...) − FSTAR` term is exactly `bell_node`'s local excess, so summing `(SUB)`
    over a branch telescopes to `bell b ≤ −ρ(root)`. -/
def IsSubaction (ρ : Branch → ℝ) : Prop :=
  ∀ cs : List Branch,
    (Real.log (1 + (cs.map bY).sum / ((cs.length : ℝ) + 1)) - FSTAR) + ρ (Branch.node cs)
      ≤ (cs.map ρ).sum

/-- **The additive SUBACTION bridge.**  If `ρ ≥ 0` is a subaction, the whole branch ceiling `∀ b, bell b ≤ 0`
    holds.  Additive analog of `ceiling_of_gstep`: the per-vertex inequality is a SUM, so `Σ_v e_v = bell b`
    telescopes against `−ρ(root) ≤ 0` with no multiplicative overshoot.  Proof: `scl_of_child_step` strong
    induction with the invariant `bell b + ρ b ≤ 0`; the hub step is exactly `(SUB)` plus the child IH sum. -/
theorem ceiling_of_subaction (ρ : Branch → ℝ)
    (hSUB : IsSubaction ρ) (hρ : ∀ b, 0 ≤ ρ b) :
    ∀ b, bell b ≤ 0 := by
  -- `Σ_c (bell c + ρ c) = Σ_c bell c + Σ_c ρ c`
  have hsplit : ∀ l : List Branch,
      (l.map (fun c => bell c + ρ c)).sum = (l.map bell).sum + (l.map ρ).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  -- strengthened invariant `bell b + ρ b ≤ 0`
  have key : ∀ b, bell b + ρ b ≤ 0 := by
    refine scl_of_child_step bsize bchildren (fun b => bell b + ρ b ≤ 0) bchildren_bsize_lt ?_
    intro a hIH
    cases a with
    | node cs =>
        have hsum : (cs.map (fun c => bell c + ρ c)).sum ≤ 0 := by
          refine list_sum_nonpos ?_
          intro x hx; rw [List.mem_map] at hx; obtain ⟨c, hc, rfl⟩ := hx
          exact hIH c (by simpa [bchildren] using hc)
        rw [hsplit] at hsum
        have hsub := hSUB cs
        rw [bell_node]
        linarith
  intro b
  have h1 := key b
  have h2 := hρ b
  linarith

/-! ### First compact-core cell of the verified witness against the kernel. -/

/-- `bY(leaf) = 1` for the leaf `node []` (the maximal message). -/
theorem bY_leaf : bY (Branch.node []) = 1 := by
  simp [bY, bh, bcc, cav, cavAgg]

/-- The 3-leaf child list of the degree-4 broom vertex has message-sum `3` and length `3` — grounding the
    cell's `(SUB)` numerics (`log(1 + 3/4) = log(7/4)`, RHS `= 3·F*`). -/
theorem broom_d4_children_eval :
    (([Branch.node [], Branch.node [], Branch.node []] : List Branch).map bY).sum = 3
    ∧ ([Branch.node [], Branch.node [], Branch.node []] : List Branch).length = 3 := by
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bY_leaf]; norm_num
  · simp

/-- `log(7/4) ≤ 4·F*` — the analytic content of the degree-4 broom cell, via log-monotonicity reduced to the
    rational `(7/4)^11 ≤ (621/64)^4` (`norm_num`).  `F* = log(621/64)/11`. -/
theorem log74_le_4fstar : Real.log (7/4 : ℝ) ≤ 4 * FSTAR := by
  rw [FSTAR]
  have key : 11 * Real.log (7/4 : ℝ) ≤ 4 * Real.log (621/64 : ℝ) := by
    have e1 : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) = 11 * Real.log (7/4 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have e2 : Real.log ((621/64 : ℝ) ^ (4 : ℕ)) = 4 * Real.log (621/64 : ℝ) := by
      rw [Real.log_pow]; norm_num
    have hle : Real.log ((7/4 : ℝ) ^ (11 : ℕ)) ≤ Real.log ((621/64 : ℝ) ^ (4 : ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [e1, e2] at hle; exact hle
  linarith

/-- **POC — the first compact-core cell of the witness against the kernel.**  The subaction inequality `(SUB)`
    at the degree-4 broom vertex (children = three leaves, all at the maximal message `y=1`), with the verified
    affine-per-degree witness `ρ(broom)=0`, `ρ(leaf)=F*`:  `(log(1 + 3/4) − F*) + 0 ≤ 3·F*`.  This is the
    all-children-maximal endpoint corner; the `log` is discharged exactly by `log74_le_4fstar`.  Kernel-checked,
    no `sorry`. -/
theorem subaction_cell_broom_d4 :
    (Real.log (1 + 3 / ((3 : ℝ) + 1)) - FSTAR) + (0 : ℝ) ≤ 3 * FSTAR := by
  have h74 : (1 + 3 / ((3 : ℝ) + 1)) = 7 / 4 := by norm_num
  rw [h74]
  have := log74_le_4fstar
  linarith

/-! ### The first TIGHT compact-core cell (deg-4 hub, deg-3 children) — tangent-endpoint + log-enclosure. -/

/-- The (rational, tie-free) degree-3 line of the verified witness, `ρ₃(μ) = (1/8)(μ − 1/5)`.  With
    `ρ(leaf)=F*`, `ρ(2,μ)=2F*−log(3/2)+(1/4)(μ−1/3)`, `ρ(3,·)=ρ₃`, `ρ(deg≥4)=0`, the subaction holds globally
    (checked on all branches `n≤14`); `ρ₃` is the piece the deg-4 tight cell exercises. -/
noncomputable def ρ3 (μ : ℝ) : ℝ := (1 / 8) * (μ - 1 / 5)

/-- **Log-enclosure** `log(5/4) − F* ≤ 1/20`, via `log x ≤ x − 1` at `x = (5/4)^11·(64/621) ≈ 1.20`
    (so `log x ≤ x−1 ≈ 0.20 ≤ 11/20`, all rational after clearing the `11·F* = log(621/64)`).  This is the
    analytic content the deg-4/deg-3 tight cell rests on (kin to the parallel session's
    `TranscendentalEnclosureEmitter`). -/
theorem log54_sub_fstar_le : Real.log (5 / 4 : ℝ) - FSTAR ≤ 1 / 20 := by
  rw [FSTAR]
  have hpos : (0 : ℝ) < (5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621) := by positivity
  have hr := Real.log_le_sub_one_of_pos hpos
  have hsplit : Real.log ((5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621))
      = 11 * Real.log (5 / 4) - Real.log (621 / 64) := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow,
        show (64 / 621 : ℝ) = (621 / 64)⁻¹ by norm_num, Real.log_inv]
    push_cast; ring
  rw [hsplit] at hr
  have hnum : (5 / 4 : ℝ) ^ (11 : ℕ) * (64 / 621) - 1 ≤ 11 / 20 := by norm_num
  linarith

/-- **POC — the first TIGHT compact-core cell (degree-4 hub with three degree-3 children).**  The subaction
    inequality `(SUB)` at a degree-4 vertex (`ρ = 0`) whose three children are degree-3 with messages
    `y_i ∈ [1/5, 1/3]` (`ρ(3,·) = ρ₃`):  `(log(1 + (Σy)/4) − F*) + 0 ≤ Σ ρ₃(y_i)`.  This is the binding cell
    class (margin ≈ 0.033), far tighter than the broom corner.  The proof is the two tools the whole
    certificate family needs: the CONCAVE-LOG TANGENT at the aggregate endpoint `S = 1` (`log_tangent`, which
    collapses the 3-variable child-message box to the message endpoint — the analytic form of ①'s
    affine-endpoint / the `CurvatureBoundaryEmitter`), plus the LOG-ENCLOSURE `log(5/4) − F* ≤ 1/20`.
    Kernel-checked, no `sorry`. -/
theorem subaction_cell_d4_d3 (y1 y2 y3 : ℝ)
    (h1 : 1 / 5 ≤ y1) (h1' : y1 ≤ 1 / 3) (h2 : 1 / 5 ≤ y2) (h2' : y2 ≤ 1 / 3)
    (h3 : 1 / 5 ≤ y3) (h3' : y3 ≤ 1 / 3) :
    (Real.log (1 + (y1 + y2 + y3) / 4) - FSTAR) + 0 ≤ ρ3 y1 + ρ3 y2 + ρ3 y3 := by
  have hS0 : (0 : ℝ) ≤ y1 + y2 + y3 := by linarith
  have hS1 : y1 + y2 + y3 ≤ 1 := by linarith
  -- tangent of the concave `log(1 + S/4)` at the aggregate endpoint S = 1
  have htan := log_tangent (d := (4 : ℝ)) (s := y1 + y2 + y3) (s0 := (1 : ℝ))
    (by norm_num) hS0 (by norm_num)
  rw [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num, show (4 : ℝ) + 1 = 5 by norm_num] at htan
  have henc := log54_sub_fstar_le
  simp only [ρ3]
  linarith

end BGSCL
end R3Cert
