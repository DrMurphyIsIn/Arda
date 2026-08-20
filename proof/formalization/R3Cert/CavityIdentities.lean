import Mathlib

/-!
  # Cavity identities — the recursion→abstract-core bridges (2026-08-20)

  The capped-joint induction's step lemmas (`GStepCore`, `MasterCore`, `CappedJointSkeleton`)
  are stated abstractly in a `base` variable. This file kernel-checks the algebraic identities
  that connect a node's *actual* cavity data to that `base`, so the tree-recursion assembly can
  substitute them.

  A node of degree `j` with children of total cavity message `S` has (`d := j+1`):
    `μ_B = 1/(d+S)`,  `a_B = 1 + S/d`,
  and the step normalizers are:
    **g-step base**   `(1 + μ_B/3)·a_B = (3d+3S+1)/(3d)`   — feeds `gstep_le_one`,
    **master base**   `(2 + μ_B)·a_B   = (2d+2S+1)/d`      — feeds `master_core`.

  Both are unconditional rational identities (`field_simp`+`ring`) given `d>0, S≥0`.  These are
  the same objects a Telperion `IdentityEmitter`/`NullstellensatzEmitter` would emit (the latter
  as ideal membership modulo `μ_B·(d+S)=1`).  Entirely in `ℚ`.  `conjecture1_proved = False`.
-/

namespace R3Cert.CavityIdentities

/-- **g-step base identity.** With `μ_B = 1/(d+S)`, `a_B = 1+S/d`, the g-step normalizer
    `(1 + μ_B/3)·a_B` equals `(3d+3S+1)/(3d)` — the `base` consumed by `gstep_le_one`. -/
theorem gstep_base {d S : ℚ} (hd : 0 < d) (hS : 0 ≤ S) :
    (1 + (1 / (d + S)) / 3) * (1 + S / d) = (3 * d + 3 * S + 1) / (3 * d) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hds : d + S ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **master base identity.** With the same `μ_B, a_B`, the master normalizer
    `(2 + μ_B)·a_B` equals `(2d+2S+1)/d` — the `base` shape behind `master_core`. -/
theorem master_base {d S : ℚ} (hd : 0 < d) (hS : 0 ≤ S) :
    (2 + 1 / (d + S)) * (1 + S / d) = (2 * d + 2 * S + 1) / d := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hds : d + S ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- Positivity of the g-step base — needed downstream (`gstep_le_one` wants `0 ≤ base`). -/
theorem gstep_base_pos {d S : ℚ} (hd : 0 < d) (hS : 0 ≤ S) :
    0 ≤ (3 * d + 3 * S + 1) / (3 * d) := by
  apply div_nonneg <;> linarith

end R3Cert.CavityIdentities
