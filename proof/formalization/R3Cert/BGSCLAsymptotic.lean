import R3Cert.BGSCLSubactionDispatch

/-!
  # The BG asymptotic upper bound `F(T) ≤ F*`, unconditional.

  `F* = log(621/64)/11` is the Brualdi–Goldwasser asymptotic per-vertex log-rate.  The whole
  branch-induction upper-bound program (`telperion/src/telperion/bg_upper_bound.py`) reduces the
  asymptotic bound to the single classical-branch ceiling `bg_ceiling : ∀ b, bell b ≤ 0`, which is
  now UNCONDITIONAL in Lean (via the additive subaction `isSubaction_ρwit`,
  `BGSCLSubactionDispatch.lean`).

  This module packages the immediate consequence.  By definition
  `bell b = Real.log (btotal b) − (bsize b)·FSTAR`, so `bell b ≤ 0` is *exactly* the normalized
  per-vertex rate bound
      `Real.log (btotal b) / (bsize b) ≤ FSTAR`     (`bsize b ≠ 0`, always true since `bsize ≥ 1`),
  i.e. `F(b) ≤ F*` for the branch rate `F(b) = (1/|b|)·log(total b)`.  The asymptotic bound is thus a
  DIRECT COROLLARY of `bg_ceiling` — no extra ledger porting is needed for this leg.

  Scope note.  The python ledger's boundary step [0] (`1 ≤ π(T)/branch_total(T,r) ≤ 4/3`, the
  `O(1/n)` correction relating the tree amplitude `π(T)` to the rooted branch total) is a finite-`n`
  structural fact that is NOT formalized here; it lives on the `Hnorm`/`Hdom` side (out of scope) and
  vanishes asymptotically.  What is delivered here is the per-branch rate bound that carries the
  asymptotics: `log(total b)/|b| ≤ F*` for every rooted branch, with the sharp tie (`= F*` at the
  degree-6 branch) preserved by `bg_ceiling`.  `conjecture1_proved = False`.
-/

namespace R3Cert
namespace BGSCL

/-- Every branch has at least one vertex, so `bsize b ≠ 0` (as a real, `(bsize b : ℝ) ≠ 0`). -/
theorem bsize_ne_zero (b : Branch) : bsize b ≠ 0 := by
  cases b with
  | node cs => simp only [bsize]; omega

theorem bsize_pos (b : Branch) : 0 < bsize b :=
  Nat.pos_of_ne_zero (bsize_ne_zero b)

/-- `(bsize b : ℝ) > 0`. -/
theorem cast_bsize_pos (b : Branch) : (0:ℝ) < (bsize b : ℝ) := by
  exact_mod_cast bsize_pos b

/-- **The asymptotic upper bound, rate form.**  For every rooted branch `b`, the normalized log-rate
    `log(total b)/|b|` is at most `F* = log(621/64)/11`.  This is exactly `bg_ceiling` (`bell b ≤ 0`)
    divided by the (positive) vertex count `|b|`. -/
theorem bg_asymptotic_bound (b : Branch) :
    Real.log (btotal b) / (bsize b : ℝ) ≤ FSTAR := by
  have hpos : (0:ℝ) < (bsize b : ℝ) := cast_bsize_pos b
  have hceil : bell b ≤ 0 := bg_ceiling b
  -- `bell b = log (btotal b) − |b|·FSTAR`, and `btotal b = (cav b).2`.
  have hbell : Real.log (btotal b) - (bsize b : ℝ) * FSTAR ≤ 0 := by
    simpa only [bell, btotal] using hceil
  rw [div_le_iff₀ hpos]
  linarith [hbell]

/-- **The asymptotic upper bound, product/log form.**  `log(total b) ≤ |b|·F*` — the un-normalized
    restatement (avoids the division), i.e. `total b ≤ (621/64)^(|b|/11)`.  Identical content to
    `bg_asymptotic_bound`, packaged for callers that want the sized log inequality. -/
theorem log_btotal_le (b : Branch) :
    Real.log (btotal b) ≤ (bsize b : ℝ) * FSTAR := by
  have hceil : bell b ≤ 0 := bg_ceiling b
  have hbell : Real.log (btotal b) - (bsize b : ℝ) * FSTAR ≤ 0 := by
    simpa only [bell, btotal] using hceil
  linarith [hbell]

/-- **The asymptotic upper bound, exponential form.**  `total b ≤ (621/64)^(|b|/11)`, the amplitude
    bound with the rate written out.  Follows from `log_btotal_le` since `btotal b > 0` and `x ↦ exp x`
    is monotone; `FSTAR = log(621/64)/11`. -/
theorem btotal_le_rpow (b : Branch) :
    btotal b ≤ (621 / 64 : ℝ) ^ ((bsize b : ℝ) / 11) := by
  have hpos : 0 < btotal b := btotal_pos b
  have hbase : (0:ℝ) < 621 / 64 := by norm_num
  have hlog : Real.log (btotal b) ≤ (bsize b : ℝ) * FSTAR := log_btotal_le b
  -- RHS log: log ((621/64) ^ (|b|/11)) = (|b|/11) · log(621/64) = |b|·FSTAR.
  have hrhs_pos : (0:ℝ) < (621 / 64 : ℝ) ^ ((bsize b : ℝ) / 11) := Real.rpow_pos_of_pos hbase _
  have hlog_rhs : Real.log ((621 / 64 : ℝ) ^ ((bsize b : ℝ) / 11))
      = (bsize b : ℝ) * FSTAR := by
    rw [Real.log_rpow hbase]
    unfold FSTAR
    ring
  have : Real.log (btotal b) ≤ Real.log ((621 / 64 : ℝ) ^ ((bsize b : ℝ) / 11)) := by
    rw [hlog_rhs]; exact hlog
  exact (Real.log_le_log_iff hpos hrhs_pos).mp this

end BGSCL
end R3Cert
