import R3Cert.R7CollapseT0
import R3Cert.R7CollapsePointFloor

/-!
  # R7 collapse composition — mixed `a=1` full slack ≥ floor over all cavities (G7) — 2026-08-22

  Composes the three collapse-assembly inputs into the per-class floor for the **mixed `a=1`**
  class (`p=3`, `a=1`, `k=1+m`, `c0=1/3`, `t=T0=ρB−1`, floor `27/5000`):

    `full_slack m y = 3·Lval − log(3/2) + slk m (1+m) (1/3) (ρB−1) y`   (equal children at cavity `y`)

  The `y`-independent class constant `3·Lval − log(3/2)` preserves the argmin, so
  `slk_min_at_T0` (min of `slk` at the real knee) lifts to `full_slack`, and the certified
  point-floor `point_floor_mixed_a1` (`full_slack(T0) ≥ 27/5000`) then holds for ALL `y ≥ 0`:

    `full_slack m y  ≥  full_slack m (ρB−1)  ≥  27/5000`    (`∀ m ≥ 4`).

  This closes the `y`-minimisation half of the mixed-`a=1` collapse floor end-to-end in Lean
  (equal-children profiles). The remaining step — lifting arbitrary UNEQUAL child profiles to the
  equal case — is the profile→equal `hinge_profile_floor` (Finset posPart subadditivity), composed
  on top via `Σφ(y_c) ≥ k·φ(ȳ)`; see follow-up. `conjecture1_proved = False`.
-/

namespace R3Cert.R7CollapseMono

/-- Full slack of the mixed `a=1` collapse class with `m` equal children at cavity `y`
    (`p·Lval − a·log(3/2)` constant `+ slk`, `p=3, a=1, k=1+m, c0=1/3, t=ρB−1`). -/
noncomputable def full_slack (m : ℕ) (y : ℝ) : ℝ :=
  3 * Lval - Real.log (3 / 2) + slk m (1 + m) (1 / 3) (rhoB - 1) y

/-- `full_slack m (ρB−1)` equals the point-floor's RHS (the `slk` hinge term vanishes at `y=T0`,
    and `↑(1+m)+1 = ↑m+2`). -/
theorem full_slack_at_knee (m : ℕ) : full_slack m (rhoB - 1)
    = 3 * Lval - Real.log (3 / 2)
        - Real.log (1 + (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2)) := by
  have hden : ((1 + m : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
  unfold full_slack slk
  rw [sub_self, max_self, mul_zero, add_zero, hden]
  ring

/-- **Mixed `a=1` collapse floor over all cavities.** For every `m ≥ 4` and `y ≥ 0`, the full slack
    of the mixed `a=1` class with `m` equal children at cavity `y` is at least the floor `27/5000`.
    Composes `slk_min_at_T0` (min at the real knee) with `point_floor_mixed_a1` (the point floor). -/
theorem full_slack_ge_floor (m : ℕ) (hm : 4 ≤ m) (y : ℝ) (hy : 0 ≤ y) :
    (27 : ℝ) / 5000 ≤ full_slack m y := by
  have hpt : (27 : ℝ) / 5000 ≤ full_slack m (rhoB - 1) := by
    rw [full_slack_at_knee]; exact point_floor_mixed_a1 m hm
  have hmin := slk_min_at_T0 m (1 + m) hm (Nat.le_add_left m 1) (1 / 3) (by norm_num) y hy
  have hmono : full_slack m (rhoB - 1) ≤ full_slack m y := by
    unfold full_slack; linarith [hmin]
  linarith [hpt, hmono]

end R3Cert.R7CollapseMono
