import R3Cert.R7CollapseMono
import R3Cert.ExactCruxes
import R3Cert.ChainMargin

/-!
  # R7 collapse min at the REAL knee `T0 = ρB − 1` (G7 assembly brick) — 2026-08-22

  Instantiates the abstract `slk_min_at_knee` (which holds for any threshold `t ≥ 1/5`) at the
  actual collapse knee `T0 = ρB − 1`, discharging the hypothesis `1/5 ≤ T0` from the on-`main`
  bound `17/14 < ρB` (`seventeen_14_lt_rhoB`), since `6/5 ≤ 17/14`. This connects the abstract
  monotonicity to the real hinge constant used by the ledger, so the collapse floor's `y`-min
  is pinned at the genuine `T0`. One brick of the G7 floor assembly. `conjecture1_proved = False`.
-/

namespace R3Cert.R7CollapseMono

/-- `1/5 ≤ T0 = ρB − 1` — the hypothesis needed to instantiate `slk_min_at_knee` at the real knee.
    From `6/5 ≤ 17/14 < ρB` (`seventeen_14_lt_rhoB`), i.e. `(6/5)^11 ≤ 621/64`. -/
theorem one_fifth_le_T0 : (1 / 5 : ℝ) ≤ rhoB - 1 := by
  have h := seventeen_14_lt_rhoB
  have h2 : (6 / 5 : ℝ) ≤ 17 / 14 := by norm_num
  linarith

/-- **Collapse slack min at the real knee `T0 = ρB − 1`.** For `m ≥ 4`, `k ≥ m`, `c0 ≥ 0`, the
    collapse slack over `y ≥ 0` attains its minimum at the actual knee `y = T0`. Instantiates
    `slk_min_at_knee` at `t = ρB − 1`. -/
theorem slk_min_at_T0 (m k : ℕ) (hm : 4 ≤ m) (hk : m ≤ k) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (y : ℝ) (hy : 0 ≤ y) : slk m k c0 (rhoB - 1) (rhoB - 1) ≤ slk m k c0 (rhoB - 1) y :=
  slk_min_at_knee m k hm hk c0 hc0 (rhoB - 1) one_fifth_le_T0 y hy

end R3Cert.R7CollapseMono
