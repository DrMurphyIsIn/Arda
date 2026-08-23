import R3Cert.Sweep
import R3Cert.NearStar
import R3Cert.PotentialGVal

/-!
  # R7 collapse point-floor at the knee — mixed `a=1` class (G7 assembly input) — 2026-08-22

  The `point-floor` input to the `m ≥ 4` collapse composition: the full slack at the real knee
  `T0 = ρB − 1` is `≥` the class floor.  For the **mixed `a=1`** class (`p = 1+2a+nl = 3`,
  `c0 = a/3+nl = 1/3`, `k = a+nl+m = 1+m`, floor `27/5000`), the collapse cavity

      u(m) = (1/3 + m·T0) / (m + 2)

  sits **below the knee** (`u(m) < T0`, since `T0 > 1/6` from `rhoB > 1229/1000`), so
  `log(1+u) < log(1+T0) = log ρB = Lval`.  Hence

      3·Lval − log(3/2) − log(1+u)  >  2·Lval − log(3/2)  =  −omegaVal  >  77/10000  >  27/5000,

  reusing R3Cert's own `omega_enclosure` (`omegaVal = log(3/2) − 2·Lval < −77/10000`).  No new
  transcendental bound is needed — the whole point fact is `linarith` over the existing constant
  enclosures.  `m`-uniform (the collapse tail, `∀ m ≥ 4`); the assembly composes this with
  `slk_min_at_T0` + the profile→equal floor.  `conjecture1_proved = False`.
-/

namespace R3Cert

/-- **Point-floor, mixed `a=1` collapse class.**  For every `m ≥ 4`, the full slack at the knee
    `T0 = ρB − 1` (`p=3, c0=1/3, k=1+m`) is at least the class floor `27/5000`. -/
theorem point_floor_mixed_a1 (m : ℕ) (hm : 4 ≤ m) :
    (27 : ℝ) / 5000 ≤
      3 * Lval - Real.log (3 / 2)
        - Real.log (1 + (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2)) := by
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  -- T0 = ρB − 1 > 1/6
  have hT0 : (1 : ℝ) / 6 < rhoB - 1 := by have := rhoB_gt_1229; linarith
  -- the collapse cavity is below the knee: u(m) < T0
  have hu : (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2) < rhoB - 1 := by
    rw [div_lt_iff₀ hden]; nlinarith [hT0]
  have hunn : (0 : ℝ) ≤ (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2) :=
    div_nonneg (by nlinarith [hT0, hmr]) (by linarith)
  have h1u : (0 : ℝ) < 1 + (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2) := by linarith
  have hlt : 1 + (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2) < rhoB := by linarith [hu]
  -- log(1+u) < log ρB = Lval
  have hlog : Real.log (1 + (1 / 3 + (m : ℝ) * (rhoB - 1)) / ((m : ℝ) + 2)) < Lval := by
    rw [← logRhoB]; exact Real.log_lt_log h1u hlt
  -- omegaVal = log(3/2) − 2·Lval < −77/10000
  have homega : Real.log (3 / 2) - 2 * Lval < -77 / 10000 := by
    have h := omega_enclosure.2; unfold omegaVal at h; exact h
  linarith [hlog, homega]

end R3Cert
