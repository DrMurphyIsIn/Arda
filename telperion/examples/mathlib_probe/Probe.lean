/- PROBE 5: the crux split identity for residue_logDeriv --
   logDeriv ((·-z0)^n • g) w = n/(w-z0) + logDeriv g w  for w != z0, g w != 0.
   Verify A4's suggested names + full logDeriv_mul signature. -/
import Mathlib
open Filter Topology

set_option pp.numericTypes true in
#check @logDeriv_mul
#check @logDeriv_congr_nhdsNE
#check @logDeriv_fun_zpow
#check @logDeriv_zpow
#check @logDeriv_sub_const
#check @DifferentiableAt.logDeriv_ne  -- guess

-- the split identity (the crux). g differentiable at w, g w != 0, w != z0.
example (g : ℂ → ℂ) (z₀ w : ℂ) (n : ℤ) (hw : w ≠ z₀) (hg : DifferentiableAt ℂ g w) (hgw : g w ≠ 0) :
    logDeriv (fun z => (z - z₀) ^ n • g z) w = (n : ℂ) / (w - z₀) + logDeriv g w := by
  have hbase : (fun z : ℂ => (z - z₀) ^ n • g z) = (fun z => (z - z₀) ^ n * g z) := by
    funext z; simp [smul_eq_mul]
  rw [hbase]
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (z - z₀) ^ n) w :=
    ((differentiableAt_id'.sub_const z₀).zpow (Or.inl (sub_ne_zero.mpr hw)))
  have hpne : (w - z₀) ^ n ≠ 0 := zpow_ne_zero _ (sub_ne_zero.mpr hw)
  rw [logDeriv_mul w hpne hgw hpow hg]
  congr 1
  -- logDeriv (fun z => (z-z0)^n) w = n/(w-z0)
  rw [show (fun z : ℂ => (z - z₀) ^ n) = (fun z => z ^ n) ∘ (fun z => z - z₀) from rfl]
  sorry
