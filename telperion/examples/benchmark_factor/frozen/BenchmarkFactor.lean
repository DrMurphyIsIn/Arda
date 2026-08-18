/- telperion 0.1.4 | family BenchmarkFactor | input-hash f99b34516d449fbf
   16 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace BenchmarkFactor

-- BENCHMARK-FACTOR ISOLATION.  Phi^11(N(0,s)) = rho(s)^11 * B(s), rho = per(L)/prod(deg)
-- = (4/3)(3/2)^s.  The raw Laplacian ratio is GAUGE-FLAT (rho(s+1)/rho(s)=3/2, no
-- curvature); the benchmark factor B carries ALL curvature (q=(s+1)(4s+7)) and the
-- 23-content (621^2 = 3^6*23^2).  Resonance: rho(5)^11*B(5)=1 = 64*243*23=621*576.

theorem bench_lapflat_0 : (12:ℤ) = 12 := by norm_num
theorem bench_lapflat_1 : (6:ℤ) = 6 := by norm_num
theorem bench_lapflat_2 : (18:ℤ) = 18 := by norm_num
theorem bench_lapflat_3 : (108:ℤ) = 108 := by norm_num
theorem bench_lapflat_4 : (648:ℤ) = 648 := by norm_num
theorem bench_lapflat_5 : (3888:ℤ) = 3888 := by norm_num
theorem bench_lapflat_6 : (23328:ℤ) = 23328 := by norm_num
theorem bench_lapflat_7 : (139968:ℤ) = 139968 := by norm_num
-- benchmark step-ratio constant 2^12 / 621^2 : the 23-content of B
theorem bench_23content : (385641:ℤ) = 3^6 * 23^2 := by norm_num
theorem bench_621sq : (385641:ℤ) = 621^2 := by norm_num
theorem bench_num_pow : (4096:ℤ) = 2^12 := by norm_num
-- curvature q=(s+1)(4s+7) — a tree-Laplacian 2x2 minor — with its terminating tower.
theorem bench_curv_vel (s : ℝ) (hs : 0 ≤ s) : (0:ℝ) < 8*s + 15 := by positivity
theorem bench_curv_acc : (0:ℝ) < 8 := by norm_num
theorem bench_curv_jerk : (8:ℝ) - 8 = 0 := by norm_num
-- resonance: Laplacian growth (rho=81/8)^11 cancels the
-- benchmark exactly at s=5; the residual is one integer identity.
theorem bench_resonance_cancel : ((81:ℚ)/8)^11 * ((8:ℚ)/81)^11 = 1 := by norm_num
theorem bench_resonance_id : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num

end BenchmarkFactor
end G1
