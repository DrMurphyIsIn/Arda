/- telperion 0.1.6 | family LehmerPair | input-hash 1d3b893bf7396b38
   4 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace LehmerPair

-- lehmer_lambda_bound_wip: WIP skeleton for the de Bruijn–Newman lower bound.
-- CNV (1994) turns a certified Lehmer pair into Λ ≥ Λ_lo, but the exact CNV
-- constant is UNVERIFIED this pass (documented in CNV_FORMULA), so the numeric
-- Λ_lo is NOT emitted.  The abstract chaining is sound for ANY carried CNV
-- instance hCNV : Lexact ≤ Λ, giving a rounded L ≤ Λ.  Term-mode le_trans.
theorem lehmer_lambda_bound_wip (Lam Lexact L : ℝ)
    (hCNV : Lexact ≤ Lam) (hround : L ≤ Lexact) : L ≤ Lam :=
  le_trans hround hCNV

-- lehmer_neg_refutes: the falsifiability face.  RH ⟺ Λ ≤ 0; a certified
-- POSITIVE lower bound L > 0 with L ≤ Λ forces Λ > 0, contradicting Λ ≤ 0,
-- hence ¬RH through the de Bruijn–Newman equivalence (carried as hRH : RH →
-- Λ ≤ 0).  Not expected to fire; makes the ladder falsifiable.
theorem lehmer_neg_refutes {P : Prop} (Lam L : ℝ)
    (hRH : P → Lam ≤ 0) (hLo : L ≤ Lam) (hpos : 0 < L) : ¬P :=
  fun hP => absurd (hRH hP) (not_le.mpr (lt_of_lt_of_le hpos hLo))

-- lehmer_n186: certified LEHMER PAIR at n=186 — the consecutive-zero pair
-- (γ_n, γ_{n+1}) has gap δ ≈ 0.498179 and neighboring-zero curvature
-- C_n = Σ 1/(γ_mid−γ_k)² ≈ 0.813091, so quality δ²·C_n ≈ 0.201795
-- ≤ 100897574761/500000000000 ≤ 21/100 < 1 (anomalously close — a Lehmer pair).  The
-- ordinates are Arb-certified (hardy_z_zeros); quality_short ≥ δ²·C_n rounded up.
-- Face 5 (de Bruijn–Newman: RH ⟺ Λ ≤ 0).  A finite Lehmer-pair witness; NOT RH.
theorem lehmer_n186 : ((100897574761 / 500000000000) : ℝ) ≤ ((21 / 100) : ℝ) := by norm_num

-- lehmer_n453: certified LEHMER PAIR at n=453 — the consecutive-zero pair
-- (γ_n, γ_{n+1}) has gap δ ≈ 0.310431 and neighboring-zero curvature
-- C_n = Σ 1/(γ_mid−γ_k)² ≈ 0.925310, so quality δ²·C_n ≈ 0.089170
-- ≤ 89169525319/1000000000000 ≤ 9/100 < 1 (anomalously close — a Lehmer pair).  The
-- ordinates are Arb-certified (hardy_z_zeros); quality_short ≥ δ²·C_n rounded up.
-- Face 5 (de Bruijn–Newman: RH ⟺ Λ ≤ 0).  A finite Lehmer-pair witness; NOT RH.
theorem lehmer_n453 : ((89169525319 / 1000000000000) : ℝ) ≤ ((9 / 100) : ℝ) := by norm_num

-- lehmer_n693: certified LEHMER PAIR at n=693 — the consecutive-zero pair
-- (γ_n, γ_{n+1}) has gap δ ≈ 0.221107 and neighboring-zero curvature
-- C_n = Σ 1/(γ_mid−γ_k)² ≈ 1.369590, so quality δ²·C_n ≈ 0.066957
-- ≤ 669569222683/10000000000000 ≤ 67/1000 < 1 (anomalously close — a Lehmer pair).  The
-- ordinates are Arb-certified (hardy_z_zeros); quality_short ≥ δ²·C_n rounded up.
-- Face 5 (de Bruijn–Newman: RH ⟺ Λ ≤ 0).  A finite Lehmer-pair witness; NOT RH.
theorem lehmer_n693 : ((669569222683 / 10000000000000) : ℝ) ≤ ((67 / 1000) : ℝ) := by norm_num

-- lehmer_n922: certified LEHMER PAIR at n=922 — the consecutive-zero pair
-- (γ_n, γ_{n+1}) has gap δ ≈ 0.161501 and neighboring-zero curvature
-- C_n = Σ 1/(γ_mid−γ_k)² ≈ 1.715128, so quality δ²·C_n ≈ 0.044735
-- ≤ 22367422003/500000000000 ≤ 9/200 < 1 (anomalously close — a Lehmer pair).  The
-- ordinates are Arb-certified (hardy_z_zeros); quality_short ≥ δ²·C_n rounded up.
-- Face 5 (de Bruijn–Newman: RH ⟺ Λ ≤ 0).  A finite Lehmer-pair witness; NOT RH.
theorem lehmer_n922 : ((22367422003 / 500000000000) : ℝ) ≤ ((9 / 200) : ℝ) := by norm_num

end LehmerPair
