/- telperion 0.1.6 | family PerSizeDominanceSweep | input-hash 4703ce0d1bf6060c
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace PerSizeDominanceSweep

/-- Base constant `W = 64/621`. -/
def W : ℚ := 64 / 621
/-- `glemma(μ) = W²(5/3)¹¹/(1+μ/3)¹¹`. -/
def glemma (μ : ℚ) : ℚ := W ^ 2 * (5 / 3) ^ 11 / (1 + μ / 3) ^ 11
/-- `master_ub(μ) = W(3/(2+μ))¹¹`. -/
def master_ub (μ : ℚ) : ℚ := W * (3 / (2 + μ)) ^ 11
/-- `Bcap(μ) = min(master_ub, glemma, 1)` — the per-child three-way-min cap. -/
def Bcap (μ : ℚ) : ℚ := min (master_ub μ) (min (glemma μ) 1)
/-- `baseOf l = (3(|l|+1)+3Σl+1)/(3(|l|+1))` — the g-step base of config `l`. -/
def baseOf (l : List ℚ) : ℚ :=
  (3 * ((l.length : ℚ) + 1) + 3 * l.sum + 1) / (3 * ((l.length : ℚ) + 1))
/-- `prodBcap l = ∏ Bcap(μ)` over the config. -/
def prodBcap (l : List ℚ) : ℚ := (l.map Bcap).prod

-- CONCRETE per-config g-step domination face for [1/3, 1/3, 1/3]
-- (same face as tight_cap_enclosure concrete: whole LHS is a rational;
--  norm_num over the unfolded defs closes it).
theorem sweep_n3_cfg0 :
    (baseOf [1/3, 1/3, 1/3]) ^ 11 * prodBcap [1/3, 1/3, 1/3]
      / (W * (5 / 3) ^ 11) ≤ 1 := by
  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,
    List.prod, List.sum, List.length, List.foldr]

-- CONCRETE per-config g-step domination face for [1/3, 1/2, 1/3]
-- (same face as tight_cap_enclosure concrete: whole LHS is a rational;
--  norm_num over the unfolded defs closes it).
theorem sweep_n3_cfg1 :
    (baseOf [1/3, 1/2, 1/3]) ^ 11 * prodBcap [1/3, 1/2, 1/3]
      / (W * (5 / 3) ^ 11) ≤ 1 := by
  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,
    List.prod, List.sum, List.length, List.foldr]

-- CONCRETE per-config g-step domination face for [1/2, 1/2, 1/3]
-- (same face as tight_cap_enclosure concrete: whole LHS is a rational;
--  norm_num over the unfolded defs closes it).
theorem sweep_n3_cfg2 :
    (baseOf [1/2, 1/2, 1/3]) ^ 11 * prodBcap [1/2, 1/2, 1/3]
      / (W * (5 / 3) ^ 11) ≤ 1 := by
  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,
    List.prod, List.sum, List.length, List.foldr]

-- AGGREGATE per-size sweep over the enumerated config set (size n).
-- Dispatches each membership to its per-config face via List.forall_mem_cons.
-- HONEST SCOPE: finite sweep of the LISTED configs — NOT exhaustive over
-- all size-n normal-form states, and NOT uniform in n.
theorem sweep_n3 :
    ∀ l ∈ ([[1/3, 1/3, 1/3], [1/3, 1/2, 1/3], [1/2, 1/2, 1/3]] : List (List ℚ)),
      (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1 := by
  simp only [List.forall_mem_cons]
  exact ⟨sweep_n3_cfg0, sweep_n3_cfg1, sweep_n3_cfg2, List.forall_mem_nil _⟩

end PerSizeDominanceSweep
