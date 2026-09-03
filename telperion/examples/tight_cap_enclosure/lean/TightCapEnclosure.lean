/- telperion 0.1.6 | family TightCapEnclosure | input-hash a80d049d39ae2b61
   2 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace TightCapEnclosure

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

-- CONCRETE g-step tight-cap enclosure for the named config [1/3, 1/3, 1/3, 1/3, 1/3].
-- The whole LHS is a concrete rational; norm_num over the unfolded defs closes it.
-- (fixed-config cert_jk / tie face — NOT the general-arity g-lemma.)
theorem tie_cherry_d6 :
    (baseOf [1/3, 1/3, 1/3, 1/3, 1/3]) ^ 11 * prodBcap [1/3, 1/3, 1/3, 1/3, 1/3]
      / (W * (5 / 3) ^ 11) ≤ 1 := by
  norm_num [baseOf, prodBcap, Bcap, master_ub, glemma, W, List.map,
    List.prod, List.sum, List.length, List.foldr]

-- SYMBOLIC single non-leaf child over the box 0 < μ ≤ 1/2 (the arm face).
-- Mirrors R3Cert.CappedJointAchievable.single_child_le_one EXACTLY:
--   baseOf[μ]¹¹·glemma μ = W²(5/3)¹¹·((7+3μ)/(2(3+μ)))¹¹,
--   (7+3μ)/(2(3+μ)) ≤ 17/14 on [0,1/2], and W·(17/14)¹¹ ≤ 1.
theorem single_child_box (μ : ℚ) (h0 : 0 < μ) (h1 : μ ≤ 1 / 2) :
    (baseOf [μ]) ^ 11 * prodBcap [μ] / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hμ0 : (0 : ℚ) ≤ μ := le_of_lt h0
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hbase : baseOf [μ] = (7 + 3 * μ) / 6 := by
    unfold baseOf
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    push_cast; ring
  have hprod : prodBcap [μ] = Bcap μ := by simp [prodBcap]
  have hb11 : (0 : ℚ) ≤ (baseOf [μ]) ^ 11 := by rw [hbase]; positivity
  have hBle : Bcap μ ≤ glemma μ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hreduce : (baseOf [μ]) ^ 11 * glemma μ
      = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := by
    have hden1 : (1 : ℚ) + μ / 3 ≠ 0 := by positivity
    have h3 : (3 : ℚ) + μ ≠ 0 := by positivity
    rw [hbase, glemma]; field_simp; ring
  have hrle : (7 + 3 * μ) / (2 * (3 + μ)) ≤ 17/14 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hcert : W * (17/14 : ℚ) ^ 11 ≤ 1 := by norm_num [W]
  have hcap : W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 ≤ 1 := by
    have hWnn : (0 : ℚ) ≤ W := by norm_num [W]
    refine le_trans ?_ hcert
    apply mul_le_mul_of_nonneg_left _ hWnn
    gcongr
  rw [div_le_one hden, hprod]
  calc (baseOf [μ]) ^ 11 * Bcap μ
      ≤ (baseOf [μ]) ^ 11 * glemma μ :=
        mul_le_mul_of_nonneg_left hBle hb11
    _ = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := hreduce
    _ = (W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11) * (W * (5 / 3) ^ 11) := by ring
    _ ≤ 1 * (W * (5 / 3) ^ 11) :=
        mul_le_mul_of_nonneg_right hcap (le_of_lt hden)
    _ = W * (5 / 3) ^ 11 := one_mul _

end TightCapEnclosure
