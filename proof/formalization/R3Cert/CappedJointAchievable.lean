import R3Cert.CappedJointConfig
import R3Cert.GStepCore

/-!
  # Achievability-corrected Case 2 + the single non-leaf child (discharged)

  `R3Cert.CappedJointConfig.Case2Property` is FALSE as stated: it quantifies the
  child messages only as `0 < μ`, with **no upper bound**, but the g-step factor
  `baseOf(l)^11 · ∏Bcap / (W(5/3)^11)` exceeds `1` for a single child message
  `μ ∈ [279/400, 399/400] ⊂ (1/2, 1)` (peak `≈ 1.076` at `μ = 13/16`).  That band
  is a GAP the cavity recursion cannot realize: every child message is
  `μ = 1/(j+1+S)`, so a leaf (`j=0`) has `μ = 1` and every non-leaf (`j ≥ 1`) has
  `μ ≤ 1/2`.  (Exact-enumeration cross-check: all 16,755 rooted vertices with
  `n ≤ 10` have max non-leaf message `17/35 < 1/2`.)

  Adding the achievability hypothesis `μ ≤ 1/2 ∨ μ = 1` makes the statement true.
  This file records the corrected predicate `Case2PropertyAchievable` and
  DISCHARGES the single non-leaf child (`|l| = 1`, `μ ≤ 1/2`) unconditionally, by
  the exact reduction `gstep([μ]) = W·((7+3μ)/(2(3+μ)))^11` and the kernel-green
  `GStepCore.frac_j1` (monotone cap `≤ 17/14`) + `GStepCore.cert_j1`
  (`W(17/14)^11 ≤ 1`).  Equality holds only at the arm.  `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore

/-- A child message is **achievable** iff it is the leaf (`= 1`) or a non-leaf
    (`≤ 1/2`).  The recursion realizes no `μ ∈ (1/2, 1)`. -/
def Achievable (μ : ℚ) : Prop := 0 < μ ∧ (μ ≤ 1 / 2 ∨ μ = 1)

/-- **Corrected Case 2** — the achievability-constrained open hypothesis (true,
    unlike the unconstrained `Case2Property`, which is false in `(1/2,1)`). -/
def Case2PropertyAchievable : Prop :=
  ∀ l : List ℚ, (∀ μ ∈ l, Achievable μ) → W * (5 / 3) ^ 11 < (baseOf l) ^ 11 →
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1

/-- `Bcap ≤ glemma` (Bcap is a `min` whose right branch is `min glemma 1`). -/
theorem Bcap_le_glemma (μ : ℚ) : Bcap μ ≤ glemma μ := by
  unfold Bcap
  exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- `baseOf [μ] = (7+3μ)/6` — the single-child hub base. -/
theorem baseOf_singleton (μ : ℚ) : baseOf [μ] = (7 + 3 * μ) / 6 := by
  unfold baseOf
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- `prodBcap [μ] = Bcap μ`. -/
theorem prodBcap_singleton (μ : ℚ) : prodBcap [μ] = Bcap μ := by
  simp [prodBcap]

/-- **The exact single-child reduction** (product form, no division).
    `baseOf [μ]^11 · glemma μ = W²(5/3)^11 · ((7+3μ)/(2(3+μ)))^11`. -/
theorem single_child_reduce {μ : ℚ} (h0 : 0 < μ) :
    (baseOf [μ]) ^ 11 * glemma μ
      = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := by
  have hden : (1 : ℚ) + μ / 3 ≠ 0 := by positivity
  have h3 : (3 : ℚ) + μ ≠ 0 := by positivity
  rw [baseOf_singleton, glemma]
  field_simp
  ring

/-- **Single non-leaf child, discharged.** For `0 < μ ≤ 1/2` the g-step factor is
    `≤ 1`, unconditionally — reduced to `frac_j1` + `cert_j1`.  No `Case2Property`
    hypothesis is used, so this is a genuine shrink of the open crux. -/
theorem single_child_le_one {μ : ℚ} (h0 : 0 < μ) (h1 : μ ≤ 1 / 2) :
    (baseOf [μ]) ^ 11 * prodBcap [μ] / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hμ0 : (0 : ℚ) ≤ μ := le_of_lt h0
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hb11 : (0 : ℚ) ≤ (baseOf [μ]) ^ 11 := by
    rw [baseOf_singleton]; positivity
  have hrle : (7 + 3 * μ) / (2 * (3 + μ)) ≤ 17 / 14 := frac_j1 hμ0 h1
  -- the clean fraction is capped ≤ 1 by frac_j1 + cert_j1
  have hcap : W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 ≤ 1 := by
    have hWnn : (0 : ℚ) ≤ W := by norm_num [W]
    refine le_trans ?_ cert_j1
    apply mul_le_mul_of_nonneg_left _ hWnn
    gcongr
  rw [div_le_one hden, prodBcap_singleton]
  calc (baseOf [μ]) ^ 11 * Bcap μ
      ≤ (baseOf [μ]) ^ 11 * glemma μ := mul_le_mul_of_nonneg_left (Bcap_le_glemma μ) hb11
    _ = W ^ 2 * (5 / 3) ^ 11 * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11 := single_child_reduce h0
    _ = (W * ((7 + 3 * μ) / (2 * (3 + μ))) ^ 11) * (W * (5 / 3) ^ 11) := by ring
    _ ≤ 1 * (W * (5 / 3) ^ 11) := mul_le_mul_of_nonneg_right hcap (le_of_lt hden)
    _ = W * (5 / 3) ^ 11 := one_mul _

/-! ### Two non-leaf children — the same elementary path via `frac_q2` + `cert_q2`

  The multi-child case needs NO new positivity certificate (no Handelman/Putinar):
  the two-child g-step reduces, exactly as the single-child one, to a kernel-green
  per-arity primitive.  `gstep([a,b]) = W³(5/3)¹¹·((10+3a+3b)/((3+a)(3+b)))¹¹`, and
  `frac_q2` caps the fraction at `10/9`, so `gstep ≤ W³(50/27)¹¹ = cert_q2 < 1`.
  (General `j` is the g-lemma `gV_le`, already proven in the cavity model.)
-/

/-- `baseOf [a,b] = (10+3a+3b)/9`. -/
theorem baseOf_pair (a b : ℚ) : baseOf [a, b] = (10 + 3 * a + 3 * b) / 9 := by
  unfold baseOf
  simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- `prodBcap [a,b] = Bcap a · Bcap b`. -/
theorem prodBcap_pair (a b : ℚ) : prodBcap [a, b] = Bcap a * Bcap b := by
  simp [prodBcap]

/-- Exact two-child reduction (product form). -/
theorem pair_reduce {a b : ℚ} (h0a : 0 < a) (h0b : 0 < b) :
    (baseOf [a, b]) ^ 11 * (glemma a * glemma b)
      = (W ^ 3 * (5 / 3) ^ 11 * ((10 + 3 * a + 3 * b) / ((3 + a) * (3 + b))) ^ 11)
        * (W * (5 / 3) ^ 11) := by
  have ha3 : (3 : ℚ) + a ≠ 0 := by positivity
  have hb3 : (3 : ℚ) + b ≠ 0 := by positivity
  have hda : (1 : ℚ) + a / 3 ≠ 0 := by positivity
  have hdb : (1 : ℚ) + b / 3 ≠ 0 := by positivity
  rw [baseOf_pair, glemma, glemma]
  field_simp
  ring

/-- **Two children, discharged — with NO achievability constraint.** For any
    `0 < a, b` the g-step factor is `≤ 1`, reduced to `frac_q2` + `cert_q2`.
    Unlike the single-child case, `a, b ≤ 1/2` is **not needed**: `frac_q2` holds
    for all `a, b ≥ 0`.  So the `(1/2,1)` violation — and the whole integrality
    wall — is a `j = 1` (single-child / arm) phenomenon; `j ≥ 2` is unconditional
    and needs no continuous (Handelman) certificate. -/
theorem two_child_le_one {a b : ℚ} (h0a : 0 < a) (h0b : 0 < b) :
    (baseOf [a, b]) ^ 11 * prodBcap [a, b] / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hb11 : (0 : ℚ) ≤ (baseOf [a, b]) ^ 11 := by
    rw [baseOf_pair]; positivity
  have hinner : (10 + 3 * a + 3 * b) / ((3 + a) * (3 + b)) ≤ 10 / 9 :=
    frac_q2 (le_of_lt h0a) (le_of_lt h0b)
  have hcap : W ^ 3 * (5 / 3) ^ 11 * ((10 + 3 * a + 3 * b) / ((3 + a) * (3 + b))) ^ 11 ≤ 1 := by
    have hpow : ((10 + 3 * a + 3 * b) / ((3 + a) * (3 + b))) ^ 11 ≤ (10 / 9) ^ 11 := by
      gcongr
    have hpre : (0 : ℚ) ≤ W ^ 3 * (5 / 3) ^ 11 := by norm_num [W]
    refine le_trans ?_ (le_of_lt cert_q2)
    calc W ^ 3 * (5 / 3) ^ 11 * ((10 + 3 * a + 3 * b) / ((3 + a) * (3 + b))) ^ 11
        ≤ W ^ 3 * (5 / 3) ^ 11 * (10 / 9) ^ 11 := mul_le_mul_of_nonneg_left hpow hpre
      _ = W ^ 3 * (50 / 27) ^ 11 := by rw [mul_assoc, ← mul_pow]; norm_num
  rw [div_le_one hden, prodBcap_pair]
  calc (baseOf [a, b]) ^ 11 * (Bcap a * Bcap b)
      ≤ (baseOf [a, b]) ^ 11 * (glemma a * glemma b) := by
        apply mul_le_mul_of_nonneg_left _ hb11
        exact mul_le_mul (Bcap_le_glemma a) (Bcap_le_glemma b)
          (Bcap_nonneg (le_of_lt h0b)) (glemma_nonneg (le_of_lt h0a))
    _ = (W ^ 3 * (5 / 3) ^ 11 * ((10 + 3 * a + 3 * b) / ((3 + a) * (3 + b))) ^ 11)
          * (W * (5 / 3) ^ 11) := pair_reduce h0a h0b
    _ ≤ 1 * (W * (5 / 3) ^ 11) := mul_le_mul_of_nonneg_right hcap (le_of_lt hden)
    _ = W * (5 / 3) ^ 11 := one_mul _

end R3Cert.CappedJointConfig
