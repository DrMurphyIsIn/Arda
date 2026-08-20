import R3Cert.CappedJointConfig

/-!
  # g-lemma inductive step, config-based (honest, 2026-08-20)

  Re-points `GLemmaAssembly.glemma_step` (which used the DEPRECATED, unsatisfiable abstract
  `Case2Property`) to the corrected `CappedJointConfig` — the config-based, **satisfiable**
  hypothesis. Given a config `l` (child messages) and the child-factor product `PF = ∏F_c`
  bounded by the induction hypothesis `PF ≤ prodBcap l = ∏Bcap(μ_c)`, the node's g-lemma
  holds in normalized form `W·baseOf(l)¹¹·PF ≤ γ = W²(5/3)¹¹`, discharged through the honest
  config `gstep_le_one`.  (The connection to the raw `g(B) = F_B·(1+μ_B/3)¹¹` is the cavity
  identity `gstep_base` + the `F_B = W·a_B¹¹·PF` recursion, `baseOf l = (1+μ_B/3)·a_B`.)
  Conditional only on the satisfiable `CappedJointConfig.Case2Property`.
  `conjecture1_proved = False`.
-/

namespace R3Cert.GLemmaConfig

open R3Cert.GStepCore R3Cert.CappedJointConfig

/-- **g-lemma step (config-based, honest hypothesis).** For an achievable config `l` and any
    child-product `PF ≤ prodBcap l`, `W·baseOf(l)¹¹·PF ≤ γ`. Conditional on the *satisfiable*
    `CappedJointConfig.Case2Property`. -/
theorem glemma_step_config (h2 : Case2Property) (l : List ℚ) (hl : ∀ μ ∈ l, 0 < μ)
    {PF : ℚ} (hPFbc : PF ≤ prodBcap l) :
    W * (baseOf l) ^ 11 * PF ≤ W ^ 2 * (5 / 3) ^ 11 := by
  have hden : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  have hW0 : (0 : ℚ) ≤ W := by norm_num [W]
  have hb0 : 0 ≤ baseOf l := baseOf_nonneg l (fun μ hμ => le_of_lt (hl μ hμ))
  have hb11 : 0 ≤ (baseOf l) ^ 11 := pow_nonneg hb0 11
  have hstep := gstep_le_one h2 l hl
  rw [div_le_one hden] at hstep
  calc W * (baseOf l) ^ 11 * PF
      ≤ W * (baseOf l) ^ 11 * prodBcap l :=
        mul_le_mul_of_nonneg_left hPFbc (mul_nonneg hW0 hb11)
    _ = W * ((baseOf l) ^ 11 * prodBcap l) := by ring
    _ ≤ W * (W * (5 / 3) ^ 11) := mul_le_mul_of_nonneg_left hstep hW0
    _ = W ^ 2 * (5 / 3) ^ 11 := by ring

end R3Cert.GLemmaConfig
