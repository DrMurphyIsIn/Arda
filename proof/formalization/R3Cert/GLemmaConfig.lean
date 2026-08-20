import R3Cert.CappedJointConfig

/-!
  # g-lemma inductive step, config-based (⚠ DEPRECATED hypothesis, 2026-08-20)

  **⚠ HONESTY CORRECTION.** This step is conditional on `CappedJointConfig.Case2Property`, which
  was believed satisfiable when this file was written but is in fact **FALSE** (it admits child
  messages `μ ∈ (1/2,1)`, unrealizable by the cavity recursion, where the g-step exceeds `1`; see
  `CappedJointConfig` / `CappedJointAchievable`). So `glemma_step_config` is a valid theorem whose
  hypothesis can never be discharged. **Use the achievability-corrected bridge
  `CappedJointAchievable.gstep_le_one_of_glemmaBound`** (general arity) with the unconditionally
  proven `single_child_le_one` / `two_child_le_one` instead. Retained only for continuity.

  Content (unchanged): given a config `l` and child-factor product `PF ≤ prodBcap l`, the node's
  g-lemma holds in normalized form `W·baseOf(l)¹¹·PF ≤ γ = W²(5/3)¹¹`, via the config
  `gstep_le_one`.  (Cavity bridge to the raw `g(B) = F_B·(1+μ_B/3)¹¹`: identity `gstep_base` +
  the `F_B = W·a_B¹¹·PF` recursion, `baseOf l = (1+μ_B/3)·a_B`.)  `conjecture1_proved = False`.
-/

namespace R3Cert.GLemmaConfig

open R3Cert.GStepCore R3Cert.CappedJointConfig

/-- **⚠ DEPRECATED — conditional on the FALSE `CappedJointConfig.Case2Property`.** For a config
    `l` and any child-product `PF ≤ prodBcap l`, `W·baseOf(l)¹¹·PF ≤ γ`. Valid, but the
    `Case2Property` hypothesis is false, so undischargeable. Superseded by
    `CappedJointAchievable.gstep_le_one_of_glemmaBound`. Retained for continuity. -/
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
