import R3Cert.CappedJointAchievable
import R3Cert.GLemmaAbstract

/-!
  # Closing the config g-step for every arity (assembly bridge → the ported g-lemma)

  Proves `gstep_le_one_achievable`: for every achievable config `l`,
  `baseOf(l)¹¹·prodBcap(l)/(W(5/3)¹¹) ≤ 1`, UNCONDITIONALLY (no `Case2Property`), by
  routing to the ported abstract g-step `G1.ArmExtremality.gstep_lt_gamma`
  (`W·gCoreOff < γ`, `j ≥ 2`) plus the leaf (`|l|=0`) and single-child (`|l|=1`) cases.

  The ℚ config quantities cast to the ℝ abstract ones:
  `baseOf l = boostR l.length l.sum`, `Bcap μ ≤ factorR γ μ = min(1,glemma μ)`,
  and `gCoreOff γ n 0 (l.map ↑) = boostR n l.sum¹¹ · ∏ factorR`.  Constants align:
  `↑W = Wr = 64/621`, `↑(W²(5/3)¹¹) = gammaR`.  `conjecture1_proved = False`.
-/

namespace R3Cert.CappedJointConfig

open R3Cert.GStepCore G1.ArmExtremality G1.GLemma

/-- `↑W = Wr` (both `64/621`). -/
theorem W_cast : ((W : ℚ) : ℝ) = Wr := by
  simp only [W, Wr]; norm_num

/-- `↑(W²(5/3)¹¹) = gammaR`. -/
theorem gamma_cast : ((W ^ 2 * (5 / 3) ^ 11 : ℚ) : ℝ) = gammaR := by
  unfold gammaR
  push_cast [W_cast]
  ring

/-- `↑(glemma μ) = gammaR/(1+↑μ/3)¹¹`. -/
theorem glemma_cast (μ : ℚ) :
    ((glemma μ : ℚ) : ℝ) = gammaR / (1 + ((μ : ℚ) : ℝ) / 3) ^ 11 := by
  unfold glemma gammaR
  push_cast [W_cast]
  ring

/-- `↑(baseOf l) = boostR l.length ↑(l.sum)`. -/
theorem baseOf_cast (l : List ℚ) :
    ((baseOf l : ℚ) : ℝ) = boostR l.length ((l.sum : ℚ) : ℝ) := by
  have h1 : (3 : ℝ) * ((l.length : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (3 : ℝ) * (l.length : ℝ) + 3 ≠ 0 := by positivity
  unfold baseOf boostR
  push_cast
  field_simp
  ring

/-- `Bcap μ ≤ factorR gammaR ↑μ`  (`Bcap ≤ min(glemma,1) = factorR`). -/
theorem Bcap_le_factorR (μ : ℚ) : ((Bcap μ : ℚ) : ℝ) ≤ factorR gammaR ((μ : ℚ) : ℝ) := by
  rw [factorR]
  apply le_min
  · have h := Bcap_le_one μ
    exact_mod_cast h
  · have h : Bcap μ ≤ glemma μ := Bcap_le_glemma μ
    have hc : ((Bcap μ : ℚ) : ℝ) ≤ ((glemma μ : ℚ) : ℝ) := by exact_mod_cast h
    rwa [glemma_cast] at hc

/-- `↑(l.sum) = (l.map ↑).sum`. -/
theorem sum_cast (l : List ℚ) : ((l.sum : ℚ) : ℝ) = (l.map (fun (x : ℚ) => (x : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.sum_cons, ih]

/-- `↑(prodBcap l) ≤ ∏ factorR gammaR ↑μ`. -/
theorem prodBcap_cast_le (l : List ℚ) (hl : ∀ μ ∈ l, 0 < μ) :
    ((prodBcap l : ℚ) : ℝ) ≤ (l.map (fun μ => factorR gammaR ((μ : ℚ) : ℝ))).prod := by
  induction l with
  | nil => simp [prodBcap]
  | cons a t ih =>
    have ha : 0 < a := hl a (by simp)
    have ht : ∀ μ ∈ t, 0 < μ := fun μ hμ => hl μ (List.mem_cons_of_mem a hμ)
    have h2 := ih ht
    simp only [prodBcap_cons, List.map_cons, List.prod_cons]
    push_cast
    have hfa0 : (0 : ℝ) ≤ factorR gammaR ((a : ℚ) : ℝ) :=
      factorR_nonneg gammaR _ gammaR_pos (by exact_mod_cast ha.le)
    have hpt0 : (0 : ℝ) ≤ ((prodBcap t : ℚ) : ℝ) := by
      have := prodBcap_nonneg t (fun μ hμ => le_of_lt (ht μ hμ)); exact_mod_cast this
    calc ((Bcap a : ℚ) : ℝ) * ((prodBcap t : ℚ) : ℝ)
        ≤ factorR gammaR ((a : ℚ) : ℝ) * ((prodBcap t : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_right (Bcap_le_factorR a) hpt0
      _ ≤ factorR gammaR ((a : ℚ) : ℝ) * (t.map (fun μ => factorR gammaR ((μ : ℚ) : ℝ))).prod :=
          mul_le_mul_of_nonneg_left h2 hfa0

/-- **`|l| ≥ 2`: the config g-step is `≤ 1`, unconditionally (nonneg messages).**
    Routed through the ported `gstep_lt_gamma`. -/
theorem gstep_le_one_len_ge_two (l : List ℚ) (hl2 : 2 ≤ l.length) (hl : ∀ μ ∈ l, 0 < μ) :
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1 := by
  have hdenQ : (0 : ℚ) < W * (5 / 3) ^ 11 := by norm_num [W]
  rw [div_le_one hdenQ]
  have key : ((baseOf l ^ 11 * prodBcap l : ℚ) : ℝ) ≤ ((W * (5 / 3) ^ 11 : ℚ) : ℝ) := by
    push_cast
    rw [baseOf_cast l]
    have hmuslen : (l.map (fun (x : ℚ) => (x : ℝ))).length = l.length := by simp
    have hsumcast : (l.map (fun (x : ℚ) => (x : ℝ))).sum = ((l.sum : ℚ) : ℝ) := (sum_cast l).symm
    have hall : ∀ v ∈ l.map (fun (x : ℚ) => (x : ℝ)), 0 ≤ v := by
      intro v hv
      rw [List.mem_map] at hv
      obtain ⟨μ, hμl, rfl⟩ := hv
      have hμ : (0 : ℚ) < μ := hl μ hμl
      have hcast : (0 : ℝ) ≤ ((μ : ℚ) : ℝ) := by exact_mod_cast hμ.le
      exact hcast
    have hstep : Wr * gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ))) < gammaR :=
      gstep_lt_gamma l.length hl2 gammaR Wr muStar muStar_nonneg muStar_lt_third muStar_crossover
        Wr_pos Wr_four_thirds_lt (l.map (fun (x : ℚ) => (x : ℝ))) hmuslen hall
    have hmapeq : (l.map (fun (x : ℚ) => (x : ℝ))).map (factorR gammaR)
        = l.map (fun μ => factorR gammaR ((μ : ℚ) : ℝ)) := by
      rw [List.map_map]; rfl
    have hcore : gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ)))
        = boostR l.length ((l.sum : ℚ) : ℝ) ^ 11
          * ((l.map (fun (x : ℚ) => (x : ℝ))).map (factorR gammaR)).prod := by
      unfold gCoreOff; rw [zero_add, hsumcast]
    have hpb : ((prodBcap l : ℚ) : ℝ)
        ≤ ((l.map (fun (x : ℚ) => (x : ℝ))).map (factorR gammaR)).prod := by
      rw [hmapeq]; exact prodBcap_cast_le l hl
    have hsnn : (0 : ℝ) ≤ ((l.sum : ℚ) : ℝ) := by rw [← hsumcast]; exact List.sum_nonneg hall
    have hb0 : (0 : ℝ) ≤ boostR l.length ((l.sum : ℚ) : ℝ) ^ 11 := by
      have := boostR_pos l.length ((l.sum : ℚ) : ℝ) hsnn; positivity
    have hle : boostR l.length ((l.sum : ℚ) : ℝ) ^ 11 * ((prodBcap l : ℚ) : ℝ)
        ≤ gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ))) := by
      rw [hcore]; exact mul_le_mul_of_nonneg_left hpb hb0
    have hγeq : gammaR = Wr * (((W : ℚ) : ℝ) * (5 / 3) ^ 11) := by
      rw [W_cast]; unfold gammaR; ring
    have hgcore_lt : gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ)))
        < ((W : ℚ) : ℝ) * (5 / 3) ^ 11 := by
      by_contra hc
      push_neg at hc
      have hmono : Wr * (((W : ℚ) : ℝ) * (5 / 3) ^ 11)
          ≤ Wr * gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hc Wr_pos.le
      rw [← hγeq] at hmono
      exact absurd hstep (not_lt.mpr hmono)
    calc boostR l.length ((l.sum : ℚ) : ℝ) ^ 11 * ((prodBcap l : ℚ) : ℝ)
        ≤ gCoreOff gammaR l.length 0 (l.map (fun (x : ℚ) => (x : ℝ))) := hle
      _ ≤ ((W : ℚ) : ℝ) * (5 / 3) ^ 11 := le_of_lt hgcore_lt
  exact_mod_cast key

/-- **The config g-step is `≤ 1` for every achievable config — unconditionally.**
    Discharges `Case2PropertyAchievable`'s content: `|l|=0` leaf, `|l|=1` via
    `single_child_le_one` (`μ=1` is the arm, `gstep=1`), `|l|≥2` via `gstep_lt_gamma`. -/
theorem gstep_le_one_achievable (l : List ℚ) (hl : ∀ μ ∈ l, Achievable μ) :
    (baseOf l) ^ 11 * prodBcap l / (W * (5 / 3) ^ 11) ≤ 1 := by
  match l with
  | [] =>
    simp only [baseOf, prodBcap, List.length_nil, List.sum_nil, List.map_nil, List.prod_nil,
      Nat.cast_zero]
    norm_num [W]
  | [μ] =>
    obtain ⟨h0, hcase⟩ := hl μ (by simp)
    rcases hcase with h1 | h1
    · exact single_child_le_one h0 h1
    · subst h1
      have hb : baseOf [(1 : ℚ)] = 5 / 3 := by rw [baseOf_singleton]; norm_num
      have hp : prodBcap [(1 : ℚ)] = W := by
        rw [prodBcap_singleton]
        unfold Bcap master_ub glemma W
        norm_num [min_def]
      rw [hb, hp]; norm_num [W]
  | a :: b :: t =>
    exact gstep_le_one_len_ge_two (a :: b :: t) (by simp) (fun μ hμ => (hl μ hμ).1)

end R3Cert.CappedJointConfig
