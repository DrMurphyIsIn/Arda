import Mathlib

/-!
  # Arm-load rate unimodality (Hnorm/Hdom frontier, Step 1)

  The arm-load axis analogue of `R47LegsRate.lean`.  Where `R47LegsRate` pins the
  *leg length* `ℓ` of a star's arms toward the cherry value, this file pins the
  *arm load* `j` (number of cherries hung on one arm-center) toward its
  rate-maximal value.

  Ground truth (exact rational, ℝ identity `R47HubState.Ztot_dtSub_armU`):

      A(j) := Ztot(dtSub(armU j)) = (3/2)^j · (1 + j/(3(j+1)))

  and the per-arm rate exponent is `usize(armU j) = 1 + 2j` (`R47StepSize.usize_armU`),
  with `rho_B^11 = 621/64` (`ExactCruxes.rhoB_pow11_factor`).  So the rate-normalized
  arm value is `armRate(j) = A(j) / rho_B^(1+2j)`, and

      armRate(j)^11 = A(j)^11 / (621/64)^(1+2j)   (rational — no `rpow`).

  **The peak is load 5, exactly.**  `A(5) = 621/64 = rho_B^11` (`armVal_five`), so
  `armRate(5) = 1`, and the marginal per-step comparison

      armRate(j+1) ⋛ armRate(j)   ⟺   A(j+1)^11 ⋛ A(j)^11 · (621/64)^2

  climbs strictly for `j ≤ 4` (`armVal_succ_up`) and falls for `j ≥ 5`
  (`armVal_succ_dn`): strictly unimodal, single peak at `j = 5`.  These two cleared
  (division-free) successor inequalities ARE the rate-normalized unimodality — the
  `(621/64)^2 = (rho_B^11)^2 = rho_B^22` factor is exactly the two-step rate
  normalization (`usize` rises by 2 per unit load).

  **The `{4,5}` marginal correction.**  The approved plan expected a `{4,5}` plateau;
  exact computation shows the *marginal* peak is a single load 5 (`A(5) = 621/64`
  exactly, `armRate < 1` for every `j ≠ 5`).  Allowing load 4 is a JOINT/integrality
  effect (a fixed total size forces some arms down to 4), a separate and harder
  argument named at assembly — NOT the marginal resize proved here.

  HONEST SCOPE.  This is the marginal (single-arm) resize on the ℚ rate axis.  The
  next bricks: (a) the division-wrapped restatement `armRate(j) ≤ armRate(5) = 1`
  — already available in ℝ via `R47RateZBound.Ztot_dtSub_le_rhoB_pow`, here just the
  ℚ unimodal envelope through the `Telperion.unimodal_peak` prelude; (b) the multi-arm
  lift via the merged `R47R6SpineMono.node_Ztot_child_mono` (#134) — resizing any one
  arm toward 5 does not decrease the rate-normalized hub objective; (c) the JOINT
  `{4,5}` pinning.  conjecture1_proved = False.
-/

namespace R3Cert
namespace Step3

/-- The rational arm value `A(j) = Ztot(dtSub(armU j)) = (3/2)^j·(1 + j/(3(j+1)))`.
    (The ℝ identity is `R47HubState.Ztot_dtSub_armU`; we work in ℚ to clear the
    11th root, exactly as `R47LegsRate.armBase` does on the leg axis.) -/
def armVal (j : ℕ) : ℚ := (3 / 2) ^ j * (1 + (j : ℚ) / (3 * ((j : ℚ) + 1)))

/-- `A(j) > 0`. -/
theorem armVal_pos (j : ℕ) : 0 < armVal j := by
  unfold armVal; positivity

/-- **The peak identity**: `A(5) = 621/64 = rho_B^11` exactly, so the rate-normalized
    arm value hits `armRate(5) = 1`.  `(243/32)·(23/18) = 5589/576 = 621/64`. -/
theorem armVal_five : armVal 5 = (621 / 64 : ℚ) := by
  norm_num [armVal]

/-- **Strict climb below the peak** (`j ≤ 4`): the rate-normalized arm value rises,
    `A(j)^11 · (621/64)^2 < A(j+1)^11`.  Finite — one `norm_num` per load. -/
theorem armVal_succ_up (j : ℕ) (hj : j ≤ 4) :
    armVal j ^ 11 * (621 / 64 : ℚ) ^ 2 < armVal (j + 1) ^ 11 := by
  interval_cases j <;> norm_num [armVal]

/-- **Decay above the peak** (`j ≥ 5`): the rate-normalized arm value falls,
    `A(j+1)^11 ≤ A(j)^11 · (621/64)^2`.

    Proof: the single-step ratio `A(j+1)/A(j) = (3/2)·(4j+7)(3j+3)/((3j+6)(4j+3))`
    is decreasing on `j ≥ 5`, so `A(j+1) ≤ (243/161)·A(j)` (the `243/161` value is the
    ratio at the peak `j = 5`, where it is tight); the difference clears to
    `(j-5)(4j+31)/(322(j+1)(j+2)) ≥ 0`.  Then `(243/161)^11 ≤ (621/64)^2` (`norm_num`)
    raises it to the 11th power. -/
theorem armVal_succ_dn (j : ℕ) (hj : 5 ≤ j) :
    armVal (j + 1) ^ 11 ≤ armVal j ^ 11 * (621 / 64 : ℚ) ^ 2 := by
  have hjq : (5 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj
  have hP : (0 : ℚ) < (3 / 2 : ℚ) ^ j := by positivity
  -- The power-free single-step bound `A(j+1) ≤ (243/161)·A(j)`.
  have hstep : armVal (j + 1) ≤ (243 / 161 : ℚ) * armVal j := by
    have hL : armVal (j + 1)
        = (3 / 2 : ℚ) ^ j * ((3 / 2) * (1 + ((j : ℚ) + 1) / (3 * ((j : ℚ) + 2)))) := by
      rw [armVal, pow_succ]; push_cast; ring
    have hR : (243 / 161 : ℚ) * armVal j
        = (3 / 2 : ℚ) ^ j * ((243 / 161) * (1 + (j : ℚ) / (3 * ((j : ℚ) + 1)))) := by
      rw [armVal]; ring
    rw [hL, hR]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hP)
    rw [← sub_nonneg]
    have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((j : ℚ) + 2) ≠ 0 := by positivity
    have hid : (243 / 161 : ℚ) * (1 + (j : ℚ) / (3 * ((j : ℚ) + 1)))
          - 3 / 2 * (1 + ((j : ℚ) + 1) / (3 * ((j : ℚ) + 2)))
        = ((j : ℚ) - 5) * (4 * (j : ℚ) + 31) / (322 * ((j : ℚ) + 1) * ((j : ℚ) + 2)) := by
      field_simp
      ring
    rw [hid]
    apply div_nonneg
    · apply mul_nonneg
      · linarith [hjq]
      · positivity
    · positivity
  -- Raise to the 11th power against the tight rate constant.
  have hpos_j1 : (0 : ℚ) ≤ armVal (j + 1) := le_of_lt (armVal_pos _)
  calc armVal (j + 1) ^ 11
      ≤ ((243 / 161 : ℚ) * armVal j) ^ 11 := pow_le_pow_left₀ hpos_j1 hstep 11
    _ = (243 / 161 : ℚ) ^ 11 * armVal j ^ 11 := by rw [mul_pow]
    _ ≤ (621 / 64 : ℚ) ^ 2 * armVal j ^ 11 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (armVal_pos j).le 11)
        norm_num
    _ = armVal j ^ 11 * (621 / 64 : ℚ) ^ 2 := by ring

/-- The rate-normalized 11th-power arm value `armRate(j)^11 = A(j)^11 / (621/64)^(1+2j)`.
    (Stated at the 11th power to stay rational — `621/64 = rho_B^11`.) -/
def armRate11 (j : ℕ) : ℚ := armVal j ^ 11 / (621 / 64 : ℚ) ^ (1 + 2 * j)

/-- The peak value is exactly `1`: `armRate(5)^11 = (621/64)^11 / (621/64)^11 = 1`. -/
theorem armRate11_five : armRate11 5 = 1 := by
  rw [armRate11, armVal_five]; norm_num

/-- **Tail envelope** (`j ≥ 5`): `armRate(j)^11 ≤ 1`, by induction from the peak
    `armRate(5) = 1` using the decay `armVal_succ_dn` (`R(j+1) = R(j)·(621/64)^2`). -/
theorem armRate11_le_one_tail (j : ℕ) (hj : 5 ≤ j) : armRate11 j ≤ 1 := by
  induction j, hj using Nat.le_induction with
  | base => exact le_of_eq armRate11_five
  | succ k hk ih =>
    rw [armRate11, div_le_one (by positivity)]
    have hR : (621 / 64 : ℚ) ^ (1 + 2 * (k + 1))
        = (621 / 64 : ℚ) ^ (1 + 2 * k) * (621 / 64 : ℚ) ^ 2 := by
      rw [← pow_add]; congr 1; ring
    rw [hR]
    have hBk : armVal k ^ 11 ≤ (621 / 64 : ℚ) ^ (1 + 2 * k) := by
      rw [armRate11, div_le_one (by positivity)] at ih; exact ih
    calc armVal (k + 1) ^ 11
        ≤ armVal k ^ 11 * (621 / 64 : ℚ) ^ 2 := armVal_succ_dn k hk
      _ ≤ (621 / 64 : ℚ) ^ (1 + 2 * k) * (621 / 64 : ℚ) ^ 2 :=
          mul_le_mul_of_nonneg_right hBk (by positivity)

/-- **The rate-normalized arm-value envelope**: `armRate(j)^11 ≤ 1` for every load `j`,
    with equality exactly at the peak `j = 5` (`armRate11_five`) — the unimodality
    `armVal_succ_up`/`armVal_succ_dn` assembled (finite climb below the peak, monotone
    tail above).  This ℚ envelope also follows in ℝ from
    `R47RateZBound.Ztot_dtSub_le_rhoB_pow`; stated here on the rate axis for the
    resize/`armProd` lift.  conjecture1_proved = False. -/
theorem armRate11_le_one (j : ℕ) : armRate11 j ≤ 1 := by
  rcases le_or_lt j 5 with h | h
  · interval_cases j <;> norm_num [armRate11, armVal]
  · exact armRate11_le_one_tail j (le_of_lt h)

end Step3
end R3Cert
