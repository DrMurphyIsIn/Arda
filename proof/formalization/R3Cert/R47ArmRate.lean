import Mathlib
import R3Cert.R47RateZBound
import R3Cert.R47HeadId
import R3Cert.R47HubState

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

open RTree

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

/-- Cross-multiplied single-step rate climb (`j ≤ 4`): the division-free form of
    `armRate(j) ≤ armRate(j+1)`, from `armVal_succ_up` times `(621/64)^(1+2j)`. -/
theorem armVal_cross_up (j : ℕ) (hj : j ≤ 4) :
    armVal j ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * (j + 1))
      ≤ armVal (j + 1) ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * j) := by
  have h := armVal_succ_up j hj
  have hexp : 1 + 2 * (j + 1) = (1 + 2 * j) + 2 := by ring
  have hpos : (0 : ℚ) ≤ (621 / 64 : ℚ) ^ (1 + 2 * j) := by positivity
  rw [hexp, pow_add]
  calc armVal j ^ 11 * ((621 / 64 : ℚ) ^ (1 + 2 * j) * (621 / 64 : ℚ) ^ 2)
      = (armVal j ^ 11 * (621 / 64 : ℚ) ^ 2) * (621 / 64 : ℚ) ^ (1 + 2 * j) := by ring
    _ ≤ armVal (j + 1) ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * j) :=
        mul_le_mul_of_nonneg_right (le_of_lt h) hpos

/-- Cross-multiplied single-step rate decay (`j ≥ 5`): the division-free form of
    `armRate(j+1) ≤ armRate(j)`, from `armVal_succ_dn` times `(621/64)^(1+2j)`. -/
theorem armVal_cross_dn (j : ℕ) (hj : 5 ≤ j) :
    armVal (j + 1) ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * j)
      ≤ armVal j ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * (j + 1)) := by
  have h := armVal_succ_dn j hj
  have hsplit : (621 / 64 : ℚ) ^ (1 + 2 * (j + 1))
      = (621 / 64 : ℚ) ^ (1 + 2 * j) * (621 / 64 : ℚ) ^ 2 := by
    rw [show 1 + 2 * (j + 1) = (1 + 2 * j) + 2 from by ring]; exact pow_add _ _ _
  have hpos : (0 : ℚ) ≤ (621 / 64 : ℚ) ^ (1 + 2 * j) := by positivity
  rw [hsplit]
  calc armVal (j + 1) ^ 11 * (621 / 64 : ℚ) ^ (1 + 2 * j)
      ≤ (armVal j ^ 11 * (621 / 64 : ℚ) ^ 2) * (621 / 64 : ℚ) ^ (1 + 2 * j) :=
        mul_le_mul_of_nonneg_right h hpos
    _ = armVal j ^ 11 * ((621 / 64 : ℚ) ^ (1 + 2 * j) * (621 / 64 : ℚ) ^ 2) := by ring

/-- The rate-normalized 11th-power arm value `armRate(j)^11 = A(j)^11 / (621/64)^(1+2j)`.
    (Stated at the 11th power to stay rational — `621/64 = rho_B^11`.) -/
def armRate11 (j : ℕ) : ℚ := armVal j ^ 11 / (621 / 64 : ℚ) ^ (1 + 2 * j)

/-- Single-step rate monotonicity below the peak: `armRate(j) ≤ armRate(j+1)` (`j ≤ 4`). -/
theorem armRate11_le_up (j : ℕ) (hj : j ≤ 4) : armRate11 j ≤ armRate11 (j + 1) := by
  rw [armRate11, armRate11, div_le_div_iff₀ (by positivity) (by positivity)]
  exact armVal_cross_up j hj

/-- Single-step rate monotonicity above the peak: `armRate(j+1) ≤ armRate(j)` (`j ≥ 5`). -/
theorem armRate11_ge_dn (j : ℕ) (hj : 5 ≤ j) : armRate11 (j + 1) ≤ armRate11 j := by
  rw [armRate11, armRate11, div_le_div_iff₀ (by positivity) (by positivity)]
  exact armVal_cross_dn j hj

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
    have hexp : 1 + 2 * (k + 1) = (1 + 2 * k) + 2 := by ring
    have hR : (621 / 64 : ℚ) ^ (1 + 2 * (k + 1))
        = (621 / 64 : ℚ) ^ (1 + 2 * k) * (621 / 64 : ℚ) ^ 2 := by
      rw [hexp, pow_add]
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
  rcases Nat.lt_or_ge j 6 with h | h
  · interval_cases j <;> norm_num [armRate11, armVal]
  · exact armRate11_le_one_tail j (by omega)

/-! ### Multi-arm lift: the arm-block rate envelope -/

/-- The arm-load product is nonnegative (a product of positive arm `Ztot`s). -/
theorem armProd_nonneg (arms : List ℕ) : 0 ≤ armProd arms := by
  unfold armProd
  apply List.prod_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact le_of_lt (Ztot_dt_pos (armU j))

/-- **The arm-block rate envelope** (the `armProd` lift): the raw `Ztot` product of any
    arm-load list is bounded by `rho_B` raised to the block's total size,
    `armProd arms ≤ rho_B ^ usizeList (arms.map armU)`.  It is the product over the list
    of the per-arm rate bound `Ztot_dtSub_le_rhoB_pow (armU j)` (the ℝ form of
    `armRate(j) ≤ 1`), tight exactly when every arm sits at the peak load 5.

    Honest boundary: this is the arm-block envelope (each arm's rate ≤ 1, multiplied),
    NOT the joint hub optimum.  The marginal per-arm unimodality (`armVal_succ_up`/`_dn`,
    `armRate11_le_one`) is what pins each arm's peak to load 5.  conjecture1_proved = False. -/
theorem armProd_le_rhoB_pow (arms : List ℕ) :
    armProd arms ≤ rhoB ^ usizeList (arms.map armU) := by
  induction arms with
  | nil => simp [armProd, usizeList_nil]
  | cons a rest ih =>
    have hstep : Ztot (dtSub (armU a)) ≤ rhoB ^ usize (armU a) :=
      Ztot_dtSub_le_rhoB_pow (armU a)
    have hrho : (0 : ℝ) ≤ rhoB ^ usize (armU a) := le_of_lt (pow_pos rhoB_pos _)
    calc armProd (a :: rest)
        = Ztot (dtSub (armU a)) * armProd rest := by simp [armProd]
      _ ≤ rhoB ^ usize (armU a) * rhoB ^ usizeList (rest.map armU) :=
          mul_le_mul hstep ih (armProd_nonneg rest) hrho
      _ = rhoB ^ (usize (armU a) + usizeList (rest.map armU)) := by rw [← pow_add]
      _ = rhoB ^ usizeList ((a :: rest).map armU) := by
          rw [List.map_cons, usizeList_cons]

/-! ### Single-arm monotone resize: moving one arm toward the peak load 5 -/

/-- Bridge: the real arm `Ztot` is the cast of the rational `armVal`. -/
theorem armVal_cast (j : ℕ) : ((armVal j : ℚ) : ℝ) = Ztot (dtSub (armU j)) := by
  rw [Ztot_dtSub_armU, armVal]; push_cast; ring

/-- The rate-normalized arm-block objective (real), `armProd^11 / (621/64)^size`. -/
noncomputable def armObj (arms : List ℕ) : ℝ :=
  armProd arms ^ 11 / (621 / 64 : ℝ) ^ usizeList (arms.map armU)

theorem armObj_nonneg (arms : List ℕ) : 0 ≤ armObj arms := by
  unfold armObj
  exact div_nonneg (pow_nonneg (armProd_nonneg arms) 11) (le_of_lt (pow_pos (by norm_num) _))

/-- **The factorization**: the block objective peels one arm off the head as its own
    rate factor, `armObj (j :: rest) = armRate(j)^11 · armObj rest`.  This is what makes
    a single-arm resize a *local* move — the rest of the block is an untouched constant. -/
theorem armObj_cons (j : ℕ) (rest : List ℕ) :
    armObj (j :: rest) = (armRate11 j : ℝ) * armObj rest := by
  have hP : armProd (j :: rest) = Ztot (dtSub (armU j)) * armProd rest := by simp [armProd]
  have hU : usizeList ((j :: rest).map armU) = (1 + 2 * j) + usizeList (rest.map armU) := by
    rw [List.map_cons, usizeList_cons, usize_armU]
  have hZ : Ztot (dtSub (armU j)) = ((armVal j : ℚ) : ℝ) := (armVal_cast j).symm
  simp only [armObj, hP, hU, hZ, armRate11]
  push_cast
  rw [mul_pow, pow_add]
  ring

/-- The block objective depends only on the multiset of arm loads. -/
theorem armObj_perm {l1 l2 : List ℕ} (h : l1.Perm l2) : armObj l1 = armObj l2 := by
  have hu : usizeList (l1.map armU) = usizeList (l2.map armU) := by
    rw [usizeList_map_armU, usizeList_map_armU, h.length_eq, h.sum_eq]
  unfold armObj
  rw [armProd_perm h, hu]

/-- **Monotone resize below the peak** (`j ≤ 4`): incrementing the head arm's load
    toward 5, with the rest of the block held fixed, does not decrease the objective.
    Via `armObj_perm`, "head" is any arm.  conjecture1_proved = False. -/
theorem armObj_resize_up (j : ℕ) (rest : List ℕ) (hj : j ≤ 4) :
    armObj (j :: rest) ≤ armObj ((j + 1) :: rest) := by
  rw [armObj_cons, armObj_cons]
  apply mul_le_mul_of_nonneg_right _ (armObj_nonneg rest)
  exact_mod_cast armRate11_le_up j hj

/-- **Monotone resize above the peak** (`j ≥ 5`): decrementing the head arm's load
    toward 5, with the rest of the block held fixed, does not decrease the objective. -/
theorem armObj_resize_dn (j : ℕ) (rest : List ℕ) (hj : 5 ≤ j) :
    armObj ((j + 1) :: rest) ≤ armObj (j :: rest) := by
  rw [armObj_cons, armObj_cons]
  apply mul_le_mul_of_nonneg_right _ (armObj_nonneg rest)
  exact_mod_cast armRate11_ge_dn j hj

end Step3
end R3Cert
