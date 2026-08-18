/- HAND-AUTHORED (not telperion-generated): R1 single-hub arm-extremality -- the two scalar inequalities.

   Validated in exact Fraction arithmetic by  telperion/src/telperion/arm_lean_certificates.py
   (`ArmLeanCertificate.check()`); the Lean kernel re-proves each statement from scratch here.

   INEQUALITY 1  B(L,j') <= (3/2)^11 : base equality (L=0) + the integer descent tail
                 64(m+1)^11 <= 621 m^11 (m>=6), kernel-tight by an all-nonneg-coefficient Polya identity.
   INEQUALITY 2  the j=2 closure's final rational certificate  W*gamma^2 < 486/529  (W^3(50/27)^11 < 1).

   The g-lemma's multi-variable inductive step (max < gamma) is NOT formalized here -- it is a genuine
   optimization (grid-verified, not a Polya scalar), named as the residual in arm_lean_certificates.py.
   conjecture1_proved = False. -/
import Mathlib

namespace G1
namespace ArmExtremality

/-! ### Inequality 1 : `B(L,j') = W^L * ((3j'+L+3)/(2j'+2))^11 <= (3/2)^11` -/

/-- BASE (equality at `L = 0`): `B(0,j') = (3(j'+1)/(2(j'+1)))^11 = (3/2)^11` for every `j'`. -/
theorem B_base (j : ℕ) : (3 * ((j : ℚ) + 1)) / (2 * ((j : ℚ) + 1)) = 3 / 2 := by
  have h : ((j : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- The all-nonnegative-coefficient Polya identity underlying the descent tail
    (`m = 6 + k`): `621*(6+k)^11 = 64*(7+k)^11 + P(k)` with `P` a nonneg-coefficient polynomial. -/
theorem tail_identity (k : ℕ) :
    621 * (6 + k) ^ 11 = 64 * (7 + k) ^ 11 +
      (557 * k ^ 11 + 36058 * k ^ 10 + 1057100 * k ^ 9 + 18510360 * k ^ 8
        + 214880160 * k ^ 7 + 1734000576 * k ^ 6 + 9907054080 * k ^ 5 + 39974056320 * k ^ 4
        + 111225554880 * k ^ 3 + 202159010240 * k ^ 2 + 214181872960 * k + 98748060224) := by
  ring

/-- The descent tail in `k`-form: `64*(7+k)^11 <= 621*(6+k)^11` for every `k : ℕ`
    (the remainder `P(k)` is a sum of naturals, hence nonneg). -/
theorem per_step_tail (k : ℕ) : 64 * (7 + k) ^ 11 ≤ 621 * (6 + k) ^ 11 := by
  rw [tail_identity]; exact Nat.le_add_right _ _

/-- The descent per-step inequality at every integer `m >= 6`:  `64*(m+1)^11 <= 621*m^11`.
    (Tightest at `m = 6`; already true at `m = 5`; FALSE at `m = 4` -- so `m >= 6` is not slack.) -/
theorem per_step (m : ℕ) (hm : 6 ≤ m) : 64 * (m + 1) ^ 11 ≤ 621 * m ^ 11 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h : 6 + k + 1 = 7 + k := by omega
  rw [h]; exact per_step_tail k

/-! ### Inequality 2 : the j=2 closure's final rational certificate -/

/-- The exact rational certificate `W^3 * (50/27)^11 < 1`  (`W = 64/621`).  Equivalent to
    `W * gamma^2 = W^5 (5/3)^22 < 486/529` with `gamma = W^2 (5/3)^11`, i.e. the j=2 bound
    `Phi^11(B) <= W*gamma^2 < 486/529 = F_arm`. -/
theorem gstep_final_certificate : ((64 : ℚ) / 621) ^ 3 * (50 / 27) ^ 11 < 1 := by norm_num

/-- The j=2 closure spelled out: `W * (W^2 (5/3)^11)^2 < 486/529`. -/
theorem j2_closure :
    ((64 : ℚ) / 621) * (((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11) ^ 2 < 486 / 529 := by
  norm_num

/-- Cross-multiplied integer form of the certificate: `64^3 * 50^11 < 621^3 * 27^11`. -/
theorem gstep_final_integer : (64 : ℕ) ^ 3 * 50 ^ 11 < 621 ^ 3 * 27 ^ 11 := by
  norm_num

/-! ### The branching (j' >= 2) g-step, reduced to two rational leaves

  The g-lemma's inductive step, in the all-non-leaf branching case, is a multi-variable optimization
  `max < gamma` (gamma = W^2 (5/3)^11).  Reduced (symmetric-argmax -> per-j' max at the crossover mu* ->
  boost < 4/3) to the two exact rational facts below; together they give `f_{j'>=2}(mu*) = W*boost^11 <
  W*(4/3)^11 < gamma`.  The majorization/monotonicity reduction itself is not yet formalized (see
  telperion/src/telperion/gstep_reduction.py). -/

/-- (I) `mu* < 1/3`, i.e. `gamma = W^2 (5/3)^11 < (10/9)^11`  -- so `3*mu* < 1` and the symmetric-max
    boost `1 + (3 j' mu* + 1)/(3j'+3) < 1 + (j'+1)/(3j'+3) = 4/3`. -/
theorem gamma_lt_ten_ninths_11 : ((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11 < (10 / 9) ^ 11 := by
  norm_num

/-- (II) `W*(4/3)^11 < gamma`  -- so `f_{j'>=2}(mu*) = W*boost^11 < W*(4/3)^11 < gamma`. -/
theorem W_four_thirds_11_lt_gamma :
    ((64 : ℚ) / 621) * (4 / 3) ^ 11 < ((64 : ℚ) / 621) ^ 2 * (5 / 3) ^ 11 := by
  norm_num

/-- Cross-multiplied integer forms of the two leaves. -/
theorem gstep_leaf_I_integer : (64 : ℕ) ^ 2 * 5 ^ 11 * 9 ^ 11 < 621 ^ 2 * 3 ^ 11 * 10 ^ 11 := by
  norm_num

theorem gstep_leaf_II_integer : (621 : ℕ) * 4 ^ 11 < 64 * 5 ^ 11 := by
  norm_num

/-! ### Coordinate-wise unimodality (replaces majorization -- g_bound is Schur-CONVEX, so Schur fails).

  The global max of the branching g-step is at the symmetric crossover mu* by coordinate-wise unimodality:
  increasing below mu* (T1), and the descent condition below (T2) above mu*.  These two rational lemmas are
  the arithmetic engine; the over-the-reals T1/T2 at the irrational mu* and the Branch wiring remain. -/

/-- **T2 descent engine.**  For `j ≥ 2` and `μ ≤ S`, the coordinate-descent condition holds:
    `3 + μ ≤ (j+1) · boost`, where `boost = 1 + (3S+1)/(3j+3)`.  (Exactly `(j+1)·boost = (j+1) + (3S+1)/3
    ≥ j + 4/3 + μ ≥ 3 + μ` since `j ≥ 2`.)  This forces `g_bound` to decrease toward `μ*` above it. -/
theorem descent_engine (j : ℕ) (hj : 2 ≤ j) (S mu : ℚ) (hmu : mu ≤ S) :
    3 + mu ≤ ((j : ℚ) + 1) * (1 + (3 * S + 1) / (3 * (j : ℚ) + 3)) := by
  have hjq : (2 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj
  have hden : (0 : ℚ) < 3 * (j : ℚ) + 3 := by positivity
  have key : ((j : ℚ) + 1) * (1 + (3 * S + 1) / (3 * (j : ℚ) + 3))
      = ((j : ℚ) + 1) + (3 * S + 1) / 3 := by
    field_simp
  rw [key]
  have hfrac : (3 * mu + 1) / 3 ≤ (3 * S + 1) / 3 := by gcongr
  have hexp : ((j : ℚ) + 1) + (3 * mu + 1) / 3 = (j : ℚ) + mu + 4 / 3 := by ring
  linarith [hfrac, hexp, hjq]

/-- **Boost bound.**  If `3S ≤ j` (all child messages `≤ 1/3`), then `boost = 1 + (3S+1)/(3j+3) ≤ 4/3`.
    At the crossover this gives `boost(μ*) < 4/3` (via `3μ* < 1`, leaf I), hence `W·boost(μ*)^11 < W·(4/3)^11
    < γ`. -/
theorem boost_le_four_thirds (j : ℕ) (S : ℚ) (hS : 3 * S ≤ (j : ℚ)) :
    1 + (3 * S + 1) / (3 * (j : ℚ) + 3) ≤ 4 / 3 := by
  have hden : (0 : ℚ) < 3 * (j : ℚ) + 3 := by positivity
  have h : (3 * S + 1) / (3 * (j : ℚ) + 3) ≤ 1 / 3 := by
    rw [div_le_iff₀ hden]; linarith
  linarith

/-! ### Piece 1: coordinate-wise unimodality of the branching g-step, over ℝ (μ* symbolic).

  The box-max of `g_bound(mu_1..mu_j) = W * boostR(S)^11 * ∏ min(1, γ/(1+mu_i/3)^11)` (S = Σ mu_i) is the
  symmetric crossover value, μ* satisfying `(1+μ*/3)^11 = γ`.  It is reached by per-coordinate two-point
  monotonicity: T1 below μ* (child factor ≡ 1, `boostR` increasing) and T2 above μ*.  Both pointwise steps
  are discharged here over ℝ; moving each coordinate to μ* (a list induction) then pins the box-max. -/

/-- Real boost as a function of the message-sum `x`: `1 + (3x+1)/(3(j+1))`. -/
noncomputable def boostR (j : ℕ) (x : ℝ) : ℝ := 1 + (3 * x + 1) / (3 * (j : ℝ) + 3)

theorem boostR_pos (j : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 < boostR j x := by
  have hden : (0 : ℝ) < 3 * (j : ℝ) + 3 := by positivity
  have : (0 : ℝ) ≤ (3 * x + 1) / (3 * (j : ℝ) + 3) := by positivity
  unfold boostR; linarith

/-- **T1 (below μ*).**  `boostR` is monotone in the message-sum: `x ≤ y → boostR j x ≤ boostR j y`.  With the
    child factor `≡ 1` for `mu ≤ μ*`, this is the T1 half (increasing in each coordinate up to μ*). -/
theorem boostR_mono (j : ℕ) (x y : ℝ) (hxy : x ≤ y) : boostR j x ≤ boostR j y := by
  have hden : (0 : ℝ) < 3 * (j : ℝ) + 3 := by positivity
  unfold boostR; gcongr

/-- **T2 two-point engine (the rational identity, real form).**  For `j ≥ 2`, `0 ≤ Sr`, `ms ≤ mu`:
    `boostR j (Sr+mu) * (1 + ms/3) ≤ boostR j (Sr+ms) * (1 + mu/3)`.  The difference equals
    `(mu - ms) * (3j + 3Sr - 5) / (3(3j+3)) ≥ 0` (nonneg since `mu ≥ ms` and `3j ≥ 6 > 5` for `j ≥ 2`). -/
theorem boost_cross_le (j : ℕ) (hj : 2 ≤ j) (Sr mu ms : ℝ) (hSr : 0 ≤ Sr) (hle : ms ≤ mu) :
    boostR j (Sr + mu) * (1 + ms / 3) ≤ boostR j (Sr + ms) * (1 + mu / 3) := by
  have hjq : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hden : (0 : ℝ) < 3 * (j : ℝ) + 3 := by positivity
  have hkey : boostR j (Sr + ms) * (1 + mu / 3) - boostR j (Sr + mu) * (1 + ms / 3)
      = (mu - ms) * (3 * (j : ℝ) + 3 * Sr - 5) / (3 * (3 * (j : ℝ) + 3)) := by
    unfold boostR; field_simp; ring
  have hnn : 0 ≤ (mu - ms) * (3 * (j : ℝ) + 3 * Sr - 5) / (3 * (3 * (j : ℝ) + 3)) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  linarith [hkey, hnn]

/-- **T2 (above μ*), the g_bound coordinate step.**  For `j ≥ 2`, `0 ≤ Sr`, `0 ≤ ms ≤ mu`:
    `boostR j (Sr+mu)^11 * (1+ms/3)^11 ≤ boostR j (Sr+ms)^11 * (1+mu/3)^11`.  Substituting the crossover
    `(1+ms/3)^11 = γ` this is `boostR(Sr+mu)^11 * γ/(1+mu/3)^11 ≤ boostR(Sr+ms)^11` -- moving the heavy
    coordinate `mu` down to `μ* = ms` does not decrease `g_bound`. -/
theorem gstep_T2_step (j : ℕ) (hj : 2 ≤ j) (Sr mu ms : ℝ)
    (hSr : 0 ≤ Sr) (h0 : 0 ≤ ms) (hle : ms ≤ mu) :
    boostR j (Sr + mu) ^ 11 * (1 + ms / 3) ^ 11 ≤ boostR j (Sr + ms) ^ 11 * (1 + mu / 3) ^ 11 := by
  have hcross := boost_cross_le j hj Sr mu ms hSr hle
  have hL : 0 ≤ boostR j (Sr + mu) * (1 + ms / 3) :=
    mul_nonneg (boostR_pos j _ (by linarith)).le (by linarith)
  calc boostR j (Sr + mu) ^ 11 * (1 + ms / 3) ^ 11
      = (boostR j (Sr + mu) * (1 + ms / 3)) ^ 11 := by rw [mul_pow]
    _ ≤ (boostR j (Sr + ms) * (1 + mu / 3)) ^ 11 := by gcongr
    _ = boostR j (Sr + ms) ^ 11 * (1 + mu / 3) ^ 11 := by rw [mul_pow]

/-- **T1 (below μ*), the g_bound coordinate step.**  With child factor `≡ 1`, `boostR^11` is increasing in
    the message-sum: `0 ≤ x ≤ y → boostR j x ^ 11 ≤ boostR j y ^ 11`. -/
theorem gstep_T1_step (j : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    boostR j x ^ 11 ≤ boostR j y ^ 11 := by
  gcongr
  · exact (boostR_pos j x hx).le
  · exact boostR_mono j x y hxy

/-- The two-regime child factor `min(1, γ/(1+μ/3)^11)`. -/
noncomputable def factorR (γ mu : ℝ) : ℝ := min 1 (γ / (1 + mu / 3) ^ 11)

/-- At the crossover `μ*` (`(1+μ*/3)^11 = γ`), the child factor is exactly `1`. -/
theorem factorR_crossover (γ mustar : ℝ) (hms : 0 ≤ mustar) (hγ : (1 + mustar / 3) ^ 11 = γ) :
    factorR γ mustar = 1 := by
  have hpos : 0 < (1 + mustar / 3) ^ 11 := by positivity
  unfold factorR
  rw [← hγ, div_self (ne_of_gt hpos), min_self]

/-- **Coordinate-wise unimodality (the complete one-coordinate step).**  For `j ≥ 2`, `0 ≤ Sr`, `0 ≤ v`, and
    `μ*` the crossover (`(1+μ*/3)^11 = γ`, `0 ≤ μ*`): moving a single coordinate from `v` to `μ*` does not
    decrease the `boost^11 · factor` core, i.e.
      `boostR j (v+Sr)^11 · factorR γ v ≤ boostR j (μ*+Sr)^11`   (and `factorR γ μ* = 1`).
    Both regimes: `v ≤ μ*` (factor ≡ 1, T1) and `v ≥ μ*` (factor `= γ/(1+v/3)^11`, T2). -/
theorem boost_factor_le (j : ℕ) (hj : 2 ≤ j) (γ mustar v Sr : ℝ)
    (hγ : (1 + mustar / 3) ^ 11 = γ) (hms : 0 ≤ mustar) (hv : 0 ≤ v) (hSr : 0 ≤ Sr) :
    boostR j (v + Sr) ^ 11 * factorR γ v ≤ boostR j (mustar + Sr) ^ 11 := by
  have hms3 : (0 : ℝ) < 1 + mustar / 3 := by linarith
  rcases le_total v mustar with hvm | hvm
  · -- v ≤ μ*: factor = 1 (since (1+v/3)^11 ≤ γ), T1
    have hv3 : (0 : ℝ) < 1 + v / 3 := by linarith
    have hle : (1 + v / 3) ^ 11 ≤ γ := by rw [← hγ]; gcongr
    have h1 : (1 : ℝ) ≤ γ / (1 + v / 3) ^ 11 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hfac : factorR γ v = 1 := by unfold factorR; rw [min_eq_left h1]
    rw [hfac, mul_one]
    exact gstep_T1_step j (v + Sr) (mustar + Sr) (by linarith) (by linarith)
  · -- v ≥ μ*: factor = γ/(1+v/3)^11, T2
    have hv3 : (0 : ℝ) < 1 + v / 3 := by linarith
    have hv3p : (0 : ℝ) < (1 + v / 3) ^ 11 := by positivity
    have hge : γ ≤ (1 + v / 3) ^ 11 := by rw [← hγ]; gcongr
    have h1 : γ / (1 + v / 3) ^ 11 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hfac : factorR γ v = γ / (1 + v / 3) ^ 11 := by unfold factorR; rw [min_eq_right h1]
    have hT2 := gstep_T2_step j hj Sr v mustar hSr hms hvm
    rw [hγ, add_comm Sr v, add_comm Sr mustar] at hT2
    rw [hfac, ← mul_div_assoc, div_le_iff₀ hv3p]
    linarith [hT2]

theorem factorR_nonneg (γ mu : ℝ) (hγ : 0 < γ) (hmu : 0 ≤ mu) : 0 ≤ factorR γ mu := by
  unfold factorR
  have h1 : (0 : ℝ) < 1 + mu / 3 := by linarith
  exact le_min (by norm_num) (div_nonneg hγ.le (by positivity))

/-- The `boost^11 · factor-product` core of `g_bound`, with a nonnegative sum-offset `off` (needed to make the
    coordinate-replacement induction go through). -/
noncomputable def gCoreOff (γ : ℝ) (j : ℕ) (off : ℝ) (mus : List ℝ) : ℝ :=
  boostR j (off + mus.sum) ^ 11 * (mus.map (factorR γ)).prod

/-- **Piece 1 (assembly): the box-max is the symmetric crossover value.**  For `j ≥ 2`, `μ*` the crossover
    (`(1+μ*/3)^11 = γ`, `0 ≤ μ*`), any message list `mus` of nonnegatives, and any offset `off ≥ 0`:
      `gCoreOff γ j off mus ≤ gCoreOff γ j off (replicate mus.length μ*)`.
    Proved by moving each coordinate to `μ*` (one `boost_factor_le` step per element).  With `off = 0` and
    `mus.length = j` this says the box-max of `g_bound` is the symmetric value `W · boostR j (j·μ*)^11`. -/
theorem gCoreOff_le_replicate (j : ℕ) (hj : 2 ≤ j) (γ mustar : ℝ)
    (hγ : (1 + mustar / 3) ^ 11 = γ) (hms : 0 ≤ mustar) :
    ∀ mus : List ℝ, (∀ v ∈ mus, 0 ≤ v) → ∀ off : ℝ, 0 ≤ off →
      gCoreOff γ j off mus ≤ gCoreOff γ j off (List.replicate mus.length mustar) := by
  have hγpos : 0 < γ := by rw [← hγ]; positivity
  intro mus
  induction mus with
  | nil => intro _ off _; simp [gCoreOff]
  | cons v rest ih =>
    intro hall off hoff
    have hv : 0 ≤ v := hall v (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ w ∈ rest, 0 ≤ w := fun w hw => hall w (List.mem_cons.mpr (Or.inr hw))
    have hprod : 0 ≤ (rest.map (factorR γ)).prod :=
      List.prod_nonneg (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact factorR_nonneg γ w hγpos (hrest w hw))
    have hSr : 0 ≤ off + rest.sum :=
      add_nonneg hoff (List.sum_nonneg (fun w hw => hrest w hw))
    -- Step 1: move the head v to μ*  (boost_factor_le with Sr = off + rest.sum)
    have hstep := boost_factor_le j hj γ mustar v (off + rest.sum) hγ hms hv hSr
    have hfacms : factorR γ mustar = 1 := factorR_crossover γ mustar hms hγ
    have h1 : gCoreOff γ j off (v :: rest) ≤ gCoreOff γ j (off + mustar) rest := by
      unfold gCoreOff
      rw [List.map_cons, List.prod_cons, List.sum_cons]
      have harr : boostR j (off + (v + rest.sum)) ^ 11 * (factorR γ v * (rest.map (factorR γ)).prod)
          = (boostR j (v + (off + rest.sum)) ^ 11 * factorR γ v) * (rest.map (factorR γ)).prod := by
        ring_nf
      rw [harr]
      have hoff2 : boostR j (off + mustar + rest.sum) = boostR j (mustar + (off + rest.sum)) := by
        ring_nf
      rw [hoff2]
      exact mul_le_mul_of_nonneg_right hstep hprod
    -- Step 2: induction on the tail with offset off + μ*
    have h2 := ih hrest (off + mustar) (by linarith)
    -- glue: gCoreOff (off+μ*) (replicate rest.length μ*) = gCoreOff off (replicate (rest.length+1) μ*)
    have h3 : gCoreOff γ j (off + mustar) (List.replicate rest.length mustar)
        = gCoreOff γ j off (List.replicate (rest.length + 1) mustar) := by
      unfold gCoreOff
      rw [List.replicate_succ, List.map_cons, List.prod_cons, List.sum_cons, hfacms, one_mul]
      have : off + mustar + (List.replicate rest.length mustar).sum
          = off + (mustar + (List.replicate rest.length mustar).sum) := by ring
      rw [this]
    calc gCoreOff γ j off (v :: rest)
        ≤ gCoreOff γ j (off + mustar) rest := h1
      _ ≤ gCoreOff γ j (off + mustar) (List.replicate rest.length mustar) := h2
      _ = gCoreOff γ j off (List.replicate (rest.length + 1) mustar) := h3
      _ = gCoreOff γ j off (List.replicate (v :: rest).length mustar) := by rw [List.length_cons]

/-! ### Piece 3 (capstone): the branching g-step inequality `W · g_bound < γ`.

  Combines Piece 1 (box-max = symmetric μ*) with the leaves (`boostR(j·μ*) < 4/3`, `W·(4/3)^11 < γ`) into
  the complete inequality a block-level g-lemma applies at each all-non-leaf branching node: for `j ≥ 2`
  children with messages `mus` (`|mus| = j`, each `≥ 0`), `W · gCoreOff γ j 0 mus < γ`.  The remaining
  Branch-induction wiring (defining the block tree, the `g(C)` recursion, and using `phi_le_one` on children
  to get `Φ^11(D_i) ≤ min(1, γ/(1+μ_i/3)^11) = factorR γ μ_i`) plugs this in at each node. -/

/-- At the symmetric point, `boostR j (j·μ*) < 4/3` (from `μ* < 1/3`, i.e. `3μ* < 1`). -/
theorem boostR_jmustar_lt (j : ℕ) (hj : 1 ≤ j) (mustar : ℝ) (_h0 : 0 ≤ mustar) (hlt : mustar < 1 / 3) :
    boostR j ((j : ℝ) * mustar) < 4 / 3 := by
  have hjq : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hden : (0 : ℝ) < 3 * (j : ℝ) + 3 := by positivity
  unfold boostR
  have hfrac : (3 * ((j : ℝ) * mustar) + 1) / (3 * (j : ℝ) + 3) < 1 / 3 := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < (j : ℝ)) (by linarith : (0 : ℝ) < 1 - 3 * mustar)]
  linarith [hfrac]

/-- **Piece 3 capstone -- the branching g-step inequality.**  For `j ≥ 2`, crossover `μ*` with
    `(1+μ*/3)^11 = γ`, `0 ≤ μ* < 1/3` (leaf I), `0 < W` and `W·(4/3)^11 < γ` (leaf II), and any `j` child
    messages `mus` (each `≥ 0`):  `W · gCoreOff γ j 0 mus < γ`.  I.e. `g_bound < γ` at every all-non-leaf
    branching node -- the inductive step of the g-lemma. -/
theorem gstep_lt_gamma (j : ℕ) (hj : 2 ≤ j) (γ W mustar : ℝ)
    (h0 : 0 ≤ mustar) (hlt : mustar < 1 / 3) (hγ : (1 + mustar / 3) ^ 11 = γ)
    (hW : 0 < W) (hWγ : W * (4 / 3) ^ 11 < γ)
    (mus : List ℝ) (hlen : mus.length = j) (hall : ∀ v ∈ mus, 0 ≤ v) :
    W * gCoreOff γ j 0 mus < γ := by
  have hj1 : 1 ≤ j := by omega
  have hP1 := gCoreOff_le_replicate j hj γ mustar hγ h0 mus hall 0 le_rfl
  have hsym : gCoreOff γ j 0 (List.replicate mus.length mustar) = boostR j ((j : ℝ) * mustar) ^ 11 := by
    unfold gCoreOff
    rw [List.map_replicate, List.prod_replicate, factorR_crossover γ mustar h0 hγ, one_pow, mul_one,
      List.sum_replicate, nsmul_eq_mul, zero_add, hlen]
  have hbpos : 0 < boostR j ((j : ℝ) * mustar) := boostR_pos j _ (by positivity)
  have hbound : boostR j ((j : ℝ) * mustar) ^ 11 < (4 / 3 : ℝ) ^ 11 := by
    gcongr
    exact boostR_jmustar_lt j hj1 mustar h0 hlt
  calc W * gCoreOff γ j 0 mus
      ≤ W * gCoreOff γ j 0 (List.replicate mus.length mustar) := by
        exact mul_le_mul_of_nonneg_left hP1 hW.le
    _ = W * boostR j ((j : ℝ) * mustar) ^ 11 := by rw [hsym]
    _ < W * (4 / 3) ^ 11 := by exact mul_lt_mul_of_pos_left hbound hW
    _ < γ := hWγ

end ArmExtremality
end G1
