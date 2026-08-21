import Mathlib
import HomogMaster
import HomogMasterAssembled
import HomogMasterStrict

/-!
# Strictness companion: `GS k mu = T <-> (k,mu) = (1,1)`

This file completes the STRICTNESS half of the achievable homogeneous master
bound assembled in `HomogMasterAssembled.lean`.  It proves that the bound
`GS k mu <= T` is *strict* everywhere except at the arm `(k,mu) = (1,1)`, and
packages the equality characterisation as an iff.

Two independent slack sources (no new mathematics beyond the strict certs of
`HomogMasterStrict.lean` and the already-strict arm ratio cert):

* On the achievable region `0 < mu <= 1/2` (any `k >= 1`): the region chains of
  `HomogMasterAssembled` bound `GS k mu <= [cert quantity]`, and each strict
  Bernstein cert upgrades `[cert quantity] <= T` to `< T`.  So `GS k mu < T`.

* On the arm line `mu = 1` (`k >= 2`): the per-step arm ratio is strictly `< 1`
  (`armline_ratio_cert : 64*16^11 < 621*15^11`), giving `armGS (k+1) < armGS k`,
  hence `armGS k < T` for `k >= 2` by induction from `armGS 2 < armGS 1 = T`.

`conjecture1_proved = False`.  This closes the HOMOGENEOUS face over ACHIEVABLE
`mu` only; the heterogeneous -> homogeneous reduction remains open.
-/

namespace HomogMaster

/-- **Strict per-step arm decrease.** `armGS (k+1) < armGS k` for `k >= 1`.
    Same chain as `armGS_step`, but the geometric factor `(16/15)^11 * (64/621)`
    is *strictly* `< 1` (`armline_ratio_cert`) and `base(k)^11 * W^k > 0`. -/
theorem armGS_step_strict (k : ℕ) (hk : 1 ≤ k) : armGS (k + 1) < armGS k := by
  have hkQ : (0 : ℚ) ≤ (k : ℚ) := by positivity
  -- base ratio bound (identical to armGS_step)
  have hbr : (6 * ((k : ℚ) + 1) + 4) / (3 * (((k : ℚ) + 1) + 1))
      ≤ (16 / 15) * ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) := by
    have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have hd1 : (0 : ℚ) < 3 * (((k : ℚ) + 1) + 1) := by positivity
    have hd2 : (0 : ℚ) < 3 * ((k : ℚ) + 1) := by positivity
    rw [div_le_iff₀ hd1, mul_comm (16 / 15 : ℚ), mul_assoc, div_mul_eq_mul_div,
      le_div_iff₀ hd2]
    nlinarith [hk1, sq_nonneg ((k : ℚ) - 1), hkQ]
  have hbase_pos : (0 : ℚ) ≤ (6 * ((k : ℚ) + 1) + 4) / (3 * (((k : ℚ) + 1) + 1)) := by positivity
  have hpow : ((6 * ((k : ℚ) + 1) + 4) / (3 * (((k : ℚ) + 1) + 1))) ^ 11
      ≤ ((16 / 15) * ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1)))) ^ 11 :=
    pow_le_pow_left₀ hbase_pos hbr 11
  -- STRICT geometric factor
  have hstep_cert : ((16 : ℚ) / 15) ^ 11 * (64 / 621) < 1 := by norm_num
  have hWk : (0 : ℚ) ≤ (64 / 621 : ℚ) ^ k := by positivity
  -- the arm base is strictly positive, so base(k)^11 * W^k > 0 (strictness lever)
  have hbase_k_pos : (0 : ℚ) < (6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1)) := by
    apply div_pos <;> positivity
  have hbk_pos : (0 : ℚ) < ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) ^ 11 := by positivity
  have hWk_pos : (0 : ℚ) < (64 / 621 : ℚ) ^ k := by positivity
  have hprod_pos : (0 : ℚ) < ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) ^ 11 * (64 / 621 : ℚ) ^ k :=
    mul_pos hbk_pos hWk_pos
  have hbk : (0 : ℚ) ≤ ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) ^ 11 := le_of_lt hbk_pos
  -- expand armGS (k+1)
  have e : armGS (k + 1)
      = ((6 * ((k : ℚ) + 1) + 4) / (3 * (((k : ℚ) + 1) + 1))) ^ 11 * (64 / 621) * (64 / 621) ^ k := by
    unfold armGS; push_cast; rw [pow_succ]; ring
  rw [e]
  calc ((6 * ((k : ℚ) + 1) + 4) / (3 * (((k : ℚ) + 1) + 1))) ^ 11 * (64 / 621) * (64 / 621) ^ k
      ≤ ((16 / 15) * ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1)))) ^ 11 * (64 / 621) * (64 / 621) ^ k := by
        apply mul_le_mul_of_nonneg_right _ hWk
        apply mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) ^ 11 * (64 / 621) ^ k * ((16 / 15) ^ 11 * (64 / 621)) := by
        rw [mul_pow]; ring
    _ < ((6 * (k : ℚ) + 4) / (3 * ((k : ℚ) + 1))) ^ 11 * (64 / 621) ^ k * 1 := by
        exact (mul_lt_mul_of_pos_left hstep_cert hprod_pos)
    _ = armGS k := by unfold armGS; ring

/-- **Strict arm tail.** `armGS k < T` for all `k >= 2`. -/
theorem armGS_lt (k : ℕ) (hk : 2 ≤ k) : armGS k < Tval := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge 2 (n + 1) with h | h
    · -- n + 1 > 2, so n >= 2: strict step then IH
      have hn2 : 2 ≤ n := by omega
      have hn1 : 1 ≤ n := by omega
      exact lt_trans (armGS_step_strict n hn1) (ih hn2)
    · -- n + 1 <= 2 and 2 <= n + 1, so n + 1 = 2, i.e. n = 1
      have hn1 : n = 1 := by omega
      subst hn1
      -- armGS 2 < armGS 1 = T
      calc armGS 2 < armGS 1 := armGS_step_strict 1 (le_refl 1)
        _ = Tval := armGS_one

end HomogMaster

namespace HomogMasterAssembled

/-! ## Strict region certificates (bridges upgraded to `< T`) -/

/-- Strict bridge A: `(7/6 + mu/2)^11 < T` on `(0, 37/120]`. -/
theorem bridgeA_strict (mu : ℚ) (h0 : 0 ≤ mu) (h1 : mu ≤ 37 / 120) :
    (7 / 6 + mu / 2) ^ 11 < T := by
  have h0R : (0 : ℝ) ≤ (mu : ℝ) := by exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 37 / 120 := by
    rw [show (37:ℝ)/120 = ((37/120 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMasterStrict.certA_strict (mu : ℝ) h0R h1R
  have heq : (-(mu:ℝ)^11/2048 - 77*(mu:ℝ)^10/6144 - 2695*(mu:ℝ)^9/18432 - 18865*(mu:ℝ)^8/18432 - 132055*(mu:ℝ)^7/27648 - 1294139*(mu:ℝ)^6/82944 - 9058973*(mu:ℝ)^5/248832 - 45294865*(mu:ℝ)^4/746496 - 317064055*(mu:ℝ)^3/4478976 - 2219448385*(mu:ℝ)^2/40310784 - 3107227739*(mu:ℝ)/120932352 + 5172080092597/225296971776)
      = (64/621) * (5/3)^11 - (7/6 + (mu:ℝ)/2)^11 := by ring
  rw [heq] at hR
  have hcast : (((7 / 6 + mu / 2) ^ 11 : ℚ) : ℝ) < (T : ℝ) := by
    rw [T_cast]; push_cast; linarith
  exact_mod_cast hcast

/-- Strict bridge B: `(7/6 + mu/2)^11 * (glemma mu)^1 < T` on `[37/120, 1/3]`. -/
theorem bridgeB_strict (mu : ℚ) (h0 : 37/120 ≤ mu) (h1 : mu ≤ 1/3) :
    (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 < T := by
  have h0R : (37/120 : ℝ) ≤ (mu : ℝ) := by
    rw [show (37/120:ℝ) = ((37/120 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/3 := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMasterStrict.certB_strict (mu : ℝ) h0R h1R
  have heq : (-568847656250*(mu:ℝ)^11/448215674395347 - 4691113281250*(mu:ℝ)^10/149405224798449 - 17364746093750*(mu:ℝ)^9/49801741599483 - 12627441406250*(mu:ℝ)^8/5533526844387 - 1987304687500*(mu:ℝ)^7/204945438681 - 153142773437500*(mu:ℝ)^6/5533526844387 - 872761914062500*(mu:ℝ)^5/16600580533161 - 3082997070312500*(mu:ℝ)^4/49801741599483 - 5026833496093750*(mu:ℝ)^3/149405224798449 + 16685071777343750*(mu:ℝ)^2/1344647023186041 + 116730331738281250*(mu:ℝ)/4033941069558123 + 150677582128906250/12101823208674369)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 := by
    have hcast : (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have : (0:ℝ) < (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast this
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 11 := by positivity
  have hglem : (glemma mu) ^ 1 = GAMMA ^ 1 / (1 + mu / 3) ^ 11 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-- Strict bridge C1: `(7/6 + mu/2)^11 * (glemma mu)^1 < T` on `[1/3, 1/2]`. -/
theorem bridgeC1_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMasterStrict.certC1_strict (mu : ℝ) h0R h1R
  have heq : (-568847656250*(mu:ℝ)^11/448215674395347 - 4691113281250*(mu:ℝ)^10/149405224798449 - 17364746093750*(mu:ℝ)^9/49801741599483 - 12627441406250*(mu:ℝ)^8/5533526844387 - 1987304687500*(mu:ℝ)^7/204945438681 - 153142773437500*(mu:ℝ)^6/5533526844387 - 872761914062500*(mu:ℝ)^5/16600580533161 - 3082997070312500*(mu:ℝ)^4/49801741599483 - 5026833496093750*(mu:ℝ)^3/149405224798449 + 16685071777343750*(mu:ℝ)^2/1344647023186041 + 116730331738281250*(mu:ℝ)/4033941069558123 + 150677582128906250/12101823208674369)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 := by
    have hcast : (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have : (0:ℝ) < (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast this
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 11 := by positivity
  have hglem : (glemma mu) ^ 1 = GAMMA ^ 1 / (1 + mu / 3) ^ 11 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-- Strict bridge C2: `((10 + 6 mu)/9)^11 * (glemma mu)^2 < T` on `[1/3, 1/2]`. -/
theorem bridgeC2_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    ((10 + 6 * mu) / 9) ^ 11 * (glemma mu) ^ 2 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMasterStrict.certC2_strict (mu : ℝ) h0R h1R
  have heq : (3125000000*(mu:ℝ)^22/3452176611830979783 + 68750000000*(mu:ℝ)^21/1150725537276993261 + 240625000000*(mu:ℝ)^20/127858393030777029 + 4812500000000*(mu:ℝ)^19/127858393030777029 + 22859375000000*(mu:ℝ)^18/42619464343592343 + 9143750000000*(mu:ℝ)^17/1578498679392309 + 77721875000000*(mu:ℝ)^16/1578498679392309 + 177650000000000*(mu:ℝ)^15/526166226464103 + 111031250000000*(mu:ℝ)^14/58462914051567 + 1554437500000000*(mu:ℝ)^13/175388742154701 + 2020768750000000*(mu:ℝ)^12/58462914051567 + 93440078858813577325000000000*(mu:ℝ)^11/826737822113891853061955763 + 767050890585212012931250000000*(mu:ℝ)^10/2480213466341675559185867289 + 5228904934820698551062500000000*(mu:ℝ)^9/7440640399025026677557601867 + 9738350945725632919906250000000*(mu:ℝ)^8/7440640399025026677557601867 + 43815444539483038015550000000000*(mu:ℝ)^7/22321921197075080032672805601 + 155275312874214462186228125000000*(mu:ℝ)^6/66965763591225240098018416803 + 421336640894563585768018750000000*(mu:ℝ)^5/200897290773675720294055250409 + 842141602236408964420046875000000*(mu:ℝ)^4/602691872321027160882165751227 + 1169531456868985406269562500000000*(mu:ℝ)^3/1808075616963081482646497253681 + 3064602400319390895391728125000000*(mu:ℝ)^2/16272680552667733343818475283129 + 1369659200273763624621481250000000*(mu:ℝ)/48818041658003200031455425849387 + 160315127384721482799696875000000/146454124974009600094366277548161)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^22 - ((10 + 6*(mu:ℝ))/9)^11*((64/621)^2 * (5/3)^11)^2 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 := by
    have hcast : (((T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^22 - ((10 + 6*(mu:ℝ))/9)^11*((64/621)^2 * (5/3)^11)^2 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have : (0:ℝ) < (((T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast this
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 22 := by positivity
  have hglem : (glemma mu) ^ 2 = GAMMA ^ 2 / (1 + mu / 3) ^ 22 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-- Strict bridge C3: `(1 + mu)^11 * (glemma mu)^3 < T` on `[1/3, 1/2]`. -/
theorem bridgeC3_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    (1 + mu) ^ 11 * (glemma mu) ^ 3 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMasterStrict.certC3_strict (mu : ℝ) h0R h1R
  have heq : (3125000000*(mu:ℝ)^33/611542730256022575619101 + 34375000000*(mu:ℝ)^32/67949192250669175068789 + 550000000000*(mu:ℝ)^31/22649730750223058356263 + 17050000000000*(mu:ℝ)^30/22649730750223058356263 + 42625000000000*(mu:ℝ)^29/2516636750024784261807 + 247225000000000*(mu:ℝ)^28/838878916674928087269 + 3461150000000000*(mu:ℝ)^27/838878916674928087269 + 494450000000000*(mu:ℝ)^26/10356529835492939349 + 1606962500000000*(mu:ℝ)^25/3452176611830979783 + 40174062500000000*(mu:ℝ)^24/10356529835492939349 + 32139250000000000*(mu:ℝ)^23/1150725537276993261 + 2921750000000000*(mu:ℝ)^22/16677181699666569 + 16069625000000000*(mu:ℝ)^21/16677181699666569 + 8652875000000000*(mu:ℝ)^20/1853020188851841 + 12361250000000000*(mu:ℝ)^19/617673396283947 + 46972750000000000*(mu:ℝ)^18/617673396283947 + 5871593750000000*(mu:ℝ)^17/22876792454961 + 5871593750000000*(mu:ℝ)^16/7625597484987 + 46972750000000000*(mu:ℝ)^15/22876792454961 + 12361250000000000*(mu:ℝ)^14/2541865828329 + 8652875000000000*(mu:ℝ)^13/847288609443 + 16069625000000000*(mu:ℝ)^12/847288609443 + 9886758546972783385527505750000000000*(mu:ℝ)^11/318824000457823368106665682399083 + 14108827480439210944452508250000000000*(mu:ℝ)^10/318824000457823368106665682399083 + 17306034350549013680565635312500000000*(mu:ℝ)^9/318824000457823368106665682399083 + 5948572366197644925003628712500000000*(mu:ℝ)^8/106274666819274456035555227466361 + 5017143722643979930772580350000000000*(mu:ℝ)^7/106274666819274456035555227466361 + 3354667339834206612823118050000000000*(mu:ℝ)^6/106274666819274456035555227466361 + 1716571861321989965386290175000000000*(mu:ℝ)^5/106274666819274456035555227466361 + 645123376545856878648081125000000000*(mu:ℝ)^4/106274666819274456035555227466361 + 170049350618342751459232450000000000*(mu:ℝ)^3/106274666819274456035555227466361 + 91333305377266267399976650000000000*(mu:ℝ)^2/318824000457823368106665682399083 + 11624994758237425137495621875000000*(mu:ℝ)/318824000457823368106665682399083 + 1056817705294311376135965625000000/318824000457823368106665682399083)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^33 - (1 + (mu:ℝ))^11*((64/621)^2 * (5/3)^11)^3 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 := by
    have hcast : (((T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^33 - (1 + (mu:ℝ))^11*((64/621)^2 * (5/3)^11)^3 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have : (0:ℝ) < (((T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast this
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 33 := by positivity
  have hglem : (glemma mu) ^ 3 = GAMMA ^ 3 / (1 + mu / 3) ^ 33 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-! ## Strict region dispatch (`GS k mu < T` on the achievable region) -/

/-- **Strict region A** (`0 < mu <= 37/120`): `GS k mu < T`. -/
theorem GS_regionA_strict (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 0 < mu) (h1 : mu ≤ 37 / 120) :
    GS k mu < T := by
  have h0' : 0 ≤ mu := le_of_lt h0
  have hmu13 : mu ≤ 1 / 3 := le_trans h1 (by norm_num)
  have hbcap0 := Bcap_nonneg mu h0'
  have hbcap1 := Bcap_le_one mu
  have hbase0 := base_nonneg k mu h0'
  have hbase1 := base_le_base_one k mu hk hmu13
  calc GS k mu = (base k mu) ^ 11 * (Bcap mu) ^ k := rfl
    _ ≤ (base 1 mu) ^ 11 * 1 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ hbase0 hbase1 11
        · exact pow_le_one₀ hbcap0 hbcap1
        · exact pow_nonneg hbcap0 k
        · exact pow_nonneg (base_nonneg 1 mu h0') 11
    _ = (7 / 6 + mu / 2) ^ 11 := by rw [base_one]; ring
    _ < T := bridgeA_strict mu h0' h1

/-- **Strict region B** (`37/120 <= mu <= 1/3`): `GS k mu < T`. -/
theorem GS_regionB_strict (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 37 / 120 ≤ mu) (h1 : mu ≤ 1 / 3) :
    GS k mu < T := by
  have h0' : 0 ≤ mu := le_trans (by norm_num) h0
  have hbcap0 := Bcap_nonneg mu h0'
  have hbcap1 := Bcap_le_one mu
  have hbcapg := Bcap_le_glemma mu
  have hbase0 := base_nonneg k mu h0'
  have hbase1 := base_le_base_one k mu hk h1
  have hpow : (Bcap mu) ^ k ≤ Bcap mu := by
    calc (Bcap mu) ^ k ≤ (Bcap mu) ^ 1 := pow_le_pow_of_le_one hbcap0 hbcap1 hk
      _ = Bcap mu := pow_one _
  calc GS k mu = (base k mu) ^ 11 * (Bcap mu) ^ k := rfl
    _ ≤ (base 1 mu) ^ 11 * glemma mu := by
        apply mul_le_mul (pow_le_pow_left₀ hbase0 hbase1 11) (le_trans hpow hbcapg)
        · exact pow_nonneg hbcap0 k
        · exact pow_nonneg (base_nonneg 1 mu h0') 11
    _ = (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by rw [base_one]; ring
    _ < T := bridgeB_strict mu h0 h1

/-- **Strict region C** (`1/3 <= mu <= 1/2`): `GS k mu < T`. -/
theorem GS_regionC_strict (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 1 / 3 ≤ mu) (h1 : mu ≤ 1 / 2) :
    GS k mu < T := by
  have h0' : 0 ≤ mu := le_trans (by norm_num) h0
  have hbcap0 := Bcap_nonneg mu h0'
  have hbcap1 := Bcap_le_one mu
  have hbcapg := Bcap_le_glemma mu
  have hglem0 := glemma_nonneg mu h0'
  have hbase0 := base_nonneg k mu h0'
  match k, hk with
  | 1, _ =>
    calc GS 1 mu = (base 1 mu) ^ 11 * (Bcap mu) ^ 1 := rfl
      _ ≤ (base 1 mu) ^ 11 * glemma mu := by
          rw [pow_one]
          apply mul_le_mul_of_nonneg_left hbcapg
          exact pow_nonneg (base_nonneg 1 mu h0') 11
      _ = (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by rw [base_one]; ring
      _ < T := bridgeC1_strict mu h0 h1
  | 2, _ =>
    calc GS 2 mu = (base 2 mu) ^ 11 * (Bcap mu) ^ 2 := rfl
      _ ≤ (base 2 mu) ^ 11 * (glemma mu) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (base_nonneg 2 mu h0') 11)
          exact pow_le_pow_left₀ hbcap0 hbcapg 2
      _ = ((10 + 6 * mu) / 9) ^ 11 * (glemma mu) ^ 2 := by rw [base_two]
      _ < T := bridgeC2_strict mu h0 h1
  | (n + 3), _ =>
    have hbase1mu := base_le_one_add (n + 3) mu h0
    have hbasele : (base (n + 3) mu) ^ 11 ≤ (1 + mu) ^ 11 :=
      pow_le_pow_left₀ hbase0 hbase1mu 11
    have hk3 : (3 : ℕ) ≤ n + 3 := by omega
    have hpow3 : (Bcap mu) ^ (n + 3) ≤ (Bcap mu) ^ 3 :=
      pow_le_pow_of_le_one hbcap0 hbcap1 hk3
    have hpowg : (Bcap mu) ^ 3 ≤ (glemma mu) ^ 3 :=
      pow_le_pow_left₀ hbcap0 hbcapg 3
    have hbcapk : (Bcap mu) ^ (n + 3) ≤ (glemma mu) ^ 3 := le_trans hpow3 hpowg
    calc GS (n + 3) mu = (base (n + 3) mu) ^ 11 * (Bcap mu) ^ (n + 3) := rfl
      _ ≤ (1 + mu) ^ 11 * (glemma mu) ^ 3 := by
          apply mul_le_mul hbasele hbcapk
          · exact pow_nonneg hbcap0 (n + 3)
          · exact pow_nonneg (by linarith : (0:ℚ) ≤ 1 + mu) 11
      _ < T := bridgeC3_strict mu h0 h1

/-! ## The arm line strictly below `T` for `k >= 2` -/

/-- **mu = 1, k >= 2 case.** `GS k 1 < T`. -/
theorem GS_arm_lt (k : ℕ) (hk : 2 ≤ k) : GS k 1 < T := by
  rw [GS_one_eq_armGS, T_eq_Tval]
  exact HomogMaster.armGS_lt k hk

/-! ## Main strict theorem and the equality iff -/

/-- **Strict achievable homogeneous master bound.**

For every integer `k >= 1` and every ACHIEVABLE `mu` (`mu = 1`, or `0 < mu <= 1/2`),
if `(k, mu) != (1, 1)` then `GS k mu < T` *strictly*.

This is the strictness companion to `homog_master_achievable`; every achievable
point except the arm `(1,1)` lies strictly below the bound. -/
theorem homog_master_strict (k : ℕ) (hk : 1 ≤ k) (mu : ℚ)
    (hach : mu = 1 ∨ (0 < mu ∧ mu ≤ 1 / 2)) (hne : ¬(k = 1 ∧ mu = 1)) :
    GS k mu < T := by
  rcases hach with hmu1 | ⟨h0, h12⟩
  · -- mu = 1: the arm line; not (k=1 ∧ mu=1) forces k >= 2
    subst hmu1
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exact absurd ⟨by omega, rfl⟩ hne
      · exact h
    exact GS_arm_lt k hk2
  · -- achievable 0 < mu <= 1/2: strict certs give < T for every k
    rcases le_total mu (37 / 120) with hA | hA'
    · exact GS_regionA_strict k mu hk h0 hA
    · rcases le_total mu (1 / 3) with hB | hC'
      · exact GS_regionB_strict k mu hk hA' hB
      · exact GS_regionC_strict k mu hk hC' h12

/-- **Equality characterisation.**

For every integer `k >= 1` and every ACHIEVABLE `mu`, the master bound is saturated
(`GS k mu = T`) if and only if `(k, mu) = (1, 1)` (the arm).

Forward: if `(k,mu) != (1,1)` then `homog_master_strict` gives `GS k mu < T`,
contradicting equality.  Backward: `GS_arm_eq : GS 1 1 = T`. -/
theorem homog_master_eq_iff (k : ℕ) (hk : 1 ≤ k) (mu : ℚ)
    (hach : mu = 1 ∨ (0 < mu ∧ mu ≤ 1 / 2)) :
    GS k mu = T ↔ (k = 1 ∧ mu = 1) := by
  constructor
  · intro heq
    by_contra hne
    have hlt := homog_master_strict k hk mu hach hne
    exact absurd heq (ne_of_lt hlt)
  · rintro ⟨hk1, hmu1⟩
    subst hk1; subst hmu1
    exact GS_arm_eq

end HomogMasterAssembled
