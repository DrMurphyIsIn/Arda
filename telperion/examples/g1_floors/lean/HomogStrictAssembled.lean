import Mathlib
import HomogMaster
import HomogMasterAssembled
import HomogStrict

/-!
# Strictness-iff for the achievable homogeneous master inequality

Companion to `HomogMasterAssembled.homog_master_achievable` (`GS k mu <= T`).
Here we prove the STRICT bound `GS k mu < T` for every achievable `(k, mu)` EXCEPT the
arm `(k,mu) = (1,1)`, and assemble the equality characterisation
`GS k mu = T <-> (k = 1 and mu = 1)`.

Route: on `0 < mu <= 1/2` the interval certs are strengthened to `0 < P` (see
`HomogStrict`), giving strict bridges `... < T`; the structural `base/Bcap` bounds stay
non-strict and compose via `lt_of_le_of_lt`.  On the arm line `mu = 1`, `k >= 2` gives
`armGS k <= armGS 2 < T` (`armGS 2 = (16/9)^11 (64/621)^2 < T`).  Kernel-clean.
`conjecture1_proved = False`.
-/

namespace HomogMasterAssembled

open HomogMaster

/-- Strict bridge A: `(7/6 + mu/2)^11 < T` on `[0, 37/120]`. -/
theorem bridgeA_strict (mu : ℚ) (h0 : 0 ≤ mu) (h1 : mu ≤ 37 / 120) :
    (7 / 6 + mu / 2) ^ 11 < T := by
  have h0R : (0 : ℝ) ≤ (mu : ℝ) := by exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 37 / 120 := by
    rw [show (37:ℝ)/120 = ((37/120 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMaster.certA_small_mu_strict (mu : ℝ) h0R h1R
  have heq : (-(mu:ℝ)^11/2048 - 77*(mu:ℝ)^10/6144 - 2695*(mu:ℝ)^9/18432 - 18865*(mu:ℝ)^8/18432 - 132055*(mu:ℝ)^7/27648 - 1294139*(mu:ℝ)^6/82944 - 9058973*(mu:ℝ)^5/248832 - 45294865*(mu:ℝ)^4/746496 - 317064055*(mu:ℝ)^3/4478976 - 2219448385*(mu:ℝ)^2/40310784 - 3107227739*(mu:ℝ)/120932352 + 5172080092597/225296971776)
      = (64/621) * (5/3)^11 - (7/6 + (mu:ℝ)/2)^11 := by ring
  rw [heq] at hR
  have key : ((7 / 6 + mu / 2) ^ 11 : ℚ) < T := by
    have hcast : (((7 / 6 + mu / 2) ^ 11 : ℚ) : ℝ) < (T : ℝ) := by
      rw [T_cast]; push_cast; linarith
    exact_mod_cast hcast
  exact key

/-- Strict bridge B_strict: strict `... * (glemma mu)^1 < T`. -/
theorem bridgeB_strict (mu : ℚ) (h0 : 37/120 ≤ mu) (h1 : mu ≤ 1/3) :
    (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 < T := by
  have h0R : (37/120 : ℝ) ≤ (mu : ℝ) := by
    rw [show (37/120:ℝ) = ((37/120 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/3 := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMaster.certB_mid_strict (mu : ℝ) h0R h1R
  have heq : (-568847656250*(mu:ℝ)^11/448215674395347 - 4691113281250*(mu:ℝ)^10/149405224798449 - 17364746093750*(mu:ℝ)^9/49801741599483 - 12627441406250*(mu:ℝ)^8/5533526844387 - 1987304687500*(mu:ℝ)^7/204945438681 - 153142773437500*(mu:ℝ)^6/5533526844387 - 872761914062500*(mu:ℝ)^5/16600580533161 - 3082997070312500*(mu:ℝ)^4/49801741599483 - 5026833496093750*(mu:ℝ)^3/149405224798449 + 16685071777343750*(mu:ℝ)^2/1344647023186041 + 116730331738281250*(mu:ℝ)/4033941069558123 + 150677582128906250/12101823208674369)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 := by
    have hcast : (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have hpos : (0:ℝ) < (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast hpos
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 11 := by positivity
  have hglem : (glemma mu) ^ 1 = GAMMA ^ 1 / (1 + mu / 3) ^ 11 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-- Strict bridge C1_strict: strict `... * (glemma mu)^1 < T`. -/
theorem bridgeC1_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMaster.certC1_k1_strict (mu : ℝ) h0R h1R
  have heq : (-568847656250*(mu:ℝ)^11/448215674395347 - 4691113281250*(mu:ℝ)^10/149405224798449 - 17364746093750*(mu:ℝ)^9/49801741599483 - 12627441406250*(mu:ℝ)^8/5533526844387 - 1987304687500*(mu:ℝ)^7/204945438681 - 153142773437500*(mu:ℝ)^6/5533526844387 - 872761914062500*(mu:ℝ)^5/16600580533161 - 3082997070312500*(mu:ℝ)^4/49801741599483 - 5026833496093750*(mu:ℝ)^3/149405224798449 + 16685071777343750*(mu:ℝ)^2/1344647023186041 + 116730331738281250*(mu:ℝ)/4033941069558123 + 150677582128906250/12101823208674369)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 := by
    have hcast : (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^11 - (7/6 + (mu:ℝ)/2)^11*((64/621)^2 * (5/3)^11)^1 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have hpos : (0:ℝ) < (((T * (1 + mu / 3) ^ 11 - (7 / 6 + mu / 2) ^ 11 * GAMMA ^ 1 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast hpos
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 11 := by positivity
  have hglem : (glemma mu) ^ 1 = GAMMA ^ 1 / (1 + mu / 3) ^ 11 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

-- Strict bridge C2_strict: strict `... * (glemma mu)^2 < T`.
set_option maxHeartbeats 660000 in
theorem bridgeC2_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    ((10 + 6 * mu) / 9) ^ 11 * (glemma mu) ^ 2 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMaster.certC2_k2_strict (mu : ℝ) h0R h1R
  have heq : (3125000000*(mu:ℝ)^22/3452176611830979783 + 68750000000*(mu:ℝ)^21/1150725537276993261 + 240625000000*(mu:ℝ)^20/127858393030777029 + 4812500000000*(mu:ℝ)^19/127858393030777029 + 22859375000000*(mu:ℝ)^18/42619464343592343 + 9143750000000*(mu:ℝ)^17/1578498679392309 + 77721875000000*(mu:ℝ)^16/1578498679392309 + 177650000000000*(mu:ℝ)^15/526166226464103 + 111031250000000*(mu:ℝ)^14/58462914051567 + 1554437500000000*(mu:ℝ)^13/175388742154701 + 2020768750000000*(mu:ℝ)^12/58462914051567 + 93440078858813577325000000000*(mu:ℝ)^11/826737822113891853061955763 + 767050890585212012931250000000*(mu:ℝ)^10/2480213466341675559185867289 + 5228904934820698551062500000000*(mu:ℝ)^9/7440640399025026677557601867 + 9738350945725632919906250000000*(mu:ℝ)^8/7440640399025026677557601867 + 43815444539483038015550000000000*(mu:ℝ)^7/22321921197075080032672805601 + 155275312874214462186228125000000*(mu:ℝ)^6/66965763591225240098018416803 + 421336640894563585768018750000000*(mu:ℝ)^5/200897290773675720294055250409 + 842141602236408964420046875000000*(mu:ℝ)^4/602691872321027160882165751227 + 1169531456868985406269562500000000*(mu:ℝ)^3/1808075616963081482646497253681 + 3064602400319390895391728125000000*(mu:ℝ)^2/16272680552667733343818475283129 + 1369659200273763624621481250000000*(mu:ℝ)/48818041658003200031455425849387 + 160315127384721482799696875000000/146454124974009600094366277548161)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^22 - ((10 + 6*(mu:ℝ))/9)^11*((64/621)^2 * (5/3)^11)^2 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 := by
    have hcast : (((T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^22 - ((10 + 6*(mu:ℝ))/9)^11*((64/621)^2 * (5/3)^11)^2 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have hpos : (0:ℝ) < (((T * (1 + mu / 3) ^ 22 - ((10 + 6 * mu) / 9) ^ 11 * GAMMA ^ 2 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast hpos
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 22 := by positivity
  have hglem : (glemma mu) ^ 2 = GAMMA ^ 2 / (1 + mu / 3) ^ 22 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

-- Strict bridge C3_strict: strict `... * (glemma mu)^3 < T`.
set_option maxHeartbeats 1020000 in
theorem bridgeC3_strict (mu : ℚ) (h0 : 1/3 ≤ mu) (h1 : mu ≤ 1/2) :
    (1 + mu) ^ 11 * (glemma mu) ^ 3 < T := by
  have h0R : (1/3 : ℝ) ≤ (mu : ℝ) := by
    rw [show (1/3:ℝ) = ((1/3 : ℚ):ℝ) by norm_num]; exact_mod_cast h0
  have h1R : (mu : ℝ) ≤ 1/2 := by
    rw [show (1/2:ℝ) = ((1/2 : ℚ):ℝ) by norm_num]; exact_mod_cast h1
  have hR := HomogMaster.certC3_kge3_strict (mu : ℝ) h0R h1R
  have heq : (3125000000*(mu:ℝ)^33/611542730256022575619101 + 34375000000*(mu:ℝ)^32/67949192250669175068789 + 550000000000*(mu:ℝ)^31/22649730750223058356263 + 17050000000000*(mu:ℝ)^30/22649730750223058356263 + 42625000000000*(mu:ℝ)^29/2516636750024784261807 + 247225000000000*(mu:ℝ)^28/838878916674928087269 + 3461150000000000*(mu:ℝ)^27/838878916674928087269 + 494450000000000*(mu:ℝ)^26/10356529835492939349 + 1606962500000000*(mu:ℝ)^25/3452176611830979783 + 40174062500000000*(mu:ℝ)^24/10356529835492939349 + 32139250000000000*(mu:ℝ)^23/1150725537276993261 + 2921750000000000*(mu:ℝ)^22/16677181699666569 + 16069625000000000*(mu:ℝ)^21/16677181699666569 + 8652875000000000*(mu:ℝ)^20/1853020188851841 + 12361250000000000*(mu:ℝ)^19/617673396283947 + 46972750000000000*(mu:ℝ)^18/617673396283947 + 5871593750000000*(mu:ℝ)^17/22876792454961 + 5871593750000000*(mu:ℝ)^16/7625597484987 + 46972750000000000*(mu:ℝ)^15/22876792454961 + 12361250000000000*(mu:ℝ)^14/2541865828329 + 8652875000000000*(mu:ℝ)^13/847288609443 + 16069625000000000*(mu:ℝ)^12/847288609443 + 9886758546972783385527505750000000000*(mu:ℝ)^11/318824000457823368106665682399083 + 14108827480439210944452508250000000000*(mu:ℝ)^10/318824000457823368106665682399083 + 17306034350549013680565635312500000000*(mu:ℝ)^9/318824000457823368106665682399083 + 5948572366197644925003628712500000000*(mu:ℝ)^8/106274666819274456035555227466361 + 5017143722643979930772580350000000000*(mu:ℝ)^7/106274666819274456035555227466361 + 3354667339834206612823118050000000000*(mu:ℝ)^6/106274666819274456035555227466361 + 1716571861321989965386290175000000000*(mu:ℝ)^5/106274666819274456035555227466361 + 645123376545856878648081125000000000*(mu:ℝ)^4/106274666819274456035555227466361 + 170049350618342751459232450000000000*(mu:ℝ)^3/106274666819274456035555227466361 + 91333305377266267399976650000000000*(mu:ℝ)^2/318824000457823368106665682399083 + 11624994758237425137495621875000000*(mu:ℝ)/318824000457823368106665682399083 + 1056817705294311376135965625000000/318824000457823368106665682399083)
      = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^33 - (1 + (mu:ℝ))^11*((64/621)^2 * (5/3)^11)^3 := by ring
  rw [heq] at hR
  have hRq : (0 : ℚ) < T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 := by
    have hcast : (((T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 : ℚ)) : ℝ)
        = (64/621) * (5/3)^11*(1+(mu:ℝ)/3)^33 - (1 + (mu:ℝ))^11*((64/621)^2 * (5/3)^11)^3 := by
      simp only [T, GAMMA, W]; push_cast; ring
    have hpos : (0:ℝ) < (((T * (1 + mu / 3) ^ 33 - (1 + mu) ^ 11 * GAMMA ^ 3 : ℚ)) : ℝ) := by
      rw [hcast]; exact hR
    exact_mod_cast hpos
  have hden : (0 : ℚ) < (1 + mu / 3) ^ 33 := by positivity
  have hglem : (glemma mu) ^ 3 = GAMMA ^ 3 / (1 + mu / 3) ^ 33 := by
    simp only [glemma, div_pow]; rw [← pow_mul]
  rw [hglem, ← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith [hRq]

/-! ## Strict region lemmas (0 < mu <= 1/2) -/

/-- Region A strict: `GS k mu < T` on `0 < mu ≤ 37/120`. -/
theorem GS_regionA_lt (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 0 < mu) (h1 : mu ≤ 37 / 120) :
    GS k mu < T := by
  have h0' : 0 ≤ mu := le_of_lt h0
  have hmu13 : mu ≤ 1 / 3 := le_trans h1 (by norm_num)
  have hbcap0 := Bcap_nonneg mu h0'
  have hbcap1 := Bcap_le_one mu
  have hbase0 := base_nonneg k mu h0'
  have hbase1 := base_le_base_one k mu hk hmu13
  have hstep : GS k mu ≤ (7 / 6 + mu / 2) ^ 11 := by
    calc GS k mu = (base k mu) ^ 11 * (Bcap mu) ^ k := rfl
      _ ≤ (base 1 mu) ^ 11 * 1 := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ hbase0 hbase1 11
          · exact pow_le_one₀ hbcap0 hbcap1
          · exact pow_nonneg hbcap0 k
          · exact pow_nonneg (base_nonneg 1 mu h0') 11
      _ = (7 / 6 + mu / 2) ^ 11 := by rw [base_one]; ring
  exact lt_of_le_of_lt hstep (bridgeA_strict mu h0' h1)

/-- Region B strict: `GS k mu < T` on `37/120 ≤ mu ≤ 1/3`. -/
theorem GS_regionB_lt (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 37 / 120 ≤ mu) (h1 : mu ≤ 1 / 3) :
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
  have hstep : GS k mu ≤ (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by
    calc GS k mu = (base k mu) ^ 11 * (Bcap mu) ^ k := rfl
      _ ≤ (base 1 mu) ^ 11 * glemma mu := by
          apply mul_le_mul (pow_le_pow_left₀ hbase0 hbase1 11) (le_trans hpow hbcapg)
          · exact pow_nonneg hbcap0 k
          · exact pow_nonneg (base_nonneg 1 mu h0') 11
      _ = (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by rw [base_one]; ring
  exact lt_of_le_of_lt hstep (bridgeB_strict mu h0 h1)

/-- Region C strict: `GS k mu < T` on `1/3 ≤ mu ≤ 1/2`. -/
theorem GS_regionC_lt (k : ℕ) (mu : ℚ) (hk : 1 ≤ k) (h0 : 1 / 3 ≤ mu) (h1 : mu ≤ 1 / 2) :
    GS k mu < T := by
  have h0' : 0 ≤ mu := le_trans (by norm_num) h0
  have hbcap0 := Bcap_nonneg mu h0'
  have hbcap1 := Bcap_le_one mu
  have hbcapg := Bcap_le_glemma mu
  have hglem0 := glemma_nonneg mu h0'
  have hbase0 := base_nonneg k mu h0'
  match k, hk with
  | 1, _ =>
    have hstep : GS 1 mu ≤ (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by
      calc GS 1 mu = (base 1 mu) ^ 11 * (Bcap mu) ^ 1 := rfl
        _ ≤ (base 1 mu) ^ 11 * glemma mu := by
            rw [pow_one]
            apply mul_le_mul_of_nonneg_left hbcapg
            exact pow_nonneg (base_nonneg 1 mu h0') 11
        _ = (7 / 6 + mu / 2) ^ 11 * (glemma mu) ^ 1 := by rw [base_one]; ring
    exact lt_of_le_of_lt hstep (bridgeC1_strict mu h0 h1)
  | 2, _ =>
    have hstep : GS 2 mu ≤ ((10 + 6 * mu) / 9) ^ 11 * (glemma mu) ^ 2 := by
      calc GS 2 mu = (base 2 mu) ^ 11 * (Bcap mu) ^ 2 := rfl
        _ ≤ (base 2 mu) ^ 11 * (glemma mu) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (base_nonneg 2 mu h0') 11)
            exact pow_le_pow_left₀ hbcap0 hbcapg 2
        _ = ((10 + 6 * mu) / 9) ^ 11 * (glemma mu) ^ 2 := by rw [base_two]
    exact lt_of_le_of_lt hstep (bridgeC2_strict mu h0 h1)
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
    have hstep : GS (n + 3) mu ≤ (1 + mu) ^ 11 * (glemma mu) ^ 3 := by
      calc GS (n + 3) mu = (base (n + 3) mu) ^ 11 * (Bcap mu) ^ (n + 3) := rfl
        _ ≤ (1 + mu) ^ 11 * (glemma mu) ^ 3 := by
            apply mul_le_mul hbasele hbcapk
            · exact pow_nonneg hbcap0 (n + 3)
            · exact pow_nonneg (by linarith : (0:ℚ) ≤ 1 + mu) 11
    exact lt_of_le_of_lt hstep (bridgeC3_strict mu h0 h1)

/-! ## Arm line `mu = 1`, `k >= 2` -/

/-- `armGS 2 < Tval` exactly (`(16/9)^11 (64/621)^2 < (5/3)^11 (64/621)`). -/
theorem armGS_two_lt : HomogMaster.armGS 2 < HomogMaster.Tval := by
  unfold HomogMaster.armGS HomogMaster.Tval; norm_num

/-- For `k ≥ 2`, `armGS k ≤ armGS 2` (monotone decreasing arm line). -/
theorem armGS_le_two (k : ℕ) (hk : 2 ≤ k) : HomogMaster.armGS k ≤ HomogMaster.armGS 2 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge 2 (n + 1) with h | h
    · have hn2 : 2 ≤ n := by omega
      have hn1 : 1 ≤ n := by omega
      exact le_trans (HomogMaster.armGS_step n hn1) (ih hn2)
    · have hn : n + 1 = 2 := by omega
      rw [hn]

/-- Arm line strict: `armGS k < Tval` for `k ≥ 2`. -/
theorem armGS_lt_T (k : ℕ) (hk : 2 ≤ k) : HomogMaster.armGS k < HomogMaster.Tval :=
  lt_of_le_of_lt (armGS_le_two k hk) armGS_two_lt

/-- `GS k 1 < T` for `k ≥ 2` (arm line above the tip). -/
theorem GS_arm_lt (k : ℕ) (hk : 2 ≤ k) : GS k 1 < T := by
  rw [GS_one_eq_armGS, T_eq_Tval]
  exact armGS_lt_T k hk

/-! ## Main strictness theorem and the equality iff -/

/-- **Strict achievable homogeneous master bound.**

For every integer `k ≥ 1` and every ACHIEVABLE `mu` (`mu = 1`, or `0 < mu ≤ 1/2`),
`GS k mu < T` UNLESS `(k, mu) = (1, 1)` (the arm tip, where `GS 1 1 = T`).
`conjecture1_proved = False`. -/
theorem GS_lt_T_of_not_arm (k : ℕ) (hk : 1 ≤ k) (mu : ℚ)
    (hach : mu = 1 ∨ (0 < mu ∧ mu ≤ 1 / 2)) (hne : ¬ (k = 1 ∧ mu = 1)) :
    GS k mu < T := by
  rcases hach with hmu1 | ⟨h0, h12⟩
  · -- arm line mu = 1: not-arm forces k ≥ 2
    subst hmu1
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso; exact hne ⟨by omega, rfl⟩
      · exact h
    exact GS_arm_lt k hk2
  · -- 0 < mu ≤ 1/2: strict everywhere via region certs
    rcases le_total mu (37 / 120) with hA | hA'
    · exact GS_regionA_lt k mu hk h0 hA
    · rcases le_total mu (1 / 3) with hB | hC'
      · exact GS_regionB_lt k mu hk hA' hB
      · exact GS_regionC_lt k mu hk hC' h12

/-- **Equality characterisation (strictness-iff).**

On the achievable domain, the homogeneous master inequality is saturated iff at the arm
tip: `GS k mu = T <-> (k = 1 and mu = 1)`. -/
theorem GS_eq_T_iff_arm (k : ℕ) (hk : 1 ≤ k) (mu : ℚ)
    (hach : mu = 1 ∨ (0 < mu ∧ mu ≤ 1 / 2)) :
    GS k mu = T ↔ (k = 1 ∧ mu = 1) := by
  constructor
  · intro heqT
    by_contra hne
    exact absurd heqT (ne_of_lt (GS_lt_T_of_not_arm k hk mu hach hne))
  · rintro ⟨hk1, hmu1⟩
    subst hk1; subst hmu1
    exact GS_arm_eq

end HomogMasterAssembled
