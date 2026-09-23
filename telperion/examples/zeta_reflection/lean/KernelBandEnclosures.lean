/-  KernelBandEnclosures.lean -- ANDURIL G2, KERNEL DISCHARGE: the three `gLine` enclosures that
    replace the Arb hypotheses hmem0/hmem1/hmem2 of `ReflectedBand_t14.pilot`.

    Consumed by `ReflectedBand_t14_Kernel` (band datum `dK`, kernel-decided `okK`, and the
    hypothesis-free `pilot_kernel`).  This module holds the analysis; that one holds only the band.

    ## Why wide boxes

    The Arb boxes of `ReflectedBand_t14.d` have relative width about 1e-75: they need `|Gamma_R|` and
    zeta at about 250 bits.  No evaluator on the island reaches that (the kernel zeta boxes used below
    are 0.016 to 0.44 wide, and nothing bounded `|Gamma_R|` at all before `KernelGammaEnvelope`).  The
    band checker only reads signs, so the boxes proved here are wide but sign-definite:

        gLine14_encl : gLine 14 in [-2^-1, -2^-37]      (true value -2.05e-6)
        gLine15_encl : gLine 15 in [ 2^-37,  2^2 ]      (true value  6.27e-6)
        gLine22_encl : gLine 22 in [-2^3,  -2^-55]      (true value -3.19e-8)

    ## How each membership is proved (all kernel-checked, no Arb input)

    `KernelGammaEnvelope.gLine_decomp_explicit` writes
        gLine t = M(t) * S(t),   S(t) = cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it),
    with `M(t) = pi^(-1/4) |Gamma(1/4 + i t/2)|` and `(3/4) exp(-pi |t|/2) <= M(t) <= 4`
    (`gammaRMag_bounds`: Euler-integral norm bound + reflection formula).  The two factors of S come from:

      * zeta boxes : `ForgeZeta14/15` (EM order 3, N = 50, existing) and `ForgeZeta22` (EM order 3,
        N = 10, new, emitted by the island's trig_forge.py);
      * phase boxes: `ForgeThetaBox.cossin_14/15` (existing) and `ForgePhi22.cossin22` (new:
        imLnVal (1/4) 11 128 + `ForgeRate.rate_at`, phase in [2.046, 2.585], so cos <= 0, sin >= 0.35).

    Then S(14) in [-0.1224, -0.0893], S(15) in [0.654, 0.769], S(22) in [-1.819, -0.1567], and the
    boxes follow by interval multiplication with the M envelope.  The inner (small) edge of every box
    is set by the crude lower bound on M, not by the zeta or phase precision; each has a margin of at
    least 2.5x.

    ## Kernel time per enclosure (measured 2026-09-23, this host)

    Every declaration below was re-checked by `Kernel.Environment.addDeclCore` (full kernel type
    check of the stored proof term, under a fresh name, in the environment of
    `ReflectedBand_t14_Kernel`), timed per declaration.  Milliseconds; "shared" items serve all three heights.

        enclosure        own theorem   zeta side                          phase side                         total
        gLine 14 box     26.7          ForgeZ14Terms 7227 + ForgeZeta14    ForgePhi14Terms 1744 + PhiFold14    ~11400
                                       351 + tail 12                       1954 + ThetaBox(14) 88
        gLine 15 box     28.2          ForgeZ15Terms 5598 + ForgeZeta15    ForgePhi15Terms 1749 + PhiFold15    ~8900
                                       377 + tail 15                       1066 + ThetaBox(15) 86
        gLine 22 box     20.2          ForgeZ22Terms 1036 + ForgeZeta22    ForgePhi22 1049                     ~2260
                                       159 (tail included)
        shared           KernelGammaEnvelope 67, ForgeRate 35, ZetaEMSum 19, ForgeTailTerms 8
        band             okK (checkLine by decide) 1.2, pilot_kernel 19.2

    The t = 22 zeta and phase boxes are the only new numerics in this discharge (t = 14 and 15
    reuse ForgeZeta14/15 and ForgeThetaBox).  The t = 22 enclosure costs about a fifth of the t = 14
    one because its sign has large margins: EM cut N = 10 instead of 50, Euler cut 128 instead of
    200, and a phase box of half-width about 0.27 rad instead of about 0.1.

    conjecture1_proved = False.  Two verified zeros at low height by finite interval arithmetic and the
    intermediate value theorem; this is not a proof of RH.
-/
import KernelGammaEnvelope
import ForgeZeta14
import ForgeZeta15
import ForgeZeta22
import ForgeThetaBox
import ForgePhi22

open XiLineZeros Complex Real ThetaGap

namespace KernelBandEnclosures

/-! ## 1.  Small interval lemmas -/

/-- `exp(-n) >= 1 / 2.7182818286^n` (Mathlib's `exp 1 < 2.7182818286`). -/
theorem exp_neg_nat_ge (n : ℕ) : (1 / (2.7182818286 : ℝ) ^ n) ≤ Real.exp (-(n : ℝ)) := by
  have h1 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have h2 : Real.exp 1 ^ n ≤ (2.7182818286 : ℝ) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  rw [Real.exp_neg, h1, one_div]
  exact inv_anti₀ (by positivity) h2

/-- Product enclosure, negative second factor. -/
theorem prod_encl_neg {M S Mlo Mhi Slo Shi : ℝ} (hM1 : Mlo ≤ M) (hM2 : M ≤ Mhi) (hMlo : 0 ≤ Mlo)
    (hS1 : Slo ≤ S) (hS2 : S ≤ Shi) (hShi : Shi ≤ 0) :
    Mhi * Slo ≤ M * S ∧ M * S ≤ Mlo * Shi := by
  have hM0 : 0 ≤ M := le_trans hMlo hM1
  have hSlo0 : Slo ≤ 0 := le_trans (le_trans hS1 hS2) hShi
  constructor
  · calc Mhi * Slo ≤ M * Slo := mul_le_mul_of_nonpos_right hM2 hSlo0
      _ ≤ M * S := mul_le_mul_of_nonneg_left hS1 hM0
  · calc M * S ≤ M * Shi := mul_le_mul_of_nonneg_left hS2 hM0
      _ ≤ Mlo * Shi := mul_le_mul_of_nonpos_right hM1 hShi

/-- Product enclosure, positive second factor. -/
theorem prod_encl_pos {M S Mlo Mhi Slo Shi : ℝ} (hM1 : Mlo ≤ M) (hM2 : M ≤ Mhi) (hMlo : 0 ≤ Mlo)
    (hS1 : Slo ≤ S) (hS2 : S ≤ Shi) (hSlo : 0 ≤ Slo) :
    Mlo * Slo ≤ M * S ∧ M * S ≤ Mhi * Shi := by
  have hM0 : 0 ≤ M := le_trans hMlo hM1
  have hShi0 : 0 ≤ Shi := le_trans hSlo (le_trans hS1 hS2)
  constructor
  · calc Mlo * Slo ≤ M * Slo := mul_le_mul_of_nonneg_right hM1 hSlo
      _ ≤ M * S := mul_le_mul_of_nonneg_left hS1 hM0
  · calc M * S ≤ M * Shi := mul_le_mul_of_nonneg_left hS2 hM0
      _ ≤ Mhi * Shi := mul_le_mul_of_nonneg_right hM2 hShi0

/-! ## 2.  The three `gLine` enclosures (the discharged `hmem` facts, in numeric form) -/

/-- **`gLine 14` in `[-2^-1, -2^-37]`.** -/
theorem gLine14_encl : (-(1/2) : ℝ) ≤ gLine 14 ∧ gLine 14 ≤ -(1/137438953472) := by
  obtain ⟨Λ, hΛ, hdec⟩ := KernelGammaEnvelope.gLine_decomp_explicit 14 (by norm_num)
  obtain ⟨hc1, hc2, hs1, hs2⟩ := ForgeThetaBox.cossin_14 Λ hΛ
  obtain ⟨hR1, hR2⟩ := ForgeZeta14.zt14_zeta_re
  obtain ⟨hJ1, hJ2⟩ := ForgeZeta14.zt14_zeta_im
  have hb : ((1/2:ℂ) + (14:ℂ) * Complex.I) = ((1/2:ℂ) + ((14:ℝ):ℂ) * I) := by push_cast; ring
  rw [hb] at hR1 hR2 hJ1 hJ2
  obtain ⟨hM1, hM2⟩ := KernelGammaEnvelope.gammaRMag_bounds 14
  have hE : (1 / (2.7182818286:ℝ) ^ 22) ≤ Real.exp (-(Real.pi * |(14:ℝ) / 2|)) := by
    rw [abs_of_pos (show (0:ℝ) < 14 / 2 by norm_num)]
    refine le_trans (exp_neg_nat_ge 22) (Real.exp_le_exp.mpr ?_)
    have := Real.pi_lt_d4
    push_cast; linarith
  set c := Real.cos (Λ - 14 / 2 * Real.log Real.pi)
  set s := Real.sin (Λ - 14 / 2 * Real.log Real.pi)
  set R := (riemannZeta ((1/2:ℂ) + ((14:ℝ):ℂ) * I)).re
  set J := (riemannZeta ((1/2:ℂ) + ((14:ℝ):ℂ) * I)).im
  set M := KernelGammaEnvelope.gammaRMag 14
  -- S = c R - s J in [-0.1224, -0.0893]
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
  have hS2 : c * R - s * J ≤ -893 / 10000 := by
    have h1 : c * R ≤ (-6/100) * R := mul_le_mul_of_nonneg_right hc2 hR0
    have h2 : (-6/100 : ℝ) * R ≤ (-6/100) * (16293603109527569 / 1152921504606846976) :=
      mul_le_mul_of_nonpos_left hR1 (by norm_num)
    have h3 : (-93/100 : ℝ) * J ≤ s * J := mul_le_mul_of_nonpos_right hs2 (le_trans hJ2 (by norm_num))
    have h4 : (-93/100 : ℝ) * (-109668107004231189 / 1152921504606846976) ≤ (-93/100) * J :=
      mul_le_mul_of_nonpos_left hJ2 (by norm_num)
    linarith
  have hS1 : -1224 / 10000 ≤ c * R - s * J := by
    have h1 : (-36/100 : ℝ) * R ≤ c * R := mul_le_mul_of_nonneg_right hc1 hR0
    have h2 : (-36/100 : ℝ) * (8750969458477793 / 288230376151711744) ≤ (-36/100) * R :=
      mul_le_mul_of_nonpos_left hR2 (by norm_num)
    have h3 : s * J ≤ (-100/100 : ℝ) * J :=
      mul_le_mul_of_nonpos_right hs1 (le_trans hJ2 (by norm_num))
    have h4 : (-100/100 : ℝ) * J ≤ (-100/100) * (-128427663091229467 / 1152921504606846976) :=
      mul_le_mul_of_nonpos_left hJ1 (by norm_num)
    linarith
  have hMlo : (3/4) * (1 / (2.7182818286:ℝ) ^ 22) ≤ M :=
    le_trans (mul_le_mul_of_nonneg_left hE (by norm_num)) hM1
  obtain ⟨hp1, hp2⟩ := prod_encl_neg hMlo hM2 (by positivity) hS1 hS2 (by norm_num)
  rw [hdec]
  constructor
  · refine le_trans (by norm_num) hp1
  · refine le_trans hp2 (by norm_num)

/-- **`gLine 15` in `[2^-37, 2^2]`.** -/
theorem gLine15_encl : (1/137438953472 : ℝ) ≤ gLine 15 ∧ gLine 15 ≤ 4 := by
  obtain ⟨Λ, hΛ, hdec⟩ := KernelGammaEnvelope.gLine_decomp_explicit 15 (by norm_num)
  obtain ⟨hc1, hc2, hs1, hs2⟩ := ForgeThetaBox.cossin_15 Λ hΛ
  obtain ⟨hR1, hR2⟩ := ForgeZeta15.zt15_zeta_re
  obtain ⟨hJ1, hJ2⟩ := ForgeZeta15.zt15_zeta_im
  have hb : ((1/2:ℂ) + (15:ℂ) * Complex.I) = ((1/2:ℂ) + ((15:ℝ):ℂ) * I) := by push_cast; ring
  rw [hb] at hR1 hR2 hJ1 hJ2
  obtain ⟨hM1, hM2⟩ := KernelGammaEnvelope.gammaRMag_bounds 15
  have hE : (1 / (2.7182818286:ℝ) ^ 24) ≤ Real.exp (-(Real.pi * |(15:ℝ) / 2|)) := by
    rw [abs_of_pos (show (0:ℝ) < 15 / 2 by norm_num)]
    refine le_trans (exp_neg_nat_ge 24) (Real.exp_le_exp.mpr ?_)
    have := Real.pi_lt_d4
    push_cast; linarith
  set c := Real.cos (Λ - 15 / 2 * Real.log Real.pi)
  set s := Real.sin (Λ - 15 / 2 * Real.log Real.pi)
  set R := (riemannZeta ((1/2:ℂ) + ((15:ℝ):ℂ) * I)).re
  set J := (riemannZeta ((1/2:ℂ) + ((15:ℝ):ℂ) * I)).im
  set M := KernelGammaEnvelope.gammaRMag 15
  -- S = c R - s J in [0.654, 0.769]
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
  have hJ0 : 0 ≤ J := le_trans (by norm_num) hJ1
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc1
  have hS1 : 654 / 1000 ≤ c * R - s * J := by
    have h1 : (5/100 : ℝ) * R ≤ c * R := mul_le_mul_of_nonneg_right hc1 hR0
    have h2 : (5/100 : ℝ) * (79736512093489793 / 576460752303423488) ≤ (5/100) * R :=
      mul_le_mul_of_nonneg_left hR1 (by norm_num)
    have h3 : s * J ≤ (-93/100 : ℝ) * J := mul_le_mul_of_nonneg_right hs2 hJ0
    have h4 : (-93/100 : ℝ) * J ≤ (-93/100) * (200594983225468989 / 288230376151711744) :=
      mul_le_mul_of_nonpos_left hJ1 (by norm_num)
    linarith
  have hS2 : c * R - s * J ≤ 769 / 1000 := by
    have h1 : c * R ≤ (35/100 : ℝ) * R := mul_le_mul_of_nonneg_right hc2 hR0
    have h2 : (35/100 : ℝ) * R ≤ (35/100) * (44931265996841455 / 288230376151711744) :=
      mul_le_mul_of_nonneg_left hR2 (by norm_num)
    have h3 : (-100/100 : ℝ) * J ≤ s * J := mul_le_mul_of_nonneg_right hs1 hJ0
    have h4 : (-100/100 : ℝ) * (205669604490296197 / 288230376151711744) ≤ (-100/100) * J :=
      mul_le_mul_of_nonpos_left hJ2 (by norm_num)
    linarith
  have hMlo : (3/4) * (1 / (2.7182818286:ℝ) ^ 24) ≤ M :=
    le_trans (mul_le_mul_of_nonneg_left hE (by norm_num)) hM1
  obtain ⟨hp1, hp2⟩ := prod_encl_pos hMlo hM2 (by positivity) hS1 hS2 (by norm_num)
  rw [hdec]
  constructor
  · refine le_trans (by norm_num) hp1
  · refine le_trans hp2 (by norm_num)

/-- **`gLine 22` in `[-2^3, -2^-55]`.** -/
theorem gLine22_encl : (-8 : ℝ) ≤ gLine 22 ∧ gLine 22 ≤ -(1/36028797018963968) := by
  obtain ⟨Λ, hΛ, hdec⟩ := KernelGammaEnvelope.gLine_decomp_explicit 22 (by norm_num)
  have h11 : ((22:ℝ) / 2) = 11 := by norm_num
  rw [h11] at hΛ hdec
  obtain ⟨hc2, hs1⟩ := ForgePhi22.cossin22 Λ hΛ
  obtain ⟨hR1, hR2⟩ := ForgeZeta22.zt22_zeta_re
  obtain ⟨hJ1, hJ2⟩ := ForgeZeta22.zt22_zeta_im
  have hb : ((1/2:ℂ) + (22:ℂ) * Complex.I) = ((1/2:ℂ) + ((22:ℝ):ℂ) * I) := by push_cast; ring
  rw [hb] at hR1 hR2 hJ1 hJ2
  obtain ⟨hM1, hM2⟩ := KernelGammaEnvelope.gammaRMag_bounds 22
  have hE : (1 / (2.7182818286:ℝ) ^ 35) ≤ Real.exp (-(Real.pi * |(22:ℝ) / 2|)) := by
    rw [abs_of_pos (show (0:ℝ) < 22 / 2 by norm_num)]
    refine le_trans (exp_neg_nat_ge 35) (Real.exp_le_exp.mpr ?_)
    have := Real.pi_lt_d4
    push_cast; linarith
  set c := Real.cos (Λ - 11 * Real.log Real.pi)
  set s := Real.sin (Λ - 11 * Real.log Real.pi)
  set R := (riemannZeta ((1/2:ℂ) + ((22:ℝ):ℂ) * I)).re
  set J := (riemannZeta ((1/2:ℂ) + ((22:ℝ):ℂ) * I)).im
  set M := KernelGammaEnvelope.gammaRMag 22
  have hc1 : -1 ≤ c := Real.neg_one_le_cos _
  have hs2 : s ≤ 1 := Real.sin_le_one _
  -- S = c R - s J in [-1.819, -0.1567]
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
  have hJ0 : 0 ≤ J := le_trans (by norm_num) hJ1
  have hS2 : c * R - s * J ≤ -1567 / 10000 := by
    have h1 : c * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc2 hR0
    have h2 : ((7:ℝ) / 20) * J ≤ s * J := mul_le_mul_of_nonneg_right hs1 hJ0
    have h3 : ((7:ℝ) / 20) * (258147160874351687 / 576460752303423488) ≤ ((7:ℝ) / 20) * J :=
      mul_le_mul_of_nonneg_left hJ1 (by norm_num)
    linarith
  have hS1 : -1819 / 1000 ≤ c * R - s * J := by
    have h1 : (-1 : ℝ) * R ≤ c * R := mul_le_mul_of_nonneg_right hc1 hR0
    have h2 : s * J ≤ 1 * J := mul_le_mul_of_nonneg_right hs2 hJ0
    linarith
  have hMlo : (3/4) * (1 / (2.7182818286:ℝ) ^ 35) ≤ M :=
    le_trans (mul_le_mul_of_nonneg_left hE (by norm_num)) hM1
  obtain ⟨hp1, hp2⟩ := prod_encl_neg hMlo hM2 (by positivity) hS1 hS2 (by norm_num)
  rw [hdec]
  constructor
  · refine le_trans (by norm_num) hp1
  · refine le_trans hp2 (by norm_num)

end KernelBandEnclosures
