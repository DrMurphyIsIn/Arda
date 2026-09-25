import CF_Test
import CF_Arch
import CF_EData
import CF_Num
import CF_Cert
import CF_LemmaO

/-!
# CF_AxiomGuard: axiom report for the counterfeit-ladder lane (CF), 2026-09-24

Every line below must print `[propext, Classical.choice, Quot.sound]` (or a subset).  No `sorryAx`,
no `Lean.ofReduceBool` (all table checks are `decide +kernel`).

`conjecture1_proved = False`.
-/

-- CF_Test: the M-mode window test
#print axioms CF.bandM_freqData
#print axioms CF.acR_bandM
#print axioms CF.acR_bandM_zero
#print axioms CF.lorTermB_bandM
#print axioms CF.integral_bandM_exp_half
#print axioms CF.abs_integral_cos_cos_decay'
-- CF_Arch: the Gamma_C (conductor 20) functional
#print axioms CF.re_digamma_le
#print axioms CF.re_digamma_ge
#print axioms CF.psiR_le
#print axioms CF.psiD_ge
#print axioms Crux3.FreqData.pole_eq
#print axioms Crux3.FreqData.archGC_re_eq
#print axioms Crux3.FreqData.archGC_re_ge
#print axioms Crux3.FreqData.archGC_re_le
#print axioms CF.bandM_moment
-- CF_EData: E and zeta_K coefficients and weights
#print axioms CF.aEcount_tab
#print axioms CF.cE_conv
#print axioms CF.eq_cE_of_conv
#print axioms CF.chi20_eq_mul
#print axioms CF.aE_eq_half_sum
#print axioms CF.cK_eq
#print axioms CF.cK_conv
#print axioms CF.cE_six
#print axioms CF.epstein_orbit_six
-- CF_Num: the checker
#print axioms CF.blk_sum_eq
#print axioms CF.mEntry_sound
#print axioms CF.exp_le_Q
#print axioms CF.exp_ge_Q
-- CF_Cert: the instance and the separation
#print axioms CF.modeHyp0
#print axioms CF.acR_vStar
#print axioms CF.tabM_ok
#print axioms CF.tabM_tamper
#print axioms CF.Pr_ball
#print axioms CF.primeE_eq
#print axioms CF.primeK_eq
#print axioms CF.gamma_ge
#print axioms CF.cosh_le
#print axioms CF.certE_ok
#print axioms CF.certK_ok
#print axioms CF.certE_tamper
#print axioms CF.certK_tamper
#print axioms CF.epstein_window_negative
#print axioms CF.zetaK_window_pos
#print axioms CF.window_separation
#print axioms CF.window_separation_cE
-- CF_LemmaO: orbit-at-log-6 witnesses
#print axioms CF.cD_six
#print axioms CF.cD_six_ne_zero
#print axioms CF.dh_orbit_six
#print axioms CF.not_isPrimePow_six
#print axioms CF.cK_support
#print axioms CF.cE_not_primePow_supported
#print axioms CF.aE_not_mult
#print axioms CF.aD_not_mult
#print axioms CF.aK_mult_six
