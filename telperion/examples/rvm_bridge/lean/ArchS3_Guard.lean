/-
  ArchS3_Guard -- axiom guard for stage S3 (structural positivity L = W_inf + D >= 0, CC Cor 2.3).
  Required output for every line: [propext, Classical.choice, Quot.sound].
  Run:  lake build ArchS3_Mellin && lake env lean ArchS3_Guard.lean
-/
import ArchS3_Mellin

-- M1: the kernel delta (CC (48)/(49)) and its properties
#print axioms ArchS3.integral_cos_mul_neg_log
#print axioms ArchS3.ccDelta_eq
#print axioms ArchS3.deltaK_eq_ccDelta
#print axioms ArchS3.deltaK_zero
#print axioms ArchS3.continuous_deltaK
#print axioms ArchS3.abs_Si_le
#print axioms ArchS3.abs_deltaK_le
#print axioms ArchS3.integrable_deltaK
#print axioms ArchS3.continuous_deltaHat
#print axioms ArchS3.pairing_deltaK
-- M1: the functional L = W_inf + D
#print axioms ArchS3.Lfun_eq_integral_ell
#print axioms ArchS3.archW_eq_dirichlet
#print axioms ArchS3.Lfun_eq_dirichlet
#print axioms ArchS3.re_archSide_eq_poles_add_archW
#print axioms ArchS3.re_weilForm_eq_archW
#print axioms ArchS3.Lfun_nonneg_of_ell_nonneg
-- M2a: the Mellin transform of cos on the critical strip
#print axioms ArchS3.gInt_eq
#print axioms ArchS3.integral_log_gInt
#print axioms ArchS3.integral_cosD
#print axioms ArchS3.integral_log_cosD
#print axioms ArchS3.tendsto_PsiE
#print axioms ArchS3.tendsto_dPsiE
#print axioms ArchS3.hasDerivAt_PsiE
#print axioms ArchS3.Psi_eq_Gammaℂ
#print axioms ArchS3.Psi_eq_Gammaℝ
#print axioms ArchS3.norm_Psi_zt
#print axioms ArchS3.re_dPsi_mul_conj_Psi
