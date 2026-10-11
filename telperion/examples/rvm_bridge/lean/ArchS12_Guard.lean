/-
  ArchS12_Guard -- `#print axioms` for every top-level theorem of stage S12.
  Required output: exactly [propext, Classical.choice, Quot.sound] (no sorryAx, no new axioms).
  Check: `lake build ArchS12_Main && lake env lean ArchS12_Guard.lean`.
  conjecture1_proved = False.
-/
import ArchS12_Index
import ArchS12_Bridge

-- A3: the certified enumeration
#print axioms ArchS12.disjOK_eq
#print axioms ArchS12.window_sep
#print axioms ArchS12.window_unique
#print axioms ArchS12.T_phiR'
#print axioms ArchS12.ip_phiR'
#print axioms ArchS12.window_existsUnique
#print axioms ArchS12.winIdx_spec
#print axioms ArchS12.winIdx_injective
#print axioms ArchS12.exists_equiv_prefix
#print axioms ArchS12.exists_certBasis_enumeration
#print axioms ArchS12.exists_certified_prolate

-- A1 + A2: translation and Lp-to-function bridge; S11 on [-L, L]
#print axioms ArchS12.toLpI_ae
#print axioms ArchS12.integral_volI_of_vanish
#print axioms ArchS12.inner_one_toLpI
#print axioms ArchS12.norm_sq_toLpI
#print axioms ArchS12.integrable_double
#print axioms ArchS12.re_inner_toLpI
#print axioms ArchS12.double_integral_translate
#print axioms ArchS12.integral_translate
#print axioms ArchS12.integral_conj_mul_translate
#print axioms ArchS12.chiK_eq_chiT
#print axioms ArchS12.vanish_of_tsupport
#print axioms ArchS12.double_chi_eq_chiT
#print axioms ArchS12.vanish_translate
#print axioms ArchS12.re_double_chi_eq_inner
#print axioms ArchS12.norm_sq_translate
#print axioms ArchS12.inner_one_translate
#print axioms ArchS12.form_chi_half
#print axioms ArchS12.form_chi_log2
