/-
  Hodge1_Guard -- axiom guard for the HODGE-1 Phase 1 modules (Hodge1_Strip, Hodge1_Reduction).
  Run: lake env lean Hodge1_Guard.lean.  Expected for every line: [propext, Classical.choice, Quot.sound].
-/
import Hodge1_Reduction

#print axioms Hodge1.re_autocorr_pair_le_stripEnergy
#print axioms Hodge1.primeSide_autocorr_eq_two
#print axioms Hodge1.re_weilForm_eq_archW_sub_prime
#print axioms Hodge1.weilForm_ge_archW_sub_strip
#print axioms Hodge1.weil_positivity_pole_free_of_arch
