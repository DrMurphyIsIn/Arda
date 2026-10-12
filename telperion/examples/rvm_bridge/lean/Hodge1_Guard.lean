/-
  Hodge1_Guard -- axiom guard for the HODGE-1 Phase 1 modules (Hodge1_Strip, Hodge1_Reduction) and the
  Phase 1b-A strip certificate (Hodge1_KPen ... Hodge1_Window45).
  Run: lake env lean Hodge1_Guard.lean.  Expected for every line: [propext, Classical.choice, Quot.sound].
-/
import Hodge1_Reduction
import Hodge1_Window45

#print axioms Hodge1.re_autocorr_pair_le_stripEnergy
#print axioms Hodge1.primeSide_autocorr_eq_two
#print axioms Hodge1.re_weilForm_eq_archW_sub_prime
#print axioms Hodge1.weilForm_ge_archW_sub_strip
#print axioms Hodge1.weil_positivity_pole_free_of_arch
#print axioms Hodge1.paperFT_I_half
#print axioms Hodge1.paperFT_neg_I_half
#print axioms Hodge1.weil_positivity_pole_free2_of_arch
#print axioms Hodge1.weil_positivity_poleFree2_of_arch

-- Phase 1b-A: the archimedean strip certificate at l = 9/20.
#print axioms Hodge1.head_floorP
#print axioms Hodge1.RbP_floor
#print axioms Hodge1.RbP_le_archW
#print axioms Hodge1.archW_decomp
#print axioms Hodge1.archW_ge_of_sectors
#print axioms Hodge1.stripSet_le_SformC
#print axioms Hodge1.certE45
#print axioms Hodge1.certO45
#print axioms Hodge1.certE45_negative_control_lam
#print axioms Hodge1.certE45_negative_control_w2
#print axioms Hodge1.certO45_negative_control_lam
#print axioms Hodge1.evenStrip45
#print axioms Hodge1.oddStrip45
#print axioms Hodge1.arch_strip_window45
#print axioms Hodge1.hArch_window45
#print axioms Hodge1.weil_positivity_poleFree2_window45
