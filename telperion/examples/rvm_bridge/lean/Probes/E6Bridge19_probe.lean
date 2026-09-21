/-
  Probes for E6Bridge19 (2026-09-21): axiom audit of the LiValue bookkeeping and assembly.
  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge19_probe.lean
  Expected: every #print axioms line is exactly [propext, Classical.choice, Quot.sound]; no errors.
-/
import E6Bridge19

open Zeta23 Complex Filter Topology RvMBridge15 RvMBridge15.BombieriLagarias RvMBridge19

#print axioms RvMBridge19.powerSum_eq_taylor
#print axioms RvMBridge19.summable_powerSum
#print axioms RvMBridge19.powerSum_conj
#print axioms RvMBridge19.pairedPowerSum_one_eq
#print axioms RvMBridge19.summable_pairedPowerSum
#print axioms RvMBridge19.tsum_refTerm
#print axioms RvMBridge19.eta_eq
#print axioms RvMBridge19.iteratedDeriv_psiHalf
#print axioms RvMBridge19.tsum_odd_inv_pow
#print axioms RvMBridge19.archCoeff_zero
#print axioms RvMBridge19.archCoeff_succ
#print axioms RvMBridge19.logDeriv_xi_eventuallyEq_one
#print axioms RvMBridge19.taylorOne_eq
#print axioms RvMBridge19.taylorZero_eq
#print axioms RvMBridge19.liLimit_eq_taylorOne
#print axioms RvMBridge19.liValue_of
#print axioms RvMBridge19.bl_explicit_formula_of_partialFraction
#print axioms RvMBridge19.xi_eq_zero_iff
