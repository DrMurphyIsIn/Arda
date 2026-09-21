/- Composition probe (2026-09-21): the interface of E6Bridge18/22 (RvMBridge18.xi) and the Taylor
   assembly of E6Bridge19 (RvMBridge19.xi) are definitionally the same, and the chain
   LocalCountSum + StripDerivBound + NoRealZeroInUnitInterval -> LiValue n closes.
   Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/E6Bridge22_taylor_probe.lean -/
import E6Bridge19
import E6Bridge22

open RvMBridge22

theorem probe_xi_defeq : RvMBridge19.xi = RvMBridge18.xi := rfl

theorem probe_partialFraction_iff :
    RvMBridge19.XiDerivPartialFraction ↔ RvMBridge18.XiLogDerivDerivEq := Iff.rfl

theorem probe_liValue_of_two (h1 : LocalCountSum) (h2 : StripDerivBound)
    (hR : RvMBridge19.NoRealZeroInUnitInterval) (n : ℕ) (hn : 0 < n) :
    RvMBridge15.LiValue n :=
  RvMBridge19.liValue_of (probe_partialFraction_iff.mpr (xiLogDerivDerivEq_of_two h1 h2)) hR n hn

#print axioms probe_xi_defeq
#print axioms probe_partialFraction_iff
#print axioms probe_liValue_of_two
