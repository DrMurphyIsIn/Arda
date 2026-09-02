/- AxiomGuardPolylog — CI kernel-axiom guard for the polylog-improved zero-free region.

   Decoupled from AxiomGuardRH (which the elementary job runs) so building ZeroFreePolylog is not
   forced onto that job. CI runs this explicitly with `lake env lean AxiomGuardPolylog.lean` after
   `lake build ZeroFreePolylog`, and FAILS if `#print axioms` mentions `sorryAx`. A clean proof
   reports exactly `[propext, Classical.choice, Quot.sound]`. -/
import ZeroFreePolylog

#print axioms ZeroFreeBridge.riemannZeta_zero_free_polylog
