import Mathlib
import Statements.MMDefs
import RvMDischarge
open Quasicrystal

-- DISCHARGED: was `by sorry`.  Proof = the ported cc-chen-tech superlinear-distinct
-- theorem wired through the kernel-clean distinct-bridge (rvm_port).  MMDefs'
-- Quasicrystal.RvMUnboundedMeanDensity / zetaOrdinates are definitionally identical
-- to RvMGlue's, so the port discharge closes this node directly.
theorem rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates :=
  RvMGlue.rvm_unbounded_mean_density
