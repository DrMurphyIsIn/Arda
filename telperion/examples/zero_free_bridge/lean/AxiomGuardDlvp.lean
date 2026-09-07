/- AxiomGuardDlvp — CI kernel-axiom guard for the dVP concrete-zero zero-free region.

   Separate from `AxiomGuardRH.lean` because `DlvpZetaConcreteClose` transitively imports
   `DlvpZetaDisk`, which declares `ZeroFreeBridge.zeta_sphere_bound` — a name also declared in
   `ZeroFreeElementary` (imported by `AxiomGuardRH`).  Importing both in one module is an
   environment clash, so the dVP guard lives in its own top-level file.

   Like `AxiomGuardRH`, this is NOT a `lean_lib`; CI runs it explicitly with

       lake env lean AxiomGuardDlvp.lean

   AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

   Guarded anchor:
     * dlvp_zeta_region_concrete — the UNCONDITIONAL de la Vallée Poussin region for a concrete
       ζ-zero `ρ₀ = β+iγ` (`1/2 < β < 1`, `|γ| ≥ 7/2`, multiplicity `k`): `∃ A L, β ≤ 1 - 1/(112·A·L)`.
       Both the numeric coupling and the pole bound are discharged internally (only the zero's
       coordinates + multiplicity are inputs).  This is a kernel-verified REDUCTION; the classical
       rate `1 - c/log|γ|` lives in the construction (`A` a fixed pole constant, `L = O(log|γ|)`),
       and the constant is non-effective.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaConcreteClose

#print axioms ZeroFreeBridge.dlvp_zeta_region_concrete
