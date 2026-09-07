/- AxiomGuardDlvp — CI kernel-axiom guard for the dVP concrete-zero zero-free region.

   Separate from `AxiomGuardRH.lean` because `DlvpZetaConcreteClose` transitively imports
   `DlvpZetaDisk`, which declares `ZeroFreeBridge.zeta_sphere_bound` — a name also declared in
   `ZeroFreeElementary` (imported by `AxiomGuardRH`).  Importing both in one module is an
   environment clash, so the dVP guard lives in its own top-level file.

   Like `AxiomGuardRH`, this is NOT a `lean_lib`; CI runs it explicitly with

       lake env lean AxiomGuardDlvp.lean

   AFTER `lake build`, and FAILS if any `#print axioms` output mentions `sorryAx`.

   Guarded anchors:
     * dlvp_zeta_region_concrete — the UNCONDITIONAL de la Vallée Poussin region for a concrete
       ζ-zero `ρ₀ = β+iγ` (`1/2 < β < 1`, `|γ| ≥ 7/2`, multiplicity `k`): `∃ A L, β ≤ 1 - 1/(112·A·L)`.
       Both the numeric coupling and the pole bound are discharged internally (only the zero's
       coordinates + multiplicity are inputs).  Kernel-verified REDUCTION; `∃`-form.
     * dlvp_zeta_region_rate — the RATE-EXPOSED region: `∃ c > 0, ∀ ζ-zero ρ₀=β+iγ with 3/4 ≤ β < 1,
       |γ| ≥ 55/16, mult k in the fixed disk radius 11/8, β ≤ 1 - c/log|γ|`.  The classical dVP rate
       `/log|γ|` is now in the TYPE; `c` is non-effective (it derives from Mathlib's pole constant).
   Both are kernel-verified reductions.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaConcreteClose
import DlvpZetaConcreteRate

#print axioms ZeroFreeBridge.dlvp_zeta_region_concrete
#print axioms ZeroFreeBridge.dlvp_zeta_region_rate
