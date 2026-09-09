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
       `/log|γ|` is in the TYPE; `c` is non-effective (it derives from Mathlib's pole constant).
     * hpole_effective — the EXPLICIT pole bound `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + 16` for `1 < σ`,
       `σ-1 < 1/48` (Cauchy estimate on `ζ₁ = (·-1)·ζ`), replacing Mathlib's bare-`∃` pole constant.
     * dlvp_zeta_region_rate_effective / dlvpRateC_pos — the RATE with an EXPLICIT constant:
       `β ≤ 1 - dlvpRateC/log|γ|`, `dlvpRateC > 0` a concrete closed-form real.  `c` is now EFFECTIVE.
     * riemannZeta_ne_zero_region — the SELF-CONTAINED zero-free region (no multiplicity hypothesis):
       `55/16 ≤ |γ| ∧ 1 - dlvpRateC/log|γ| < β ⟹ ζ(β+iγ) ≠ 0`, i.e. `ζ(s) ≠ 0` on
       `Re s > 1 - dlvpRateC/log|Im s|`.  Multiplicity `1 ≤ divisor` is derived from `ζ ρ₀ = 0`
       (zeta_zero_divisor_pos).
     * zeta_zero_on_line_of_right_half_clear / zeta_zero_on_line_of_quarter_clear — the
       functional-equation symmetry reductions (RH-in-a-box piece 3): clearing the right half
       (resp. the quarter `1/2<Re<1, 0<Im≤T`) of the critical strip suffices, via reflection across
       `Re = 1/2` (riemannZeta_one_sub) and the real axis (riemannZeta_conj).
   All are kernel-verified reductions.  conjecture1_proved = False (NOT a proof of RH).
-/
import DlvpZetaConcreteClose
import DlvpZetaConcreteRate
import DlvpZetaPoleEffective
import DlvpZetaRateEffective
import DlvpZetaZeroFree
import DlvpZetaSymmetry
import DlvpTheta

#print axioms ZeroFreeBridge.dlvp_zeta_region_concrete
#print axioms ZeroFreeBridge.dlvp_zeta_region_rate
#print axioms ZeroFreeBridge.hpole_effective
#print axioms ZeroFreeBridge.dlvp_zeta_region_rate_effective
#print axioms ZeroFreeBridge.dlvpRateC_pos
#print axioms ZeroFreeBridge.riemannZeta_ne_zero_region
#print axioms ZeroFreeBridge.zeta_zero_divisor_pos
#print axioms ZeroFreeBridge.zeta_zero_on_line_of_right_half_clear
#print axioms ZeroFreeBridge.zeta_zero_on_line_of_quarter_clear
#print axioms ZeroFreeBridge.riemannZeta_reflect_line_eq_zero
#print axioms ZeroFreeBridge.riemannZeta_ne_zero_near_one
#print axioms ZeroFreeBridge.dlvpRateC_lower
#print axioms ZeroFreeBridge.riemannSiegelTheta_zero
#print axioms ZeroFreeBridge.riemannSiegelTheta_deriv
#print axioms ZeroFreeBridge.thetaIntegrand_continuous
#print axioms ZeroFreeBridge.logDeriv_gammaR
#print axioms ZeroFreeBridge.thetaIntegrand_eq_re_logDeriv_gammaR
#print axioms ZeroFreeBridge.digamma_shift
#print axioms ZeroFreeBridge.norm_inv_sub_log_one_add_inv_le
#print axioms ZeroFreeBridge.thetaMain_hasDerivAt
#print axioms ZeroFreeBridge.log_succ_sub_log
#print axioms ZeroFreeBridge.digamma_sub_log_telescoped
#print axioms ZeroFreeBridge.sum_norm_inv_sub_log_le
#print axioms ZeroFreeBridge.norm_digamma_sub_log_le_of_anchor
#print axioms ZeroFreeBridge.tendsto_digamma_sub_log_one_add_nat
#print axioms ZeroFreeBridge.digamma_ofReal_eq
#print axioms ZeroFreeBridge.monotoneOn_deriv_log_Gamma
#print axioms ZeroFreeBridge.tendsto_binetR_add
#print axioms ZeroFreeBridge.tendsto_digamma_sub_log_ofReal
#print axioms ZeroFreeBridge.norm_digamma_sub_log_le_ofReal
