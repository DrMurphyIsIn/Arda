/-
  FEBarrier.lean -- the FE-uniformity barrier (Davenport-Heilbronn substitution).

  BARRIER RESEARCH, branch wall/barrier, 2026-09-18.  conjecture1_proved = False.

  THE CLAIM THIS FILE FORMALIZES.  Every RH-equivalence the program owns or targets --
  Li positivity (route B, `li_criterion_rh_iff`, proved on the li_positivity island from
  `biconditional_rh_li_of_hadamard_order_one`, i.e. from ENTIRE + ORDER <= 1 and nothing
  else), Weil positivity (routes A/D, `MM_zeta_comb_membership`), de Bruijn-Newman
  `Lambda <= 0` (route C) -- is a theorem about a CLASS of functions, not about zeta:
  the class of entire, self-dual, order-one completed L-functions.  Call a statement
  FE-UNIFORM when it holds for every member of that class.

  The class contains the Davenport-Heilbronn function D (a period-5 Dirichlet series with
  the Riemann-type functional equation `xi(s) = xi(1-s)` and NO Euler product), and D has
  zeros off the critical line -- a fact this repository already certifies rigorously by an
  Arb argument-principle winding count (telperion/src/telperion/arb_dh.py;
  telperion/docs/QC_DH_SCOUT.md section 4: winding number 1 on the rational box
  Re in [79/100, 83/100], Im in [8568/100, 8572/100], re-checked at doubled precision).

  Therefore NO FE-uniform argument can prove any route's wall clause: one witness refutes
  all four routes at once.  The wall clauses are not four independent targets; they are
  four FE-uniform re-encodings of the same non-FE residue, and the residue is the Euler
  product.

  SCOPE LIMIT, stated as sharply as the claim.  This is a RELATIVIZATION-grade barrier, not
  an unprovability result.  It rules out exactly one class of arguments (those uniform in
  the bundle below) and says nothing about arguments that use the Euler product, the
  non-negativity of von Mangoldt's Lambda, or the certified zero inventory.  The program's
  17 proved RH nodes are NOT in conflict with it: none of them asserts RH, Weil positivity
  or Li positivity, and the zero-free-region chain is proved from the Euler product, which
  is outside the bundle.

  TRUST BOUNDARY.  The Davenport-Heilbronn off-line zero enters as an explicit HYPOTHESIS
  of every theorem below (`hz`, `hoff`), exactly as the Arb enclosures enter the zero
  localization ladder.  No theorem here asserts it; the Lean kernel checks only the
  transfer.  Nothing here is progress on RH.
-/
import Mathlib

namespace FEBarrier

open Complex

/-- On the critical line. -/
def OnLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- **The FE-only bundle.**  Entire, self-dual under `s -> 1 - s`, real on the real axis,
and of order one in the `exp (O (|s| log |s|))` form that `XiGrowth.riemannXi_order_le_one`
establishes for the completed zeta.  These are exactly the hypotheses consumed by
`biconditional_rh_li_of_hadamard_order_one`; no arithmetic clause (no Euler product, no
multiplicativity, no `Lambda >= 0`) appears. -/
structure FEData where
  Ξ : ℂ → ℂ
  entire : Differentiable ℂ Ξ
  fe : ∀ s : ℂ, Ξ (1 - s) = Ξ s
  orderOne : ∃ C c : ℝ, ∀ s : ℂ, ‖Ξ s‖ ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))

/-- The RH analogue for a member of the bundle. -/
def RHfor (D : FEData) : Prop := ∀ s : ℂ, D.Ξ s = 0 → OnLine s

/-- The completed zeta is a member of the bundle.  Entirety and the functional equation
come straight from Mathlib; the order bound is `XiGrowth.riemannXi_order_le_one` on the
li_positivity island (not in Mathlib), so it is carried here as a NAMED hypothesis rather
than asserted.  The point of this definition is that the bundle is non-vacuous ON ZETA:
an FE-uniform argument really would apply to the object the program cares about. -/
noncomputable def zetaFEData
    (hord : ∃ C c : ℝ, ∀ s : ℂ, ‖completedRiemannZeta₀ s‖
        ≤ C * Real.exp (c * (1 + ‖s‖) * Real.log (2 + ‖s‖))) : FEData where
  Ξ := completedRiemannZeta₀
  entire := differentiable_completedZeta₀
  fe := completedRiemannZeta₀_one_sub
  orderOne := hord

/-- **The barrier.**  A single member of the bundle with an off-line zero refutes the
FE-uniform statement of RH.  The Davenport-Heilbronn function is such a member; its
off-line zero is the Arb winding certificate of `QC_DH_SCOUT` section 4. -/
theorem fe_uniform_rh_is_false (D : FEData) (ρ : ℂ) (hz : D.Ξ ρ = 0) (hoff : ¬ OnLine ρ) :
    ¬ (∀ E : FEData, RHfor E) := fun h => hoff (h D ρ hz)

/-- **One witness kills every route.**  Let `Crit` be ANY criterion equivalent to the RH
analogue throughout the bundle -- Li positivity, Weil positivity, de Bruijn-Newman
`Lambda <= 0` and Fourier-quasicrystal membership are all of this shape, because each of
their equivalence proofs uses only bundle data.  Then the same off-line witness refutes the
FE-uniform form of `Crit`.  The four routes share ONE wall, not four. -/
theorem fe_uniform_criterion_is_false (Crit : FEData → Prop)
    (hequiv : ∀ E : FEData, Crit E ↔ RHfor E)
    (D : FEData) (ρ : ℂ) (hz : D.Ξ ρ = 0) (hoff : ¬ OnLine ρ) :
    ¬ (∀ E : FEData, Crit E) :=
  fun h => fe_uniform_rh_is_false D ρ hz hoff (fun E => (hequiv E).mp (h E))

/-- Contrapositive, in the form an integrator applies to a candidate proof: if a lemma `L`
is FE-uniform and entails the RH analogue throughout the bundle, then `L` is FALSE
somewhere in the bundle.  Substituting Davenport-Heilbronn for zeta is therefore a sound
refutation test for any candidate wall proof whose hypotheses are bundle data. -/
theorem no_fe_uniform_sufficient_condition (L : FEData → Prop)
    (hsuff : ∀ E : FEData, L E → RHfor E)
    (D : FEData) (ρ : ℂ) (hz : D.Ξ ρ = 0) (hoff : ¬ OnLine ρ) :
    ¬ (∀ E : FEData, L E) :=
  fun h => hoff (hsuff D (h D) ρ hz)

/-! ### HONESTY CHECK: the bundle above is TOO POOR, and the kernel says so

A barrier is only as strong as the bundle it quantifies over.  The four clauses of `FEData`
are refuted by a POLYNOMIAL -- `s * (s - 1)` is entire, self-dual under `s -> 1 - s`, of
order zero, and vanishes at `0` and `1`, both off the critical line.  So
`fe_uniform_rh_is_false` holds unconditionally over THIS bundle, and Davenport-Heilbronn is
not needed for it.

That is not a defect of the barrier; it is the measurement of its current reach, and it is
stated in the kernel rather than in prose.  The consequence for the integrator is precise:

  * over the bundle AS WRITTEN, the barrier rules out only arguments that use nothing beyond
    entirety, self-duality and order one -- a class no route actually lives in;
  * the DH witness earns its keep only over an ENRICHED bundle, one carrying a normalized
    Dirichlet series (`a 1 = 1`, bounded coefficients, degree one) that excludes polynomials
    and every other cheap witness while still admitting Davenport-Heilbronn;
  * enriching `FEData` to that form, and re-proving `zetaFEData` against it, is therefore the
    first task, not an optional refinement.  Until it is done, the honest statement of the
    barrier is the classical one about the RICH bundle, with this file supplying the
    transfer schema and the Arb certificate supplying the witness.

`poly_refutes_poor_bundle` is deliberately UNCONDITIONAL: it takes no hypothesis, so it
cannot be mistaken for the Davenport-Heilbronn result. -/

noncomputable def polyFEData : FEData where
  Ξ := fun s => s * (s - 1)
  entire := by fun_prop
  fe := by intro s; ring
  orderOne := by
    refine ⟨1, 2, fun s => ?_⟩
    set r := ‖s‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg s
    have hb : ‖s * (s - 1)‖ ≤ (1 + r) ^ 2 := by
      have h1 : ‖s - 1‖ ≤ r + 1 := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = r + 1 := by simp [hr]
      calc ‖s * (s - 1)‖ = r * ‖s - 1‖ := by rw [norm_mul]
        _ ≤ (1 + r) * (r + 1) := by
            apply mul_le_mul (by linarith) h1 (norm_nonneg _) (by linarith)
        _ = (1 + r) ^ 2 := by ring
    have hexp : (2 + r) ^ 2 ≤ Real.exp (2 * (1 + r) * Real.log (2 + r)) := by
      have h2 : Real.exp (2 * Real.log (2 + r)) = (2 + r) ^ 2 := by
        rw [two_mul, Real.exp_add, Real.exp_log (by linarith)]; ring
      rw [← h2]
      refine Real.exp_le_exp.mpr ?_
      have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
      nlinarith
    have hmono : (1 + r) ^ 2 ≤ (2 + r) ^ 2 := by nlinarith
    calc ‖s * (s - 1)‖ ≤ (1 + r) ^ 2 := hb
      _ ≤ (2 + r) ^ 2 := hmono
      _ ≤ Real.exp (2 * (1 + r) * Real.log (2 + r)) := hexp
      _ = 1 * Real.exp (2 * (1 + r) * Real.log (2 + r)) := by ring

/-- The bundle as written is refuted by a polynomial, unconditionally.  Measures the
barrier's current reach; see the section docstring. -/
theorem poly_refutes_poor_bundle : ¬ (∀ E : FEData, RHfor E) :=
  fe_uniform_rh_is_false polyFEData 0 (by simp [polyFEData]) (by simp [OnLine])

/-! ### The Li kernel is purely positional (arithmetic-free)

Li's criterion runs through the Moebius map `rho -> 1 - 1/rho`, which carries the open
half-plane `Re > 1/2` onto the open unit disc.  The two lemmas below are that map's entire
geometric content, and they mention no arithmetic at all -- a concrete instance of route
B's FE-uniformity: the Li ladder transmits the POSITIONS of the zeros and adds nothing to
them.  Whatever decides RH has to enter the ladder as input, not as machinery. -/

theorem norm_sub_one_lt_iff (ρ : ℂ) : ‖ρ - 1‖ < ‖ρ‖ ↔ 1 / 2 < ρ.re := by
  have h : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 - 2 * ρ.re + 1 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hA : 0 ≤ ‖ρ - 1‖ := norm_nonneg _
  have hB : 0 ≤ ‖ρ‖ := norm_nonneg _
  constructor
  · intro hlt
    have h2 : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := by nlinarith
    rw [h] at h2; linarith
  · intro hre
    have h2 : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := by rw [h]; linarith
    nlinarith

theorem mobius_disc_iff {ρ : ℂ} (hρ : ρ ≠ 0) : ‖1 - 1 / ρ‖ < 1 ↔ 1 / 2 < ρ.re := by
  have hpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hrw : ‖1 - 1 / ρ‖ = ‖ρ - 1‖ / ‖ρ‖ := by
    rw [show (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ by field_simp, norm_div]
  rw [hrw, div_lt_one hpos, norm_sub_one_lt_iff]

#print axioms FEBarrier.fe_uniform_rh_is_false
#print axioms FEBarrier.fe_uniform_criterion_is_false
#print axioms FEBarrier.no_fe_uniform_sufficient_condition
#print axioms FEBarrier.mobius_disc_iff
#print axioms FEBarrier.zetaFEData
#print axioms FEBarrier.poly_refutes_poor_bundle

end FEBarrier
