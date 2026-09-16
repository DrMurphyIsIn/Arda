import HardyTheorem.SelbergCompletedMollifiedLp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Complex MeasureTheory Set


-- PORT SHIMS (v4.33-rc2 -> v4.32): Mathlib gained `integral_comp_log_Ioi` and
-- `integrableOn_comp_exp_Ioi` after v4.32.  Provided here from v4.32 primitives
-- (integral_image_eq_integral_abs_deriv_smul / integrableOn_image_iff_...).
-- Proof-carrying, zero-axiom-drift.  Placed before `namespace HardyTheorem` so the
-- source's unqualified references resolve; inherited by the 2 downstream Fourier-mass
-- modules (Explicit, Global) which import this one.
theorem integral_comp_log_Ioi (f : ℝ → ℝ) {G : ℝ} (hG : 0 < G) :
    (∫ x in Set.Ioi G, f (Real.log x) • x⁻¹) = ∫ y in Set.Ioi (Real.log G), f y := by
  symm
  have hderiv : ∀ x ∈ Set.Ioi (Real.log G),
      HasDerivWithinAt Real.exp (Real.exp x) (Set.Ioi (Real.log G)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi (Real.log G)) := Real.exp_injective.injOn
  have himg : Real.exp '' (Set.Ioi (Real.log G)) = Set.Ioi G := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc G = Real.exp (Real.log G) := (Real.exp_log hG).symm
        _ < Real.exp y := Real.exp_lt_exp.mpr hy
    · intro hx
      exact ⟨Real.log x, Real.log_lt_log hG hx, Real.exp_log (hG.trans hx)⟩
  have key := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    measurableSet_Ioi hderiv hinj (fun x => f (Real.log x) • x⁻¹)
  rw [himg] at key
  rw [key]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
  rw [Real.log_exp, abs_of_pos (Real.exp_pos y), smul_eq_mul, smul_eq_mul]
  rw [eq_comm, mul_comm, mul_assoc, inv_mul_cancel₀ (Real.exp_pos y).ne', mul_one]

theorem integrableOn_comp_exp_Ioi (q : ℝ → ℝ) (a : ℝ) :
    MeasureTheory.IntegrableOn (fun y => Real.exp y * q (Real.exp y)) (Set.Ioi a) ↔
      MeasureTheory.IntegrableOn q (Set.Ioi (Real.exp a)) := by
  have hderiv : ∀ x ∈ Set.Ioi a,
      HasDerivWithinAt Real.exp (Real.exp x) (Set.Ioi a) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi a) := Real.exp_injective.injOn
  have himg : Real.exp '' (Set.Ioi a) = Set.Ioi (Real.exp a) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact Real.exp_lt_exp.mpr hy
    · intro hx
      refine ⟨Real.log x, ?_, Real.exp_log ((Real.exp_pos a).trans hx)⟩
      calc a = Real.log (Real.exp a) := (Real.log_exp a).symm
        _ < Real.log x := Real.log_lt_log (Real.exp_pos a) hx
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj q
  rw [himg] at key
  rw [key]
  refine integrableOn_congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [abs_of_pos (Real.exp_pos x), smul_eq_mul]

namespace HardyTheorem

/-! # Logarithmic change of variables for the nonconstant S1 kernel -/

theorem integral_comp_exp_Ioc (g : ℝ → ℝ) (a b : ℝ) :
    (∫ y in Ioc a b, Real.exp y * g (Real.exp y)) =
      ∫ x in Ioc (Real.exp a) (Real.exp b), g x := by
  rw [← Real.image_exp_Ioc]
  simpa [abs_of_pos (Real.exp_pos _)] using
    (integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioc (a := a) (b := b))
      (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      (fun _ _ _ _ h => Real.exp_injective h) g).symm

theorem integral_normSq_selbergNonconstantInverseFourierKernel_Ioc_log
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {G : ℝ} (hG : 0 < G) (X : ℕ) :
    (∫ y in Ioc 0 (Real.log G),
      Complex.normSq (selbergNonconstantInverseFourierKernel delta X y)) =
      ∫ x in Ioc 1 G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X) := by
  calc
    _ = ∫ y in Ioc 0 (Real.log G), Real.exp y *
        Complex.normSq
          (selbergPhysicalThetaKernel delta (Real.exp y) X) := by
      apply integral_congr_ae
      filter_upwards with y
      simpa only [Real.log_exp] using
        normSq_selbergNonconstantInverseFourierKernel_log
          hdelta hdelta1 hdeltaPi (Real.exp_pos y) X
    _ = ∫ x in Ioc (Real.exp 0) (Real.exp (Real.log G)),
        Complex.normSq (selbergPhysicalThetaKernel delta x X) :=
      integral_comp_exp_Ioc
        (fun x => Complex.normSq (selbergPhysicalThetaKernel delta x X))
        0 (Real.log G)
    _ = _ := by rw [Real.exp_zero, Real.exp_log hG]

theorem integral_normSq_selbergNonconstantInverseFourierKernel_div_sq_Ioi_log
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) {G : ℝ} (hG : 0 < G) (X : ℕ) :
    (∫ y in Ioi (Real.log G),
      Complex.normSq (selbergNonconstantInverseFourierKernel delta X y) /
        y ^ 2) =
      ∫ x in Ioi G,
        Complex.normSq (selbergPhysicalThetaKernel delta x X) /
          Real.log x ^ 2 := by
  rw [← integral_comp_log_Ioi
    (fun y => Complex.normSq
      (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2) hG]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hG.trans hx
  rw [normSq_selbergNonconstantInverseFourierKernel_log
    hdelta hdelta1 hdeltaPi hxpos X]
  rw [smul_eq_mul]
  field_simp [hxpos.ne']

theorem exists_integral_normSq_selbergNonconstantInverseFourierKernel_low_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  rcases exists_integral_normSq_selbergPhysicalThetaKernel_low_le
    ha hc hcEight hac with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  have hGnonneg : 0 ≤ (X : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hG : 0 < (X : ℝ) ^ a := by
    have hlogpos : 0 < Real.log ((X : ℝ) ^ a) := by linarith
    exact (Real.log_pos_iff hGnonneg).mp hlogpos |>.trans' zero_lt_one
  rw [integral_normSq_selbergNonconstantInverseFourierKernel_Ioc_log
    hdelta hdelta1 hdeltaPi hG X]
  exact hbound X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo

theorem exists_integral_normSq_selbergNonconstantInverseFourierKernel_high_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
              (selbergNonconstantInverseFourierKernel delta X y) /
            y ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  rcases exists_integral_normSq_selbergPhysicalThetaKernel_high_le
    ha hc hcEight hac with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi hXexp hXpow hlogGtwo
  have hGnonneg : 0 ≤ (X : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg X) a
  have hG : 0 < (X : ℝ) ^ a := by
    have hlogpos : 0 < Real.log ((X : ℝ) ^ a) := by linarith
    exact (Real.log_pos_iff hGnonneg).mp hlogpos |>.trans' zero_lt_one
  rw [integral_normSq_selbergNonconstantInverseFourierKernel_div_sq_Ioi_log
    hdelta hdelta1 hdeltaPi hG X]
  exact hbound X delta hdelta hdelta1 hX hXexp hXpow hlogGtwo

end HardyTheorem
