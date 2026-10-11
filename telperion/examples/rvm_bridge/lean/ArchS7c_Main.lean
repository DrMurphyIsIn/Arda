import ArchS7c_HS
import ArchS6_Trace

/-!
# ArchS7c_Main: CC Theorem 4.7 with no hypotheses beyond `IsWeilTest g`

* `norm_hatP_eq`: `‖P̂ z‖ = ‖P F z‖` for any `ProjPair` (`F` unitary, `F P̂ = P F`).
* **`hasSum_h85`** (CC (85) = Prop 2.2(iii), HS form): for every `IsWeilTest g` and every Hilbert basis
  `e` of `L²(ℝ)_ev`, `Σ_k ‖P̂ P ϑ(g) e_k‖² = archW g + Dfun g`.  This is S7's hypothesis O1.
* **`thm47_of_data`**: CC Thm 4.7, `Σ_k ‖S ϑ(g) e_k‖² = archW g + Re E(g∗g*)`, for every real prolate
  eigenbasis `bR`, enumeration `σ` and S8 `ProlateData D` with `D.lam = μ ∘ σ`, `D.phi = phiR ∘ σ`.
* **`thm47_unconditional`**: the same with the data supplied by S6 (`exists_prolateData`): an `∃` over
  `(ι, bR, σ, D)`, then `∀` Hilbert bases.  **`thm47_unconditional_nonneg`**: CC (83).

conjecture1_proved = False.  This is CC's archimedean positivity statement Thm 4.7/(83); it is not RH and
not Weil positivity.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace ArchS7c

open ArchS6 ArchS7 ArchS3

set_option linter.unusedSectionVars false

universe u

theorem norm_F_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : ProjPair H) (a : H) :
    ‖S.F a‖ = ‖a‖ := by
  have h := S.inner_F a (S.F a)
  rw [S.F_F] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ a, h]

/-- `‖P̂ z‖ = ‖F P̂ z‖ = ‖P F z‖`. -/
theorem norm_hatP_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : ProjPair H)
    (z : H) : ‖S.hatP z‖ = ‖S.P (S.F z)‖ := by
  rw [← norm_F_eq S (S.hatP z)]
  congr 1
  simp only [ProjPair.hatP_apply, ProjPair.hatP₁_apply, ProjPair.P_apply, map_sub, S.F_F]

section

variable {g : ℝ → ℂ}

/-- **CC (85) in Hilbert-Schmidt form** (S7's interface O1, now a theorem):
`‖P̂ P ϑ(g)‖²_HS = W∞(g∗g*) + D(g∗g*)` for every Hilbert basis of `L²(ℝ)_ev`. -/
theorem hasSum_h85 (hW : WeilExplicit.IsWeilTest g) {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖evenPair.hatP (evenPair.P
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k)))‖ ^ 2)
      (archW g + Dfun g) := by
  have hg : Integrable g volume := hW.1.continuous.integrable_of_hasCompactSupport hW.2
  set f : κ → ℝ := fun k => ‖evenPair.hatP (evenPair.P (theta g hg (e k)))‖ ^ 2 with hfdef
  have hfQ : ∀ k, f k = ‖Qop g hg (e k)‖ ^ 2 := fun k => by
    show ‖evenPair.hatP (evenPair.P (theta g hg (e k)))‖ ^ 2 = _
    rw [norm_hatP_eq, Qop_apply]
  have hc : 0 ≤ archW g + Dfun g := cc_cor_2_3 hW
  have hE : ∑' k, ENNReal.ofReal (f k) = ENNReal.ofReal (archW g + Dfun g) := by
    simp_rw [hfQ]; exact hs_Q_eq hW hg e
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hsum : Summable f := by
    have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (f k)) (by rw [hE]; simp)
    simpa [ENNReal.toReal_ofReal (hf0 _)] using this
  have htsum : ∑' k, f k = archW g + Dfun g := by
    have h := ENNReal.ofReal_tsum_of_nonneg hf0 hsum
    rw [hE] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf0) hc).mp h
  rw [← htsum]
  exact hsum.hasSum

/-- **CC Theorem 4.7 for any prolate data**: no analytic hypotheses remain. -/
theorem thm47_of_data {ι : Type*} (bR : EigenBasis CopR ι) (D : ArchS8.ProlateDataNat) (σ : ℕ ≃ ι)
    (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hW : WeilExplicit.IsWeilTest g) {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
      (archW g + (D.Eplus (WeilExplicit.autocorr g)).re) :=
  thm47_weil' bR D σ hDlam hDphi (summable_abs_tau bR) hW e (hasSum_h85 hW e)

/-- **CC (83) for any prolate data**: `archW g + Re E(g∗g*) ≥ 0`. -/
theorem thm47_of_data_nonneg {ι : Type*} (bR : EigenBasis CopR ι) (D : ArchS8.ProlateDataNat)
    (σ : ℕ ≃ ι) (hDlam : ∀ n, D.lam n = bR.μ (σ n)) (hDphi : ∀ n, D.phi n = phiR bR (σ n))
    (hW : WeilExplicit.IsWeilTest g) :
    0 ≤ archW g + (D.Eplus (WeilExplicit.autocorr g)).re := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ evenL2
  exact (thm47_of_data bR D σ hDlam hDphi hW b).nonneg fun _ ↦ sq_nonneg _

/-- **CC Theorem 4.7, hypothesis-free.**  For every test function `g` (smooth, compact support) there are
S6's real prolate eigenbasis `bR`, an enumeration `σ : ℕ ≃ ι` and S8 `ProlateData D` (`D.lam = μ ∘ σ`,
`D.phi = phiR ∘ σ`) such that for every Hilbert basis `e` of `L²(ℝ)_ev`,
`Tr(ϑ(g∗g*) S) = ‖S ϑ(g)‖²_HS = W∞(g∗g*) + Re E(g∗g*)`.  The data do not depend on `g`. -/
theorem thm47_unconditional :
    ∃ (ι : Type) (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι) (D : ArchS8.ProlateDataNat),
      (∀ n, D.lam n = bR.μ (σ n)) ∧ (∀ n, D.phi n = phiR bR (σ n)) ∧
      ∀ (g : ℝ → ℂ) (hW : WeilExplicit.IsWeilTest g) (κ : Type u) (e : HilbertBasis κ ℂ evenL2),
        HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
            (theta g (hW.1.continuous.integrable_of_hasCompactSupport hW.2) (e k))‖ ^ 2)
          (archW g + (D.Eplus (WeilExplicit.autocorr g)).re) := by
  obtain ⟨ι, bR, σ, D, hDlam, hDphi⟩ := exists_prolateData
  exact ⟨ι, bR, σ, D, hDlam, hDphi, fun g hW κ e => thm47_of_data bR D σ hDlam hDphi hW e⟩

/-- **CC (83), hypothesis-free**: `W∞(g∗g*) + Re E(g∗g*) ≥ 0` for every test function `g`, with S6's data. -/
theorem thm47_unconditional_nonneg :
    ∃ (ι : Type) (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι) (D : ArchS8.ProlateDataNat),
      (∀ n, D.lam n = bR.μ (σ n)) ∧ (∀ n, D.phi n = phiR bR (σ n)) ∧
      ∀ (g : ℝ → ℂ), WeilExplicit.IsWeilTest g →
        0 ≤ archW g + (D.Eplus (WeilExplicit.autocorr g)).re := by
  obtain ⟨ι, bR, σ, D, hDlam, hDphi⟩ := exists_prolateData
  exact ⟨ι, bR, σ, D, hDlam, hDphi, fun g hW => thm47_of_data_nonneg bR D σ hDlam hDphi hW⟩

end

end ArchS7c
