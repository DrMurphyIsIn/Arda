/- Task 7 (Stage 2B): KERNEL-DERIVE the local Blaschke split of `zeta'/zeta` over the box
   `B = [2/5, 3/5] x [10, 35]`.

   Controller adjustment (2026-09-06): the winding was switched to ZETA, so the capstone uses
   `zeta'/zeta` (`Ld = riemannZeta` in Task 5).  We derive, for `Ld = logDeriv riemannZeta`,
     `logDeriv zeta z = (Sum_{rho in zeros(zeta) cap ball} (divisor zeta rho)/(z - rho)) + E z`,
   with `E := logDeriv g` HOLOMORPHIC on cl(B), and discharge Task 5's H1 (split) + H2 (E-holo).

   Region: `zeta` is analytic on `{1}ᶜ` (`analyticOn_riemannZeta`).  We localize on an OPEN BALL
   `U = ball c r` with `cl(B) ⊆ U` and `1 ∉ U` (so `U ⊆ {1}ᶜ`).  On the compact `closedBall`,
   `MeromorphicOn.divisor zeta U` has finite support (Mathlib `IsCompact.inter_riemannZetaZeros_finite`
   via `divisor_support_finite_of_subset`), and `MeromorphicOn.extract_zeros_poles` gives an analytic,
   zero-free `g` on `U` with `zeta =ᶠ[codiscreteWithin U] (prod_u (·-u)^(divisor zeta U u)) • g`.

   The log-derivative transfer across the codiscrete equality (identity-principle germ argument,
   `logDeriv_congr_of_codiscrete`, reproduced in-file, function-agnostic) turns that into a POINTWISE
   `logDeriv` identity on `U`.  On the box boundary (subset of `U`, avoiding all zeros), this is the
   required split, and `E := logDeriv g` is holomorphic on `U ⊇ cl(B)` because `g` is analytic and
   zero-free there.

   conjecture1_proved = False.  This is a kernel derivation of a split hypothesis; NOT a proof of RH. -/
import Mathlib
import BoxArgPrinciple

open Complex Filter
open scoped Topology

namespace BlaschkeBox

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.

These reproduce the in-repo `zero_free_bridge/DlvpTransfer` lemmas (that library is a separate Lean
project, not importable here).  All are pure Mathlib, function-agnostic. -/

/-- Log-derivatives agree wherever the functions agree on a NEIGHBORHOOD (`logDeriv` is a germ
    invariant: value + derivative at the point). -/
theorem logDeriv_congr_nhds {f₁ f₂ : ℂ → ℂ} {z : ℂ} (h : f₁ =ᶠ[nhds z] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Log-derivatives agree at any point of an OPEN set on which the functions agree. -/
theorem logDeriv_congr_eqOn_open {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (h : Set.EqOn f₁ f₂ U) :
    logDeriv f₁ z = logDeriv f₂ z :=
  logDeriv_congr_nhds (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)

/-- **Codiscrete transfer.**  Two analytic functions on a preconnected open `U` agreeing
    CODISCRETELY (`=ᶠ[codiscreteWithin U]`) have equal log-derivatives at EVERY `z ∈ U`.  This is
    exactly the shape `MeromorphicOn.extract_zeros_poles` produces. -/
theorem logDeriv_congr_of_codiscrete {f₁ f₂ : ℂ → ℂ} {U : Set ℂ} {z₀ z : ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hf₂ : AnalyticOnNhd ℂ f₂ U)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (h : f₁ =ᶠ[Filter.codiscreteWithin U] f₂) :
    logDeriv f₁ z = logDeriv f₂ z := by
  have hmem : {x | f₁ x = f₂ x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h) z₀ hz₀
  have hU_nhds : U ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz₀)
  have hev : ∀ᶠ x in 𝓝[≠] z₀, f₁ x = f₂ x := by
    filter_upwards [hmem, hU_nhds] with x hx hxU
    rcases hx with h1 | h2
    · exact h1
    · exact absurd hxU h2
  exact logDeriv_congr_eqOn_open hU hz
    (hf₁.eqOn_of_preconnected_of_frequently_eq hf₂ hUc hz₀ hev.frequently)

/-! ## Part B: log-derivative of the factorized-rational product.

For a finite index set `T` of roots with integer multiplicities `D`, the log-derivative of the
Finset product `fun w => ∏ u ∈ T, (w - u) ^ (D u)` is `∑ u ∈ T, (D u)/(w - u)` at any `w` avoiding
the roots.  (This is the `toy_blaschke_split` content from the Stage-2B probe.) -/

/-- `logDeriv (fun w => (w - u) ^ d) z = d / (z - u)` off the root `u`. -/
theorem logDeriv_factor {u z : ℂ} (d : ℤ) (_hzu : z - u ≠ 0) :
    logDeriv (fun w : ℂ => (w - u) ^ d) z = (d : ℂ) / (z - u) := by
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
  rw [logDeriv_fun_zpow hdiff d]
  have : logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
    rw [logDeriv_apply]
    have hderiv : deriv (fun w : ℂ => w - u) z = 1 := by
      simp [deriv_sub_const (f := fun w : ℂ => w) u (x := z)]
    rw [hderiv]
  rw [this]; ring

/-- **Finset factorized-rational split.**  `logDeriv (∏ u∈T, (·-u)^(D u)) z = ∑ u∈T, (D u)/(z-u)`
    at any `z` avoiding every root in `T`. -/
theorem logDeriv_finset_prod {T : Finset ℂ} (D : ℂ → ℤ) (z : ℂ)
    (hz : ∀ u ∈ T, z - u ≠ 0) :
    logDeriv (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) z
      = ∑ u ∈ T, (D u : ℂ) / (z - u) := by
  have hne : ∀ u ∈ T, ((fun w : ℂ => (w - u) ^ (D u)) z) ≠ 0 :=
    fun u hu => zpow_ne_zero _ (hz u hu)
  have hdiff : ∀ u ∈ T, DifferentiableAt ℂ (fun w : ℂ => (w - u) ^ (D u)) z := by
    intro u hu
    have hbase : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
    exact (differentiableAt_zpow.2 (Or.inl (hz u hu))).comp z hbase
  set F : ℂ → ℂ → ℂ := fun u w => (w - u) ^ (D u) with hF
  have hfun : (fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u)) = fun w : ℂ => ∏ u ∈ T, F u w := rfl
  rw [hfun, logDeriv_prod (s := T) (f := F) (x := z) hne hdiff]
  exact Finset.sum_congr rfl (fun u hu => logDeriv_factor (D u) (hz u hu))

/-! ## Part C: region setup.

`U = ball cB 13` is an open ball centered at the box center `cB = 1/2 + (45/2) i` with radius `13`.
It contains `cl(B) = [2/5,3/5] x [10,35]` and excludes `zeta`'s only pole `s = 1` (in fact even the
CLOSED ball excludes `1`, since `dist(1, cB)^2 = 506.5 > 169 = 13^2`). -/

/-- Box center. -/
noncomputable def cB : ℂ := ⟨1 / 2, 45 / 2⟩

/-- The closed box `B = [2/5, 3/5] x [10, 35]`. -/
def boxB : Set ℂ := Set.Icc ((2 / 5) : ℝ) (3 / 5) ×ℂ Set.Icc ((10) : ℝ) 35

/-- The closed ball `closedBall cB 13` avoids `zeta`'s pole `s = 1`. -/
theorem closedBall_subset_compl_one : Metric.closedBall cB 13 ⊆ ({1}ᶜ : Set ℂ) := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq_re_im] at hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h; rw [h] at hz
  simp only [cB, Complex.one_re, Complex.one_im] at hz
  rw [show ((1 : ℝ) - 1 / 2) ^ 2 + ((0 : ℝ) - 45 / 2) ^ 2 = 506.5 by norm_num] at hz
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 506.5 by norm_num),
    Real.sqrt_nonneg (506.5 : ℝ), hz]

/-- The open ball `ball cB 13` avoids `zeta`'s pole `s = 1`. -/
theorem ball_subset_compl_one : Metric.ball cB 13 ⊆ ({1}ᶜ : Set ℂ) :=
  (Metric.ball_subset_closedBall).trans closedBall_subset_compl_one

/-- The closed box `B` is contained in the open ball `ball cB 13`. -/
theorem boxB_subset_ball : boxB ⊆ Metric.ball cB 13 := by
  intro z hz
  rw [boxB, Complex.mem_reProdIm] at hz
  obtain ⟨⟨hre0, hre1⟩, him0, him1⟩ := hz
  rw [Metric.mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' (by norm_num)]
  simp only [cB]
  nlinarith [hre0, hre1, him0, him1, sq_nonneg (z.re - 1 / 2), sq_nonneg (z.im - 45 / 2)]

/-- On `{1}ᶜ`, every meromorphic order of `zeta` is finite (`zeta` is analytic and not identically
    zero on the connected set `{1}ᶜ`; witness `zeta 2 ≠ 0`). -/
theorem meromorphicOrderAt_zeta_ne_top :
    ∀ u ∈ ({1}ᶜ : Set ℂ), meromorphicOrderAt riemannZeta u ≠ ⊤ := by
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hMero : MeromorphicOn riemannZeta ({1}ᶜ : Set ℂ) := analyticOn_riemannZeta.meromorphicOn
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hz2 : AnalyticAt ℂ riemannZeta 2 := analyticOn_riemannZeta 2 h2mem
  have hne2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hord2 : meromorphicOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [hz2.meromorphicOrderAt_eq, hz2.analyticOrderAt_eq_zero.mpr hne2]; simp
  intro u hu
  exact hMero.meromorphicOrderAt_ne_top_of_isPreconnected hconn.isPreconnected h2mem hu hord2

/-! ## Part D: the derived local Blaschke split.

`zeta_blaschke_split_box` gives, on the ball `U = ball cB 13 ⊇ cl(B)`, the local principal-part
split of `logDeriv zeta` into a residue sum over its zeros in `U` plus a HOLOMORPHIC error `E`, and
the holomorphy of `E` on the closed box `B`.  The split is stated at every `z ∈ U` where `zeta z ≠ 0`
(off the zeros; on the box BOUNDARY there are no zeros -- see the corollary in `BoxArgPrinciple`). -/

/-- **Local Blaschke split of `zeta'/zeta` over the box (Stage 2B, kernel-derived).**

    There is a finite set `s` (the support of `zeta`'s divisor on `U = ball cB 13`), an integer
    multiplicity function `d` (that divisor), and an error `E`, such that:
    * `E` is holomorphic on the closed box `B` (H2);
    * every `ρ ∈ s` is a zero of `zeta`, i.e. `riemannZeta ρ = 0` (the statement proves this
      unconditionally; the strict-interior antecedents in the `∀ ρ ∈ s, ...` conjunct are supplied
      but discarded by the proof, so the conjunct holds as stated for every `ρ ∈ s`);
    * at every `z ∈ U` with `zeta z ≠ 0`,
        `logDeriv zeta z = (∑ ρ ∈ s, (d ρ)/(z - ρ)) + E z`   (H1, off the zeros).

    `E := logDeriv g` where `g` is the analytic, zero-free remainder from
    `MeromorphicOn.extract_zeros_poles`; its holomorphy on `B ⊆ U` is exactly `logDeriv` of an
    analytic non-vanishing function.  conjecture1_proved = False. -/
theorem zeta_blaschke_split_box :
    ∃ (E : ℂ → ℂ) (s : Finset ℂ) (d : ℂ → ℤ),
      DifferentiableOn ℂ E boxB ∧
      (∀ ρ ∈ s, ((2 / 5) : ℝ) < ρ.re → ρ.re < (3 / 5) → (10 : ℝ) < ρ.im → ρ.im < 35 →
        riemannZeta ρ = 0) ∧
      (∀ ρ ∈ s, (1 : ℤ) ≤ d ρ) ∧
      (∀ ρ ∈ Metric.ball cB 13, riemannZeta ρ = 0 → ρ ∈ s) ∧
      (∀ z ∈ Metric.ball cB 13, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ s, (d ρ : ℂ) / (z - ρ)) + E z) := by
  set U := Metric.ball cB 13 with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := (convex_ball cB 13).isPreconnected
  have hUsub : U ⊆ ({1}ᶜ : Set ℂ) := ball_subset_compl_one
  have hcbsub : Metric.closedBall cB 13 ⊆ ({1}ᶜ : Set ℂ) := closedBall_subset_compl_one
  have hζU : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hUsub
  have hMeroU : MeromorphicOn riemannZeta U := hζU.meromorphicOn
  have hMeroCB : MeromorphicOn riemannZeta (Metric.closedBall cB 13) :=
    (analyticOn_riemannZeta.mono hcbsub).meromorphicOn
  have h₂f : ∀ u : U, meromorphicOrderAt riemannZeta u ≠ ⊤ :=
    fun u => meromorphicOrderAt_zeta_ne_top u.1 (hUsub u.2)
  have h₃f : (MeromorphicOn.divisor riemannZeta U).support.Finite :=
    hMeroCB.divisor_ball_support_finite
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hMeroU.extract_zeros_poles h₂f h₃f
  set D : ℂ → ℤ := fun u => (MeromorphicOn.divisor riemannZeta U : ℂ → ℤ) u with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζU x
  have hDfin : (Function.support D).Finite := h₃f
  set T : Finset ℂ := hDfin.toFinset with hTdef
  -- Pf (the factorized-rational product) reduced to a Finset product.
  have hPf_finset : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u))
      = fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) := by
    rw [Function.FactorizedRational.finprod_eq_fun (d := D) hDfin]
    ext w
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
    · intro u hu
      rw [hTdef, Set.Finite.coe_toFinset]
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [Function.mem_mulSupport] at hu
      exact hu (by rw [hc, zpow_zero])
  set Pf : ℂ → ℂ := fun w : ℂ => ∏ u ∈ T, (w - u) ^ (D u) with hPfdef
  have hPf_an : AnalyticOnNhd ℂ Pf U := by
    rw [← hPf_finset]; intro x _; exact Function.FactorizedRational.analyticAt (hDnn x)
  set P : ℂ → ℂ := fun z => Pf z * g z with hPdef
  have hP_an : AnalyticOnNhd ℂ P U := fun x hx => (hPf_an x hx).mul (hg_an x hx)
  -- codiscrete equality `zeta =ᶠ P`.
  have hg_eqP : riemannZeta =ᶠ[Filter.codiscreteWithin U] P := by
    have hPeq : ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor riemannZeta U u)) • g) = P := by
      rw [hPf_finset]; ext w; simp [hPdef, hPfdef]
    rw [← hPeq]; exact hg_eq
  -- the `u ∈ T` are exactly (a superset of) zeros of `zeta`.
  have hT_zero : ∀ u ∈ T, riemannZeta u = 0 := by
    intro u hu
    rw [hTdef, Set.Finite.mem_toFinset, Function.mem_support] at hu
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
      (by rw [Function.mem_support]; exact hu)
    by_contra hne
    apply hu
    simp only [hDdef]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
      (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp
  -- The error `E := logDeriv g`; holomorphic on `U` (hence on `B ⊆ U`).
  refine ⟨logDeriv g, T, D, ?_, ?_, ?_, ?_, ?_⟩
  · -- E holomorphic on the box (subset of U).
    have hE_an : AnalyticOnNhd ℂ (logDeriv g) U := by
      intro x hx
      have : logDeriv g = fun z => deriv g z / g z := by
        ext z; rw [logDeriv_apply]
      rw [this]
      exact (hg_an x hx).deriv.div (hg_an x hx) (hg_ne ⟨x, hx⟩)
    exact (hE_an.mono (boxB_subset_ball.trans (le_of_eq hUdef.symm))).differentiableOn
  · -- membership in T implies zeta zero (the interior-strictness antecedents are unused here).
    intro ρ hρ _ _ _ _; exact hT_zero ρ hρ
  · -- multiplicity `D ρ ≥ 1` at every support point: zeta is analytic on `U` and vanishes there,
    -- so its analytic order (= the divisor) is `≥ 1`.
    intro ρ hρ
    have hρU : ρ ∈ U := by
      rw [hTdef, Set.Finite.mem_toFinset, Function.mem_support] at hρ
      exact (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
        (by rw [Function.mem_support]; exact hρ)
    have hρzero : riemannZeta ρ = 0 := hT_zero ρ hρ
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    -- `D ρ ≥ 0` (analytic ⇒ nonneg divisor) and `D ρ ≠ 0` (order ≥ 1 at a zero) give `D ρ ≥ 1`.
    -- order is finite (≠ ⊤): otherwise the meromorphic order would be ⊤ on `U ⊆ {1}ᶜ`.
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    -- `D ρ = analyticOrderNatAt zeta ρ` (as ℤ); the nat order is ≥ 1 at a zero.
    have hDeq : D ρ = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : D ρ = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda]
      rw [← Nat.cast_analyticOrderNatAt hfin]
      rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    rw [hDeq]
    have : 1 ≤ analyticOrderNatAt riemannZeta ρ := Nat.one_le_iff_ne_zero.mpr hnat_ne
    exact_mod_cast this
  · -- every zeta-zero in `U` lies in the support `s = T`: its divisor (= analytic order) is ≥ 1 ≠ 0.
    intro ρ hρU hρzero
    rw [hTdef, Set.Finite.mem_toFinset, Function.mem_support]
    have hAtρ : AnalyticAt ℂ riemannZeta ρ := hζU ρ hρU
    have hord_ne : analyticOrderAt riemannZeta ρ ≠ 0 :=
      hAtρ.analyticOrderAt_ne_zero.mpr hρzero
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro hcontra
      exact meromorphicOrderAt_zeta_ne_top ρ (hUsub hρU)
        (by rw [hAtρ.meromorphicOrderAt_eq, hcontra]; rfl)
    -- `D ρ = analyticOrderNatAt ≠ 0`.
    have hDeq : D ρ = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
      have hda : D ρ = ((analyticOrderAt riemannZeta ρ).map (Nat.cast)).untop₀ :=
        MeromorphicOn.AnalyticOnNhd.divisor_apply hζU hρU
      rw [hda, ← Nat.cast_analyticOrderNatAt hfin]; rfl
    have hnat_ne : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
      rw [Ne, ← Nat.cast_analyticOrderNatAt hfin] at hord_ne
      simpa using hord_ne
    rw [hDeq]
    exact_mod_cast hnat_ne
  · -- the split at each z ∈ U off the zeros.
    intro z hz hznz
    have hzroots : ∀ u ∈ T, z - u ≠ 0 := by
      intro u hu hcontra
      rw [sub_eq_zero] at hcontra
      exact hznz (by rw [hcontra]; exact hT_zero u hu)
    have hPfz : Pf z ≠ 0 := by
      rw [hPfdef]
      exact Finset.prod_ne_zero_iff.mpr (fun u hu => zpow_ne_zero _ (hzroots u hu))
    have hgz : g z ≠ 0 := hg_ne ⟨z, hz⟩
    have hPf_diff : DifferentiableAt ℂ Pf z := (hPf_an z hz).differentiableAt
    have hg_diff : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    have htrans : logDeriv riemannZeta z = logDeriv P z :=
      logDeriv_congr_of_codiscrete hζU hP_an hUopen hUconn hz hz hg_eqP
    rw [htrans, hPdef, logDeriv_mul z hPfz hgz hPf_diff hg_diff, hPfdef,
      logDeriv_finset_prod D z hzroots]

end BlaschkeBox
