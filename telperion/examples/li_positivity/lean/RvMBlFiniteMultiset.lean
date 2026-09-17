/-
RvMBlFiniteMultiset — the Bombieri-Lagarias FINITE-multiset positivity core (routes-roadmap B7-i).

For a finite set `S ⊆ ℂ` avoiding `0` and `1` and closed under `ρ ↦ 1 - conj ρ`, the Li-type sums

    Re ∑_{ρ ∈ S} (1 - ((1 - 1/ρ)⁻¹)^n)

are nonnegative for every `n > 0` **iff** every point lies on the critical line `Re ρ = 1/2`.

This is the purely finite algebraic core of the Bombieri-Lagarias positivity criterion
(J. Number Theory 77 (1999) 274-287), with the convergence/admissibility layer vacuous by
finiteness.  It is deliberately ZETA-FREE: `S` is an abstract finite set, not a zero set, so this
theorem carries NO zeta-specific RH content.  The analytic layer (band-limitedness of the BL test
function `gₙ`, the `T → ∞` limit) is DEFERRED to B6/B7 and is NOT smuggled in here.

Structure.  Write `w ρ := (1 - 1/ρ)⁻¹ = ρ/(ρ-1)`; then `Re ρ = 1/2 ⟺ |w ρ| = 1`.

  * Reverse (⇐): on the line `|w ρ| = 1` so `Re(w ρ ^ n) ≤ 1`, hence `1 - Re(w ρ ^ n) ≥ 0` termwise.
  * Forward (⇒): contrapositive.  An off-line point (via the `ρ ↦ 1 - conj ρ` symmetry, which sends
    `|w|` to `|w|⁻¹`) forces a maximal modulus `R = max_ρ |w ρ| > 1`.  Simultaneous topological
    recurrence on the compact torus `∏ {|z|=1}` (`simul_recur`, from sequential compactness) yields
    arbitrarily large `m` with `w ρ ^ m ≈ R^m` for every maximal-modulus `ρ`; the modulus gap to the
    rest then drives `Re ∑ w ρ ^ m` above `#S`, i.e. the summand strictly negative.  No equidistribution
    axiom, no Pringsheim — just Bolzano-Weierstrass on the torus.

Kernel-clean: `#print axioms bl_finite_multiset` = `[propext, Classical.choice, Quot.sound]`, 0 sorryAx.
conjecture1_proved = False — this is the finite face only.
-/
import Mathlib

open Complex Finset Filter Topology

noncomputable def wOf (ρ : ℂ) : ℂ := (1 - 1/ρ)⁻¹

-- ENGINE LEMMAS (proved separately, here as opaque hypotheses via `theorem`s):
theorem simul_recur {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ m : ℕ, N₀ ≤ m ∧ ∀ i, ‖u i ^ m - 1‖ < ε := by
  set x : ℕ → (ι → ℂ) := fun n i => (u i)^n with hx
  set S : Set (ι → ℂ) := {v | ∀ i, ‖v i‖ = 1} with hS
  have hui0 : ∀ i, u i ≠ 0 := by intro i h; have := hu i; rw [h] at this; simp at this
  have hxS : ∀ n, x n ∈ S := by intro n i; simp only [hx, norm_pow, hu i, one_pow]
  have hScompact : IsCompact S := by
    have : S = Set.pi Set.univ (fun _ : ι => Metric.sphere (0:ℂ) 1) := by ext v; simp [hS]
    rw [this]; exact isCompact_univ_pi (fun _ => isCompact_sphere 0 1)
  obtain ⟨a, haS, φ, hφmono, hφlim⟩ := hScompact.tendsto_subseq hxS
  have hcomp : ∀ i, Tendsto (fun j => (x (φ j)) i) atTop (𝓝 (a i)) := fun i =>
    (continuous_apply i).continuousAt.tendsto.comp hφlim
  have hev : ∀ᶠ j in atTop, ∀ i, ‖(x (φ j)) i - a i‖ < ε/2 := by
    rw [eventually_all]; intro i
    have hmet := hcomp i; rw [Metric.tendsto_atTop] at hmet
    obtain ⟨J, hJ⟩ := hmet (ε/2) (by linarith)
    filter_upwards [eventually_ge_atTop J] with j hj
    have := hJ j hj; rwa [dist_eq_norm] at this
  obtain ⟨P, hP⟩ := eventually_atTop.1 hev
  set p := P with hp
  set q := P + (φ P) + N₀ with hq
  have hpq : p ≤ q := by omega
  have hφP_le : φ p ≤ φ q := hφmono.le_iff_le.2 hpq
  have hφq_ge : φ q ≥ q := hφmono.le_apply
  have hm : φ q - φ p ≥ N₀ := by
    have hqge : q ≥ φ p + N₀ := by rw [hq, hp]; omega
    omega
  refine ⟨φ q - φ p, hm, ?_⟩
  intro i
  have key : u i ^ (φ q - φ p) = (x (φ q) i) * (x (φ p) i)⁻¹ := by
    simp only [hx]; rw [← pow_sub₀ (u i) (hui0 i) hφP_le]
  rw [key]
  have hxp1 : ‖x (φ p) i‖ = 1 := hxS (φ p) i
  have hrw : (x (φ q) i) * (x (φ p) i)⁻¹ - 1 = ((x (φ q) i) - (x (φ p) i)) * (x (φ p) i)⁻¹ := by
    have hxp0 : x (φ p) i ≠ 0 := by rw [← norm_ne_zero_iff, hxp1]; norm_num
    field_simp
  rw [hrw, norm_mul, norm_inv, hxp1]; simp only [inv_one, mul_one]
  have hqclose : ‖(x (φ q)) i - a i‖ < ε/2 := hP q (by omega) i
  have hpclose : ‖(x (φ p)) i - a i‖ < ε/2 := hP p (le_refl _) i
  calc ‖x (φ q) i - x (φ p) i‖
      ≤ ‖(x (φ q) i - a i)‖ + ‖(a i - x (φ p) i)‖ := by
        simpa using norm_add_le (x (φ q) i - a i) (a i - x (φ p) i)
    _ < ε/2 + ε/2 := by rw [norm_sub_rev (a i)]; linarith
    _ = ε := by ring

theorem perelem (z : ℂ) (R : ℝ) (hR : 0 < R) (m : ℕ) (ε : ℝ)
    (h : ‖(z/(R:ℂ))^m - 1‖ < ε) : (R:ℝ)^m * (1 - ε) ≤ (z^m).re := by
  have hRm : (0:ℝ) < (R:ℝ)^m := pow_pos hR m
  set ζ : ℂ := (z/(R:ℂ))^m with hζ
  have hRe : 1 - ε < ζ.re := by
    have h1 : |ζ.re - 1| ≤ ‖ζ - 1‖ := by
      have := Complex.abs_re_le_norm (ζ - 1); simpa [Complex.sub_re] using this
    have h2 : |ζ.re - 1| < ε := lt_of_le_of_lt h1 h
    have := abs_lt.1 h2; linarith [this.1]
  have hRne : (R:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hzm : z^m = (R:ℂ)^m * ζ := by rw [hζ, div_pow]; field_simp
  have hre_eq : (z^m).re = (R:ℝ)^m * ζ.re := by
    rw [hzm, show ((R:ℂ)^m * ζ) = ((((R:ℝ)^m : ℝ)) : ℂ) * ζ by push_cast; ring,
       Complex.re_ofReal_mul]
  rw [hre_eq]
  have : (R:ℝ)^m * (1 - ε) ≤ (R:ℝ)^m * ζ.re :=
    mul_le_mul_of_nonneg_left (le_of_lt hRe) (le_of_lt hRm)
  linarith

theorem dominance (R r cM cS B : ℝ) (hR : 1 < R) (hr0 : 0 ≤ r) (hrR : r < R)
    (hcM : 0 < cM) (_hcS : 0 ≤ cS) :
    ∃ N0 : ℕ, ∀ m, N0 ≤ m → B < cM * R^m - cS * r^m := by
  have hRpos : 0 < R := by linarith
  have key : Tendsto (fun m => cM * R^m - cS * r^m) atTop atTop := by
    have hfac : ∀ m : ℕ, cM * R^m - cS * r^m = R^m * (cM - cS * (r/R)^m) := by
      intro m; rw [div_pow]; field_simp
    rw [tendsto_congr hfac]
    apply Filter.Tendsto.atTop_mul_pos hcM (tendsto_pow_atTop_atTop_of_one_lt hR)
    have hz : Tendsto (fun m => (r/R)^m) atTop (𝓝 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      rw [div_lt_one hRpos]; exact hrR
    have : Tendsto (fun m => cM - cS * (r/R)^m) atTop (𝓝 (cM - cS * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    simpa using this
  exact (key.eventually_gt_atTop B).exists_forall_of_atTop

theorem forward_neg (S : Finset ℂ) (hSne : S.Nonempty)
    (hR1 : 1 < S.sup' hSne (fun ρ => ‖wOf ρ‖)) :
    ∃ n : ℕ, 0 < n ∧ (∑ ρ ∈ S, (1 - (wOf ρ)^n)).re < 0 := by
  classical
  set R := S.sup' hSne (fun ρ => ‖wOf ρ‖) with hRdef
  set M := S.filter (fun ρ => ‖wOf ρ‖ = R) with hM
  have hle : ∀ ρ ∈ S, ‖wOf ρ‖ ≤ R := fun ρ hρ => Finset.le_sup' (fun ρ => ‖wOf ρ‖) hρ
  have hMne : M.Nonempty := by
    obtain ⟨ρ0, hρ0mem, hρ0eq⟩ := Finset.exists_mem_eq_sup' hSne (fun ρ => ‖wOf ρ‖)
    exact ⟨ρ0, by rw [hM, mem_filter]; exact ⟨hρ0mem, hρ0eq.symm⟩⟩
  have hR0 : 0 < R := lt_trans one_pos hR1
  -- second-max modulus r on Sc = S \ M ; if Sc empty, r=0.
  set Sc := S.filter (fun ρ => ¬ ‖wOf ρ‖ = R) with hSc
  -- r := if Sc.Nonempty then sup' else 0, with r<R and r≥0 and ∀ρ∈Sc, ‖wOf ρ‖ ≤ r
  obtain ⟨r, hr0, hrR, hrbound⟩ :
      ∃ r : ℝ, 0 ≤ r ∧ r < R ∧ ∀ ρ ∈ Sc, ‖wOf ρ‖ ≤ r := by
    rcases Sc.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, le_refl 0, hR0, by intro ρ hρ; rw [hemp] at hρ; simp at hρ⟩
    · refine ⟨Sc.sup' hne (fun ρ => ‖wOf ρ‖), ?_, ?_, ?_⟩
      · obtain ⟨ρ1, hρ1⟩ := hne
        exact le_trans (norm_nonneg _) (Finset.le_sup' (fun ρ => ‖wOf ρ‖) hρ1)
      · rw [Finset.sup'_lt_iff]
        intro ρ hρ
        have hmem := Finset.mem_filter.1 hρ
        have hρS : ρ ∈ S := hmem.1
        have hne' : ‖wOf ρ‖ ≠ R := hmem.2
        exact lt_of_le_of_ne (hle ρ hρS) hne'
      · intro ρ hρ; exact Finset.le_sup' (fun ρ => ‖wOf ρ‖) hρ
  -- cardinalities
  set kM : ℝ := (M.card : ℝ) with hkM
  set kSc : ℝ := (Sc.card : ℝ) with hkSc
  have hkMpos : 0 < kM := by
    rw [hkM]; exact_mod_cast Finset.card_pos.2 hMne
  have hkMge1 : (1:ℝ) ≤ kM := by rw [hkM]; exact_mod_cast Finset.card_pos.2 hMne
  set ε : ℝ := 1/(2*kM) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set cM : ℝ := kM * (1 - ε) with hcMdef
  have hcMpos : 0 < cM := by
    rw [hcMdef]; apply mul_pos hkMpos; rw [hεdef]
    have : 1/(2*kM) ≤ 1/2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    linarith
  have hkScnn : 0 ≤ kSc := by rw [hkSc]; positivity
  -- dominance threshold
  obtain ⟨N0, hN0⟩ := dominance R r cM kSc (S.card : ℝ) hR1 hr0 hrR hcMpos hkScnn
  -- simul_recur on M subtype
  have huM : ∀ ρ : {x // x ∈ M}, ‖wOf ρ.1 / (R:ℂ)‖ = 1 := by
    rintro ⟨ρ, hρ⟩
    have hmem := Finset.mem_filter.1 hρ
    have hnorm : ‖wOf ρ‖ = R := hmem.2
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_pos hR0, div_self (ne_of_gt hR0)]
  obtain ⟨m, hmN0, hmclose⟩ := simul_recur (ι := {x // x ∈ M})
    (fun ρ => wOf ρ.1 / (R:ℂ)) huM ε hεpos (max N0 1)
  have hm1 : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right N0 1) hmN0)
  have hmN0' : N0 ≤ m := le_trans (le_max_left N0 1) hmN0
  refine ⟨m, hm1, ?_⟩
  -- Q lower bound: Σ_S (wOf ρ^m).re ≥ cM R^m - kSc r^m > |S|
  have hsplit : (∑ ρ ∈ S, ((wOf ρ)^m).re)
      = (∑ ρ ∈ M, ((wOf ρ)^m).re) + (∑ ρ ∈ Sc, ((wOf ρ)^m).re) := by
    rw [hM, hSc]
    exact (Finset.sum_filter_add_sum_filter_not S (fun ρ => ‖wOf ρ‖ = R) (fun ρ => ((wOf ρ)^m).re)).symm
  -- M bound
  have hMbound : kM * (R^m * (1 - ε)) ≤ ∑ ρ ∈ M, ((wOf ρ)^m).re := by
    have hpt : ∀ ρ ∈ M, R^m * (1 - ε) ≤ ((wOf ρ)^m).re := by
      intro ρ hρ; exact perelem (wOf ρ) R hR0 m ε (hmclose ⟨ρ, hρ⟩)
    calc kM * (R^m * (1-ε))
        = ∑ _ρ ∈ M, (R^m * (1-ε)) := by rw [hkM, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ρ ∈ M, ((wOf ρ)^m).re := Finset.sum_le_sum hpt
  -- Sc bound
  have hScbound : - (kSc * r^m) ≤ ∑ ρ ∈ Sc, ((wOf ρ)^m).re := by
    have hpt : ∀ ρ ∈ Sc, -(r^m) ≤ ((wOf ρ)^m).re := by
      intro ρ hρ
      have hh := Complex.abs_re_le_norm ((wOf ρ)^m)
      have h3 : -‖(wOf ρ)^m‖ ≤ ((wOf ρ)^m).re := (abs_le.1 hh).1
      have h4 : ‖(wOf ρ)^m‖ = ‖wOf ρ‖^m := by rw [norm_pow]
      have h5 : ‖wOf ρ‖^m ≤ r^m := pow_le_pow_left₀ (norm_nonneg _) (hrbound ρ hρ) m
      rw [h4] at h3; linarith [neg_le_neg h5]
    calc - (kSc * r^m)
        = ∑ _ρ ∈ Sc, (-(r^m)) := by rw [hkSc, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ ρ ∈ Sc, ((wOf ρ)^m).re := Finset.sum_le_sum hpt
  -- combine
  have hQ : (S.card : ℝ) < ∑ ρ ∈ S, ((wOf ρ)^m).re := by
    have hdom := hN0 m hmN0'
    have hcMrw : cM * R^m = kM * (R^m * (1-ε)) := by rw [hcMdef]; ring
    rw [hsplit]
    have : cM * R^m - kSc * r^m ≤ (∑ ρ ∈ M, ((wOf ρ)^m).re) + (∑ ρ ∈ Sc, ((wOf ρ)^m).re) := by
      rw [hcMrw]; linarith [hMbound, hScbound]
    linarith
  -- conclude
  have hsum_re : (∑ ρ ∈ S, (1 - (wOf ρ)^m)).re
      = (S.card : ℝ) - ∑ ρ ∈ S, ((wOf ρ)^m).re := by
    rw [Complex.re_sum]
    have hc : ∀ ρ ∈ S, (1 - (wOf ρ)^m).re = 1 - ((wOf ρ)^m).re := by
      intro ρ _; rw [Complex.sub_re, Complex.one_re]
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum_re]; linarith

theorem online_normSq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hre : ρ.re = 1/2) :
    Complex.normSq (wOf ρ) = 1 := by
  have hnρ0 : Complex.normSq ρ ≠ 0 := by rw [ne_eq, Complex.normSq_eq_zero]; exact h0
  have hwe : wOf ρ = ρ / (ρ-1) := by
    unfold wOf; rw [show (1 - 1/ρ) = (ρ - 1)/ρ by field_simp, inv_div]
  have hnum : Complex.normSq (ρ - 1) = Complex.normSq ρ := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [hre]; ring
  rw [hwe, Complex.normSq_div, hnum, div_self hnρ0]

theorem sym_normSq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1)
    (h0' : (1 - (starRingEnd ℂ) ρ) ≠ 0) (h1' : (1 - (starRingEnd ℂ) ρ) ≠ 1) :
    Complex.normSq (wOf (1 - (starRingEnd ℂ) ρ)) = (Complex.normSq (wOf ρ))⁻¹ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  set σ := 1 - (starRingEnd ℂ) ρ with hσ
  have hσ1' : σ - 1 ≠ 0 := sub_ne_zero.mpr h1'
  have hwσ : wOf σ = σ/(σ-1) := by
    unfold wOf; rw [show (1 - 1/σ) = (σ-1)/σ by field_simp, inv_div]
  have hwρ : wOf ρ = ρ/(ρ-1) := by
    unfold wOf; rw [show (1 - 1/ρ) = (ρ-1)/ρ by field_simp, inv_div]
  rw [hwσ, hwρ, Complex.normSq_div, Complex.normSq_div]
  have e2 : σ - 1 = - (starRingEnd ℂ) ρ := by rw [hσ]; ring
  rw [show σ = 1 - (starRingEnd ℂ) ρ from rfl, e2]
  have n1 : Complex.normSq (1 - (starRingEnd ℂ) ρ) = Complex.normSq (ρ - 1) := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  have n2 : Complex.normSq (- (starRingEnd ℂ) ρ) = Complex.normSq ρ := by
    simp [Complex.normSq_apply]
  rw [n1, n2, inv_div]

-- off-line normSq ≠ 1

theorem offline_normSq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hre : ρ.re ≠ 1/2) :
    Complex.normSq (wOf ρ) ≠ 1 := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hnρ1 : Complex.normSq (ρ-1) ≠ 0 := by rw [ne_eq, Complex.normSq_eq_zero]; exact hρ1'
  have hwe : wOf ρ = ρ / (ρ-1) := by
    unfold wOf; rw [show (1 - 1/ρ) = (ρ - 1)/ρ by field_simp, inv_div]
  rw [hwe, Complex.normSq_div, ne_eq, div_eq_one_iff_eq hnρ1]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  intro heq; apply hre; nlinarith [heq]

theorem wOf_ne_zero (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : wOf ρ ≠ 0 := by
  unfold wOf
  rw [ne_eq, inv_eq_zero]
  rw [show (1 - 1/ρ) = (ρ-1)/ρ by field_simp]
  rw [div_eq_zero_iff]
  push Not
  refine ⟨sub_ne_zero.mpr h1, h0⟩

theorem norm_gt_one_iff (z : ℂ) : 1 < ‖z‖ ↔ 1 < Complex.normSq z := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

theorem R_gt_one (S : Finset ℂ) (hSne : S.Nonempty)
    (h0S : (0:ℂ) ∉ S) (h1S : (1:ℂ) ∉ S)
    (hsym : ∀ ρ ∈ S, 1 - (starRingEnd ℂ) ρ ∈ S)
    (ρ0 : ℂ) (hρ0 : ρ0 ∈ S) (hoff : ρ0.re ≠ 1/2) :
    1 < S.sup' hSne (fun ρ => ‖wOf ρ‖) := by
  have h0 : ρ0 ≠ 0 := fun h => h0S (h ▸ hρ0)
  have h1 : ρ0 ≠ 1 := fun h => h1S (h ▸ hρ0)
  have hns : Complex.normSq (wOf ρ0) ≠ 1 := offline_normSq ρ0 h0 h1 hoff
  have hw0 : wOf ρ0 ≠ 0 := wOf_ne_zero ρ0 h0 h1
  rcases lt_or_gt_of_ne hns with hlt | hgt
  · set σ := 1 - (starRingEnd ℂ) ρ0 with hσ
    have hσS : σ ∈ S := hsym ρ0 hρ0
    have h0σ : σ ≠ 0 := fun h => h0S (h ▸ hσS)
    have h1σ : σ ≠ 1 := fun h => h1S (h ▸ hσS)
    have hsymeq : Complex.normSq (wOf σ) = (Complex.normSq (wOf ρ0))⁻¹ :=
      sym_normSq ρ0 h0 h1 h0σ h1σ
    have hnpos : 0 < Complex.normSq (wOf ρ0) := Complex.normSq_pos.2 hw0
    have hgt1 : 1 < Complex.normSq (wOf σ) := by
      rw [hsymeq, one_lt_inv_iff₀]; exact ⟨hnpos, hlt⟩
    calc (1:ℝ) < ‖wOf σ‖ := (norm_gt_one_iff _).2 hgt1
      _ ≤ S.sup' hSne (fun ρ => ‖wOf ρ‖) := Finset.le_sup' (fun ρ => ‖wOf ρ‖) hσS
  · calc (1:ℝ) < ‖wOf ρ0‖ := (norm_gt_one_iff _).2 hgt
      _ ≤ S.sup' hSne (fun ρ => ‖wOf ρ‖) := Finset.le_sup' (fun ρ => ‖wOf ρ‖) hρ0

theorem reverse_dir (S : Finset ℂ)
    (h0S : (0:ℂ) ∉ S) (h1S : (1:ℂ) ∉ S)
    (hon : ∀ ρ ∈ S, ρ.re = 1/2) :
    ∀ n : ℕ, 0 < n → 0 ≤ (∑ ρ ∈ S, (1 - (wOf ρ)^n)).re := by
  intro n _
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro ρ hρ
  have h0 : ρ ≠ 0 := fun h => h0S (h ▸ hρ)
  have h1 : ρ ≠ 1 := fun h => h1S (h ▸ hρ)
  have hns : Complex.normSq (wOf ρ) = 1 := online_normSq ρ h0 h1 (hon ρ hρ)
  have hnsn : Complex.normSq ((wOf ρ)^n) = 1 := by rw [map_pow, hns, one_pow]
  have hsq : ((wOf ρ)^n).re * ((wOf ρ)^n).re + ((wOf ρ)^n).im * ((wOf ρ)^n).im = 1 := by
    have := hnsn; rwa [Complex.normSq_apply] at this
  have hre_le : ((wOf ρ)^n).re ≤ 1 := by
    nlinarith [hsq, mul_self_nonneg ((wOf ρ)^n).im, mul_self_nonneg (((wOf ρ)^n).re - 1)]
  rw [Complex.sub_re, Complex.one_re]; linarith

theorem bl_finite_multiset (S : Finset ℂ)
    (h0 : (0 : ℂ) ∉ S) (h1 : (1 : ℂ) ∉ S)
    (hsym : ∀ ρ ∈ S, 1 - (starRingEnd ℂ) ρ ∈ S) :
    (∀ n : ℕ, 0 < n →
        0 ≤ (∑ ρ ∈ S, (1 - ((1 - 1 / ρ)⁻¹) ^ n)).re)
      ↔ ∀ ρ ∈ S, ρ.re = 1 / 2 := by
  -- rewrite (1 - 1/ρ)⁻¹ as wOf ρ
  have hwrw : ∀ (n : ℕ), (∑ ρ ∈ S, (1 - ((1 - 1 / ρ)⁻¹) ^ n))
      = (∑ ρ ∈ S, (1 - (wOf ρ) ^ n)) := by
    intro n; rfl
  constructor
  · -- forward: positivity → on-line, by contraposition
    intro hpos
    by_contra hcon
    push Not at hcon
    obtain ⟨ρ0, hρ0, hoff⟩ := hcon
    have hSne : S.Nonempty := ⟨ρ0, hρ0⟩
    have hR1 : 1 < S.sup' hSne (fun ρ => ‖wOf ρ‖) :=
      R_gt_one S hSne h0 h1 hsym ρ0 hρ0 hoff
    obtain ⟨n, hn, hneg⟩ := forward_neg S hSne hR1
    have := hpos n hn
    rw [hwrw n] at this
    linarith
  · -- reverse
    intro hon n hn
    rw [hwrw n]
    exact reverse_dir S h0 h1 hon n hn

