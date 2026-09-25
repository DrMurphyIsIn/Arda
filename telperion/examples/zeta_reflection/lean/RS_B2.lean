/-  RS_B2.lean -- lane RS, ANDURIL brick B2: RIEMANN'S INTEGRAL REPRESENTATION OF zeta(s) for
    general complex s, with the residue bookkeeping (the exact Riemann-Siegel formula).
    Mathlib-only (imports `RS_Entire`).

    ## The headline (`riemann_siegel_integral`)

    For every complex s that is not an odd positive integer (s ∉ {1, 3, 5, ...}), all N, M ∈ ℕ and
    every c1 ∈ (N, N+1), c2 ∈ (M, M+1):

      zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                - lineUp c1 (x |-> rsG x x^(-s)) + chi(s) lineDn c2 (x |-> rsH x x^(s-1)),

      rsG x = e^{i pi x^2}/(e^{i pi x} - e^{-i pi x}),  rsH x = e^{-i pi x^2}/(e^{i pi x} - e^{-i pi x}),
      chi(s) = pi^(s-1/2) Gamma((1-s)/2) / Gamma(s/2),
      lineUp c F = int F(c + v(1+i))(1+i) dv,   lineDn c F = int F(c + v(1-i))(1-i) dv.

    This is Riemann's integral (Siegel 1932; Edwards ch. 7; Titchmarsh 2.10) in exactly the form
    used for the Riemann-Siegel saddle-point analysis: the remainder integrals run along the
    steepest-descent directions of e^{+-i pi x^2} and may cross the real axis anywhere in the gap.
    (At s = 3, 5, ... Mathlib's Gamma((1-s)/2) takes the junk value 0 at its pole, so those points
    are excluded; s = 1 is the pole of zeta.)

    ## How it is proved (no residue theorem, no Hankel contour)

      1. N = M = 0, Re s > 2 (`rs_identity_re_gt_two`): the Mellin identity (RS_Mellin: Fubini with
         the complex Gamma integral, the Mordell closed form, the Bose integral = Gamma zeta) and the
         folding of the chi-side line (RS_Fold), assembled with the Gamma identity for chi.
      2. All s ∉ {1,3,5,...} (`rs_identity`): identity theorem on the connected open set
         ℂ \ {1,3,5,...}; both sides are holomorphic there (RS_Entire).
      3. General N, M (`lineUp_book`, `lineDn_book`): induction, crossing one pole at a time
         (`lineUp_cross`, `lineDn_cross` in RS_Kernel).

    ## Critical line (`completedRiemannZeta_eq_rs`, `completed_re_eq_rs_cos`)

    For s = 1/2 + it and c ∈ (N, N+1), with S = sum_{n<=N} n^(-s) and R = -lineUp c (rsG x^(-s)):
        completedRiemannZeta s = 2 Re( Gammaℝ(s) (S + R) )        (a real number),
    and, whenever Gammaℝ(s) = M e^{i phi} with M > 0 (the island's polar form),
        Re completedRiemannZeta(s) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} R) ).
    So Z(t) = 2 sum n^(-1/2) cos(theta - t log n) + 2 Re(e^{i theta} R_N(t)) EXACTLY: the only
    analytic input left for sign certification is a bound on the remainder R_N(t) (brick B3).

    conjecture1_proved = False.  An exact integral identity for zeta; nothing here bears on RH.
-/
import RS_Entire

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. The identity for Re s > 2 -/

theorem one_add_exp_ne_zero {s : ℂ} (h : ∀ k : ℤ, s ≠ 2 * k + 1) : 1 + cexp (↑π * I * s) ≠ 0 := by
  intro h0
  have h1 : cexp (↑π * I * s) = cexp (↑π * I) := by
    rw [Complex.exp_pi_mul_I]; linear_combination h0
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  apply h n
  have h2 : (↑π * I : ℂ) * s = (↑π * I) * (2 * n + 1) := by linear_combination hn
  exact mul_left_cancel₀ (mul_ne_zero pi_ne_zero' I_ne_zero) h2

/-- **Riemann's integral, Re s > 2, N = M = 0.** -/
theorem rs_identity_re_gt_two {s : ℂ} (hs : 2 < s.re) (h : 1 + cexp (↑π * I * s) ≠ 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    riemannZeta s = -lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  have hM := mellin_identity hc hc1 (s := s) (by linarith)
  have hB := lineDn_eq_fold hs hc hc1
  have hχ := rsChi_eq (s := s) (by linarith) h
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [hB, hχ]
  set K := (2 * (π : ℂ)) ^ s * (1 + I) ^ s * (1 - I) ^ (-s) with hK
  have e : K / (Gamma s * (1 + cexp (↑π * I * s))) * ((1 + cexp (↑π * I * s)) * rsHR s) =
      K * rsHR s / Gamma s := by
    rw [div_mul_eq_mul_div, show K * ((1 + cexp (↑π * I * s)) * rsHR s) =
      K * rsHR s * (1 + cexp (↑π * I * s)) by ring, mul_div_mul_right _ _ h]
  rw [e, eq_comm, ← sub_eq_zero]
  have : -lineUp c (fun x => rsG x * x ^ (-s)) + K * rsHR s / Gamma s - riemannZeta s =
      (K * rsHR s - Gamma s * lineUp c (fun x => rsG x * x ^ (-s)) - Gamma s * riemannZeta s) /
        Gamma s := by
    field_simp
    ring
  rw [this, hM]
  simp

/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/

/-- The odd positive integers, where Mathlib's `Gamma ((1-s)/2)` sits at a pole. -/
def oddSet : Set ℂ := Set.range (fun k : ℕ => (2 * k + 1 : ℂ))

theorem mem_oddSet_compl {s : ℂ} : s ∈ oddSetᶜ ↔ ∀ k : ℕ, s ≠ 2 * k + 1 := by
  simp only [oddSet, mem_compl_iff, mem_range, not_exists]
  exact forall_congr' fun k => ne_comm

theorem isClosed_oddSet : IsClosed oddSet := by
  apply Metric.isClosed_of_pairwise_le_dist (ε := 1) one_pos
  rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hne
  have hjk : (j : ℤ) - k ≠ 0 := by
    intro h; apply hne; have : j = k := by omega
    rw [this]
  rw [Complex.dist_eq, show ((2 * j + 1 : ℂ) - (2 * k + 1)) = ((2 * ((j : ℤ) - k) : ℤ) : ℂ) by
    push_cast; ring, Complex.norm_intCast]
  have h1 : (1 : ℤ) ≤ |2 * ((j : ℤ) - k)| := by
    have := Int.one_le_abs hjk
    rw [abs_mul]; simp; omega
  exact_mod_cast h1

theorem isPreconnected_oddSet_compl : IsPreconnected oddSetᶜ :=
  ((Set.countable_range _).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/

theorem rs_identity {s : ℂ} (hs : ∀ k : ℕ, s ≠ 2 * k + 1) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    riemannZeta s = -lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  have hUo : IsOpen oddSetᶜ := isClosed_oddSet.isOpen_compl
  have hf : DifferentiableOn ℂ riemannZeta oddSetᶜ := by
    intro z hz
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro h1
    exact mem_oddSet_compl.mp hz 0 (by rw [h1]; simp)
  have hg : DifferentiableOn ℂ (fun z : ℂ => -lineUp c (fun x => rsG x * x ^ (-z)) +
      rsChi z * lineDn c (fun x => rsH x * x ^ (z - 1))) oddSetᶜ := by
    intro z hz
    exact ((differentiable_rsA hc hcl z).neg.add
      ((differentiableAt_rsChi (mem_oddSet_compl.mp hz)).mul
        (differentiable_rsB hc hcl z))).differentiableWithinAt
  have h52 : (5 / 2 : ℂ) ∈ oddSetᶜ := by
    rw [mem_oddSet_compl]
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h1 : (0 : ℝ) < k := by linarith
    have h2 : (k : ℝ) < 1 := by linarith
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  have hev : riemannZeta =ᶠ[𝓝 (5 / 2 : ℂ)] (fun z : ℂ => -lineUp c (fun x => rsG x * x ^ (-z)) +
      rsChi z * lineDn c (fun x => rsH x * x ^ (z - 1))) := by
    filter_upwards [Metric.ball_mem_nhds (5 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
    have hre : |z.re - 5 / 2| < 1 / 4 := by
      have h1 := Metric.mem_ball.mp hz
      rw [Complex.dist_eq] at h1
      have h2 := Complex.abs_re_le_norm (z - 5 / 2)
      simp at h2
      linarith
    rw [abs_lt] at hre
    refine rs_identity_re_gt_two (by linarith [hre.1]) (one_add_exp_ne_zero ?_) hc hc1
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h1 : (0 : ℝ) < k := by linarith [hre.1]
    have h2 : (k : ℝ) < 1 := by linarith [hre.2]
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo)
    isPreconnected_oddSet_compl h52 hev (mem_oddSet_compl.mpr hs)

/-! ## 4. Residue bookkeeping -/

theorem norm_cpow_le_of_ge {x w : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) :
    ‖x ^ w‖ ≤ ((m ^ w.re + 1) * Real.exp (π * |w.im|)) * Real.exp (|w.re| * ‖x‖) := by
  have hpos : 0 < ‖x‖ := lt_of_lt_of_le hm hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hpos
  rw [Complex.norm_cpow_of_ne_zero hx0]
  have hB : 1 / Real.exp (x.arg * w.im) ≤ Real.exp (π * |w.im|) := by
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h2 := Complex.abs_arg_le_pi x
    have h3 : -(x.arg * w.im) ≤ |x.arg * w.im| := neg_le_abs _
    rw [abs_mul] at h3
    nlinarith [abs_nonneg w.im, abs_nonneg x.arg]
  have hA : ‖x‖ ^ w.re ≤ (m ^ w.re + 1) * Real.exp (|w.re| * ‖x‖) := by
    have hE : 1 ≤ Real.exp (|w.re| * ‖x‖) := Real.one_le_exp (by positivity)
    have hm0 : 0 ≤ m ^ w.re := Real.rpow_nonneg hm.le _
    rcases le_total w.re 0 with h | h
    · have := Real.rpow_le_rpow_of_nonpos hm hx h
      nlinarith
    · have : ‖x‖ ^ w.re ≤ Real.exp (|w.re| * ‖x‖) := by
        rw [Real.rpow_def_of_pos hpos, abs_of_nonneg h]
        apply Real.exp_le_exp.mpr
        have := Real.log_le_sub_one_of_pos hpos
        nlinarith
      nlinarith
  calc ‖x‖ ^ w.re / Real.exp (x.arg * w.im)
      = ‖x‖ ^ w.re * (1 / Real.exp (x.arg * w.im)) := by ring
    _ ≤ ((m ^ w.re + 1) * Real.exp (|w.re| * ‖x‖)) * Real.exp (π * |w.im|) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = ((m ^ w.re + 1) * Real.exp (π * |w.im|)) * Real.exp (|w.re| * ‖x‖) := by ring

theorem slit_of_upStrip {x : ℂ} {a b : ℝ} (ha : 0 < a) (hx : x.re - x.im ∈ Icc a b) :
    x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; have := hx.1; rw [h] at this; linarith
  · right; exact h

theorem slit_of_dnStrip {x : ℂ} {a b : ℝ} (ha : 0 < a) (hx : x.re + x.im ∈ Icc a b) :
    x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; have := hx.1; rw [h] at this; linarith
  · right; exact h

theorem norm_ge_of_upStrip {x : ℂ} {a b : ℝ} (hx : x.re - x.im ∈ Icc a b) (_ha : 0 < a) :
    a / 2 ≤ ‖x‖ := by
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  have := hx.1
  have h3 : x.re - x.im ≤ |x.re| + |x.im| := by
    linarith [le_abs_self x.re, neg_abs_le x.im]
  linarith

theorem norm_ge_of_dnStrip {x : ℂ} {a b : ℝ} (hx : x.re + x.im ∈ Icc a b) (_ha : 0 < a) :
    a / 2 ≤ ‖x‖ := by
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  have := hx.1
  have h3 : x.re + x.im ≤ |x.re| + |x.im| := by
    linarith [le_abs_self x.re, le_abs_self x.im]
  linarith

/-- The slope-(+1) remainder integral may be moved inside the gap `(n, n+1)`, `n >= 0`. -/
theorem lineUp_cpow_same_gap (s : ℂ) {n : ℕ} {c c' : ℝ} (h : (n : ℝ) < c) (h' : c < n + 1)
    (k : (n : ℝ) < c') (k' : c' < n + 1) :
    lineUp c (fun x => rsG x * x ^ (-s)) = lineUp c' (fun x => rsG x * x ^ (-s)) := by
  have key : ∀ a b : ℝ, a ≤ b → (n : ℝ) < a → b < n + 1 →
      lineUp a (fun x => rsG x * x ^ (-s)) = lineUp b (fun x => rsG x * x ^ (-s)) := by
    intro a b hab ha hb
    have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
    refine lineUp_same_gap hab (fun m hm => ?_) (fun x hx => ?_) (A := ((a / 2) ^ (-s).re + 1) *
      Real.exp (π * |(-s).im|)) (B := |(-s).re|) (fun x hx => norm_cpow_le_of_ge (by positivity)
        (norm_ge_of_upStrip hx ha0))
    · have h1 : (n : ℝ) < m := lt_of_lt_of_le ha hm.1
      have h2 : (m : ℝ) < n + 1 := lt_of_le_of_lt hm.2 hb
      have h1' : (n : ℤ) < m := by exact_mod_cast h1
      have h2' : m < (n : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact (differentiableAt_id).cpow (differentiableAt_const _) (slit_of_upStrip ha0 hx)
  rcases le_total c c' with hcc | hcc
  · exact key c c' hcc h k'
  · exact (key c' c hcc k h').symm

theorem lineDn_cpow_same_gap (s : ℂ) {n : ℕ} {c c' : ℝ} (h : (n : ℝ) < c) (h' : c < n + 1)
    (k : (n : ℝ) < c') (k' : c' < n + 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) = lineDn c' (fun x => rsH x * x ^ (s - 1)) := by
  have key : ∀ a b : ℝ, a ≤ b → (n : ℝ) < a → b < n + 1 →
      lineDn a (fun x => rsH x * x ^ (s - 1)) = lineDn b (fun x => rsH x * x ^ (s - 1)) := by
    intro a b hab ha hb
    have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
    refine lineDn_same_gap hab (fun m hm => ?_) (fun x hx => ?_) (A := ((a / 2) ^ (s - 1).re + 1) *
      Real.exp (π * |(s - 1).im|)) (B := |(s - 1).re|) (fun x hx => norm_cpow_le_of_ge
        (by positivity) (norm_ge_of_dnStrip hx ha0))
    · have h1 : (n : ℝ) < m := lt_of_lt_of_le ha hm.1
      have h2 : (m : ℝ) < n + 1 := lt_of_le_of_lt hm.2 hb
      have h1' : (n : ℤ) < m := by exact_mod_cast h1
      have h2' : m < (n : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact (differentiableAt_id).cpow (differentiableAt_const _) (slit_of_dnStrip ha0 hx)
  rcases le_total c c' with hcc | hcc
  · exact key c c' hcc h k'
  · exact (key c' c hcc k h').symm

/-- **Bookkeeping, slope (+1).**  Moving the zeta-side line from the gap (0,1) to the gap (N,N+1)
    picks up the Dirichlet partial sum:
        -lineUp c (rsG x^(-s)) = sum_{n=1}^{N} n^(-s) - lineUp c1 (rsG x^(-s)). -/
theorem lineUp_book (s : ℂ) (N : ℕ) {c c₁ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h₁ : (N : ℝ) < c₁) (h₁' : c₁ < N + 1) :
    -lineUp c (fun x => rsG x * x ^ (-s)) =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - lineUp c₁ (fun x => rsG x * x ^ (-s)) := by
  induction N generalizing c₁ with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, zero_sub]
    rw [lineUp_cpow_same_gap s (n := 0) (by simpa using hc) (by simpa using hc1)
      (by simpa using h₁) (by simpa using h₁')]
  | succ N ih =>
    have hN := ih (c₁ := (N : ℝ) + 1 / 2) (by linarith) (by linarith)
    have hc₁ : 0 < c₁ := lt_of_le_of_lt (by positivity) h₁
    have hcross := lineUp_cross (φ := fun x => x ^ (-s)) (n := (N : ℤ) + 1)
      (c₁ := (N : ℝ) + 1 / 2) (c₂ := c₁) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; push_cast at h₁; linarith) (by push_cast; push_cast at h₁'; linarith)
      (fun x hx => (differentiableAt_id).cpow (differentiableAt_const _)
        (slit_of_upStrip (by positivity) hx))
      (A := ((((N : ℝ) + 1 / 2) / 2) ^ (-s).re + 1) * Real.exp (π * |(-s).im|))
      (B := |(-s).re|) (fun x hx => norm_cpow_le_of_ge (by positivity)
        (norm_ge_of_upStrip hx (by positivity)))
    rw [hN, Finset.sum_Icc_succ_top (by omega), hcross]
    push_cast
    ring

/-- **Bookkeeping, slope (-1).**  Moving the chi-side line from the gap (0,1) to the gap (M,M+1):
        lineDn c (rsH x^(s-1)) = sum_{m=1}^{M} m^(s-1) + lineDn c2 (rsH x^(s-1)). -/
theorem lineDn_book (s : ℂ) (M : ℕ) {c c₂ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h₂ : (M : ℝ) < c₂) (h₂' : c₂ < M + 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) =
      (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (s - 1)) + lineDn c₂ (fun x => rsH x * x ^ (s - 1)) := by
  induction M generalizing c₂ with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, zero_add]
    exact lineDn_cpow_same_gap s (n := 0) (by simpa using hc) (by simpa using hc1)
      (by simpa using h₂) (by simpa using h₂')
  | succ M ih =>
    have hM := ih (c₂ := (M : ℝ) + 1 / 2) (by linarith) (by linarith)
    have hc₂ : 0 < c₂ := lt_of_le_of_lt (by positivity) h₂
    have hcross := lineDn_cross (ψ := fun x => x ^ (s - 1)) (n := (M : ℤ) + 1)
      (c₁ := (M : ℝ) + 1 / 2) (c₂ := c₂) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; push_cast at h₂; linarith) (by push_cast; push_cast at h₂'; linarith)
      (fun x hx => (differentiableAt_id).cpow (differentiableAt_const _)
        (slit_of_dnStrip (by positivity) hx))
      (A := ((((M : ℝ) + 1 / 2) / 2) ^ (s - 1).re + 1) * Real.exp (π * |(s - 1).im|))
      (B := |(s - 1).re|) (fun x hx => norm_cpow_le_of_ge (by positivity)
        (norm_ge_of_dnStrip hx (by positivity)))
    rw [hM, Finset.sum_Icc_succ_top (by omega)]
    rw [hcross]
    push_cast
    ring

/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/

/-- **Riemann's integral representation of `zeta(s)` (the exact Riemann-Siegel formula).**
    For every complex `s ∉ {1, 3, 5, ...}`, all `N M : ℕ` and all crossing points
    `c1 ∈ (N, N+1)`, `c2 ∈ (M, M+1)`:
        zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                  - lineUp c1 (rsG x^(-s)) + chi(s) lineDn c2 (rsH x^(s-1)). -/
theorem riemann_siegel_integral (s : ℂ) (hs : ∀ k : ℕ, s ≠ 2 * k + 1) (N M : ℕ) {c₁ c₂ : ℝ}
    (h₁ : (N : ℝ) < c₁) (h₁' : c₁ < N + 1) (h₂ : (M : ℝ) < c₂) (h₂' : c₂ < M + 1) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + rsChi s * (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (s - 1))
        - lineUp c₁ (fun x => rsG x * x ^ (-s))
        + rsChi s * lineDn c₂ (fun x => rsH x * x ^ (s - 1)) := by
  rw [rs_identity hs (c := 1 / 2) (by norm_num) (by norm_num),
    lineUp_book s N (c := 1 / 2) (by norm_num) (by norm_num) h₁ h₁',
    lineDn_book s M (c := 1 / 2) (by norm_num) (by norm_num) h₂ h₂']
  ring

/-! ## 6. The critical line -/

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    conj ((r : ℂ) ^ w) = (r : ℂ) ^ (conj w) := by
  have harg : (r : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (r : ℂ) (conj w) harg
  rw [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm

/-- On the critical line the chi-side remainder is the conjugate of the zeta-side one. -/
theorem lineDn_eq_conj_neg_lineUp {s : ℂ} (hs : s.re = 1 / 2) {c : ℝ} (hc : 0 < c) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) = conj (-lineUp c (fun x => rsG x * x ^ (-s))) := by
  have hneg : -lineUp c (fun x => rsG x * x ^ (-s)) =
      lineUp c (fun x => (-1) * (rsG x * x ^ (-s))) := by
    rw [lineUp_const_mul]; ring
  rw [lineDn_eq_conj, hneg]
  congr 1
  refine lineUp_congr fun v => ?_
  set x : ℂ := (c : ℂ) + v * (1 + I) with hx
  have harg : x.arg ≠ π := by
    have hslit := upLine_mem_slitPlane hc v
    exact (mem_slitPlane_iff_arg.mp hslit).1
  have hconjs : conj s - 1 = -s := by
    apply Complex.ext
    · simp [hs]; norm_num
    · simp
  rw [map_mul, conj_rsH_conj, Complex.conj_cpow _ _ harg, Complex.conj_conj, map_sub, map_one,
    hconjs]
  ring

theorem conj_natCast_cpow_crit {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    conj ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (s - 1) := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have := conj_ofReal_cpow hr (-s)
  push_cast at this
  rw [this]
  congr 1
  apply Complex.ext <;> simp [hs]
  linarith

theorem Gammaℝ_mul_rsChi {s : ℂ} (hs : 0 < s.re) : Gammaℝ s * rsChi s = Gammaℝ (1 - s) := by
  have hG : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  unfold rsChi
  rw [Gammaℝ_def, Gammaℝ_def]
  have hpi := pi_ne_zero'
  have hc : (↑π : ℂ) ^ (-s / 2) * (↑π : ℂ) ^ (s - 1 / 2) = (↑π : ℂ) ^ (-(1 - s) / 2) := by
    rw [← Complex.cpow_add _ _ hpi]; congr 1; ring
  rw [show (↑π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ((↑π : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) *
      (Gamma (s / 2))⁻¹) = ((↑π : ℂ) ^ (-s / 2) * (↑π : ℂ) ^ (s - 1 / 2)) * Gamma ((1 - s) / 2) *
      (Gamma (s / 2) * (Gamma (s / 2))⁻¹) by ring, hc, mul_inv_cancel₀ hG, mul_one]

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have e1 : conj (-s / 2) = -conj s / 2 := by rw [map_div₀, map_neg, map_ofNat]
  have e2 : conj (s / 2) = conj s / 2 := by rw [map_div₀, map_ofNat]
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, conj_ofReal_cpow Real.pi_pos, ← Complex.Gamma_conj, e1, e2]

/-- **The completed zeta on the critical line, exactly.**  For `s = 1/2 + i t` and `c ∈ (N, N+1)`:
        completedRiemannZeta s = 2 Re( Gammaℝ(s) (sum_{n<=N} n^(-s) - lineUp c (rsG x^(-s))) ). -/
theorem completedRiemannZeta_eq_rs (t : ℝ) (N : ℕ) {c : ℝ} (h : (N : ℝ) < c) (h' : c < N + 1) :
    completedRiemannZeta ((1 / 2 : ℂ) + t * I) =
      ((2 * (Gammaℝ ((1 / 2 : ℂ) + t * I) *
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) -
          lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))))).re : ℝ) : ℂ) := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hsdef
  have hsre : s.re = 1 / 2 := by simp [hsdef]
  have hc : 0 < c := lt_of_le_of_lt (Nat.cast_nonneg N) h
  have hodd : ∀ k : ℕ, s ≠ 2 * k + 1 := by
    intro k hk; have := congrArg Complex.re hk; simp [hsdef] at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hs0 : s ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp [hsdef] at this
  have hGne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hZ := riemann_siegel_integral s hodd N N h h' h h'
  have hcompl : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGne]
  set S := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) with hS
  set R := -lineUp c (fun x => rsG x * x ^ (-s)) with hR
  have hS' : ∑ m ∈ Finset.Icc 1 N, (m : ℂ) ^ (s - 1) = conj S := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [conj_natCast_cpow_crit hsre n (Finset.mem_Icc.mp hn).1]
  have hB : lineDn c (fun x => rsH x * x ^ (s - 1)) = conj R := lineDn_eq_conj_neg_lineUp hsre hc
  have hχ : Gammaℝ s * rsChi s = conj (Gammaℝ s) := by
    rw [Gammaℝ_mul_rsChi (by rw [hsre]; norm_num), ← Gammaℝ_conj]
    congr 1
    apply Complex.ext <;> simp [hsdef]; norm_num
  rw [hcompl, hZ, hS', hB]
  have : Gammaℝ s * (S + rsChi s * conj S - lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * conj R) = Gammaℝ s * (S + R) + conj (Gammaℝ s * (S + R)) := by
    rw [map_mul, map_add, ← hχ, hR]; ring
  rw [this, Complex.add_conj, hR, ← sub_eq_add_neg]

/-- **The Z-form.**  If `Gammaℝ(1/2 + i t) = M e^{i phi}` with `M > 0` (the polar form the island
    already proves, `ZeroSignDecomp.gamma_r_polar_t`), then for `c ∈ (N, N+1)`
        Re completedRiemannZeta(1/2 + i t)
          = 2 M ( sum_{n=1}^{N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} R) ),
    with `R = -lineUp c (rsG x^(-(1/2 + i t)))` the exact Riemann-Siegel remainder integral. -/
theorem completed_re_eq_rs_cos (t : ℝ) (N : ℕ) {c : ℝ} (h : (N : ℝ) < c) (h' : c < N + 1)
    {M φ : ℝ} (hpolar : Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ)) :
    (completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re =
      2 * M * ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n)) +
        (cexp (I * φ) * -lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))).re) := by
  rw [completedRiemannZeta_eq_rs t N h h', Complex.ofReal_re, hpolar]
  have hterm : ∀ n ∈ Finset.Icc 1 N, (cexp (I * φ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpow : (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(t * Real.log n) * I) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn1.ne'), ← Complex.ofReal_log hn1.le,
        Complex.ofReal_cpow hn1.le, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn1.ne'),
        ← Complex.ofReal_log hn1.le, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hpow, show cexp (I * φ) * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(t * Real.log n) * I)) = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (((φ - t * Real.log n : ℝ) : ℂ) * I) by
      rw [show (((φ - t * Real.log n : ℝ) : ℂ) * I) = I * φ + (-(t * Real.log n) * I) by
        push_cast; ring, Complex.exp_add]; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hsum : (cexp (I * φ) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re =
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) := by
    rw [Finset.mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl hterm
  have hM : ((M : ℂ) * cexp (I * φ) * ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) -
      lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))))).re =
      M * ((cexp (I * φ) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))).re +
        (cexp (I * φ) * -lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))).re) := by
    rw [mul_assoc, Complex.re_ofReal_mul, mul_sub, sub_eq_add_neg, ← mul_neg, Complex.add_re]
  rw [hM, hsum]; ring

end RSInt
