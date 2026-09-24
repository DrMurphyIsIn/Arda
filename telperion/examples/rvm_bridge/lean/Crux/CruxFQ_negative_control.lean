/-
CruxFQ_negative_control.lean -- crux-fq workflow, NEGATIVE-CONTROL seat (builder).
Fourier-quasicrystal-type properties of the Guinand-Weil pair, tested on the control zoo.

conjecture1_proved = False. Nothing here bears on where the zeros of `riemannZeta` lie, and nothing
here is a step toward RH: every theorem is about a control, a finite-rank model, or an equivalence
one side of which is RH itself.

Checked by: `cd telperion/examples/rvm_bridge/lean && leanlock.sh lake env lean
Crux/CruxFQ_negative_control.lean` (Lean v4.33.0-rc2, Mathlib 51e6992e, Zeta23 fbdc36bb).
No `sorry`, `admit`, `native_decide`, new `axiom`, or `opaque`. Every `#print axioms` line at the
end reports exactly `[propext, Classical.choice, Quot.sound]`. Zeta23 enters only through
`exists_nontrivial_zero_above` (its hypothesis-free Riemann--von Mangoldt formula).
Source-ported from `Crux/Crux_axiso_construct.lean` (round 1; Crux files are not libraries):
`IsLogDerivCoeff`, `logMul_eq_convolution`, `xiC` and its lemmas, `dvdInd`, `LSeries_dvdInd`,
`exists_nontrivial_zero_above`. Companion notes and numerics:
`telperion/research/crux_fq_negative-control/README.md`.

WHAT THIS FILE ESTABLISHES (THEOREM-kernel-checked):
 A. Dual weights `Λ_F` (the Guinand-Weil prime-side atoms) of `F = L a`: they EXIST for every
    bounded `a` with `a 1 = 1` (`exists_isLogDerivCoeff_of_bounded`, via Mathlib's Dirichlet
    inverse and the new growth bound `dirichletInverse_norm_le`), and the two-prime lemma
    `Λ_F(pq) = log(pq) (a(pq) - a(p) a(q))` (`LogConv.mul_primes`) holds: the dual has an atom at
    the non-prime-power frequency `log(pq)` iff `a` is not multiplicative at `(p, q)`.
 B. Davenport-Heilbronn (seat claim 1): its dual exists and EVERY representation has
    `Λ_D(2) = κ log 2`, `Λ_D(3) = -κ log 3 < 0`, `Λ_D(4) = -(2+κ²) log 2`,
    `Λ_D(6) = (1+κ²) log 6 ≠ 0`, with `6` not a prime power (`dh_dual_values`, `dh_dual_exists`).
 C. W2 (seat claim 8, CORRECTED): `1 + a(z+w) + zw` is Lee-Yang iff `|a| ≤ 1` (`LY2_leeYang_iff`;
    the seat wrote "iff a = 1"), and is an Euler factor iff `a² = 1` (`LY2_factor_iff`). Lee-Yang
    puts every zero of `E_a` on `Re s = 1/2` (`Ea_zero_re_of_leeYang`), multiplicative or not.
    `L(w2Coeff) = ζ E_a` (`W2_LSeries_eq`); the W2 dual has the atom `√(p₁p₂)(1-a²) log(p₁p₂)` at
    `p₁p₂` (`W2_dual_defect`, `W2_dual_exists`). The fooling instance `a = 1 + 10⁻⁴`,
    `(p₁, p₂) = (101, 10007)` is neither Lee-Yang nor Euler, and its atom there is NEGATIVE
    (`W2_fooling_instance`).
 D. Finite rank (seat claims 2 and 4): for `Q_c(s) = p^{s-1/2} + c + p^{1/2-s}` the conditions
    "all zeros on Re s = 1/2", "dual weights bounded (tempered)", and "roots of x² + cx + 1 on the
    unit circle (local Lee-Yang)" are each equivalent to `|c| ≤ 2`
    (`finite_rank_realZeros_iff_tempered_iff_leeYang`). The golden fake (`p = 5`, `c = √5`) has
    weights `(-1)^k (φ^k + φ^{-k})` (`golden_weights`, unbounded) and zeros exactly at
    `Re s = 1/2 ± log φ/log 5` (`golden_zero_re`), yet its full formal-curve dual is POSITIVE,
    `5^k + 1 - α^k - β^k > 0` (`golden_count_pos`). W1 (`p = 29`, `c = 11/√29`) fails all three
    (`W1_fails_finite_rank`).
 E. The imaginary-shift control `E_θ(s) = ζ(s+θ) ζ(s-θ)` (seat claim 3): the entire self-dual
    completion `ξ(s+θ)ξ(s-θ)` has gamma factor `Γ_ℝ(s+θ)Γ_ℝ(s-θ)` (`XiTheta_one_sub`,
    `XiTheta_eq_completion`); its dual `Λ(n)(n^θ + n^{-θ}) = 2cosh(θ log n) Λ(n)` is nonnegative,
    carried exactly by the prime powers, decays against `√n` for `|θ| < 1/2`, and represents
    `-E_θ'/E_θ` (`LambdaTheta_*`, `Etheta_logDeriv_hasSum`, `Etheta_isLogDerivCoeff`). It has zeros
    off `Re s = 1/2` above EVERY height, unconditionally (`Etheta_offline_zeros`; this discharges the
    `hzero` hypothesis of the corpus scratch `eisShift_violates_RH_analogue'`, see
    `eisShift_violates_RH_analogue_unconditional`); under RH it has NO zero on the line
    (`XiTheta_no_zero_on_line_of_RH`); and `RH ⟺ every zero lies on Re s = 1/2 ± θ`
    (`RH_iff_XiTheta_two_lines`). It fails the pole axiom: a genuine pole at `1 + θ`
    (`Etheta_pole`), to the right of every zero (`XiTheta_zero_re_bounds`). Capstone
    `Etheta_shift_control`.
 F. Finite-rank temperedness = real support (the mechanism of seat claim 2): with positive
    multiplicities, `x ↦ Σ m_j e^{i γ_j x}` is polynomially bounded on ℝ iff every `γ_j` is real
    (`dualSum_polyBounded_iff_real`); polynomial growth along `n ∈ ℕ` alone already forces
    `Im γ_j ≥ 0` (`im_nonneg_of_polyBounded_nat`). No positivity of a dual, no Euler product and no
    conductor enters.
 Capstone: `negative_control_capstone`.

WHAT THIS FILE DOES NOT ESTABLISH:
 - Anything about the zeros of `riemannZeta`, RH, or any wall clause.
 - Seat claim 2 in its class-C form (infinite zero sets, tempered distributions): it remains
   THEOREM-paper-proof (Laplace transform + identity theorem). Only the finite-rank form is here.
 - The functional equations of DH, W2 and Epstein (classical; numerics in the research directory),
   and any Guinand-Weil explicit formula for a control (numerics only; zeta's is E6Bridge4).
 - Off-line zeros of DH, Epstein, and W2 at `a = 1 + 10⁻⁴`: those are Arb-certified
   (`certify_offline_zeros.py`), not kernel. The kernel shows only that `LY2 (1 + 10⁻⁴)` is not
   Lee-Yang; the ACV step "not Lee-Yang ⟹ an off-line zero on the torus orbit" is not formalized.
 - Selberg's gamma-axiom failure of `E_θ` beyond the completion identity; the degree-2 Epstein
   segment of claim 5; Landau's theorem (claim 6); Bondarenko-Radchenko-Seip (claim 7).
-/
import Mathlib
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Zeta23.Assembly
import Zeta23.Statement.SeamClosed

open Complex LSeries Filter Topology MeasureTheory
open scoped LSeries.notation ComplexOrder Real

noncomputable section

namespace CruxFQNegControl

/-! ## A. Dirichlet-series toolkit (THEOREM-kernel-checked)

The first block is source-ported from `Crux/Crux_axiso_construct.lean` on this island (round 1,
constructor seat), because Crux files are not built as libraries. New here: the recursion-level
statements `LogConv.*` and the two-prime lemma `LogConv.mul_primes`. -/

/-- Along real `x → +∞`, `(x : EReal)` eventually exceeds any `e < ⊤`. -/
lemma eventually_coe_gt {e : EReal} (he : e < ⊤) : ∀ᶠ x : ℝ in atTop, e < (x : EReal) := by
  obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real he
  filter_upwards [eventually_gt_atTop r] with x hx
  exact hr.trans (by exact_mod_cast hx)

/-- `IsLogDerivCoeff F g`: the Dirichlet series `L g` has finite abscissa of absolute
convergence and represents `-F'/F` along the real ray to `+∞` (so `g = Λ_F`, the dual weights). -/
def IsLogDerivCoeff (F : ℂ → ℂ) (g : ℕ → ℂ) : Prop :=
  abscissaOfAbsConv g < ⊤ ∧ ∀ᶠ x : ℝ in atTop, -deriv F x / F x = LSeries g x

/-- **Uniqueness of `Λ_F`** (ported). If `F = L a`, `a 1 = 1`, and `L g = -F'/F` on a real ray,
then `log n · a n = (g ⍟ a) n` for all `n ≥ 1`. -/
theorem logMul_eq_convolution {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤) (ha1 : a 1 = 1)
    (hg : IsLogDerivCoeff (LSeries a) g) {n : ℕ} (hn : n ≠ 0) :
    logMul a n = (g ⍟ a) n := by
  obtain ⟨hgA, hgE⟩ := hg
  have hne : ∀ᶠ x : ℝ in atTop, LSeries a x ≠ 0 := by
    have h := LSeries.tendsto_atTop ha
    rw [ha1] at h
    exact h.eventually_ne one_ne_zero
  have key : ∀ᶠ x : ℝ in atTop, LSeries (logMul a) x = LSeries (g ⍟ a) x := by
    filter_upwards [hgE, hne, eventually_coe_gt ha, eventually_coe_gt hgA] with x hx hx0 hxa hxg
    have hxa' : abscissaOfAbsConv a < (x : ℂ).re := by simpa using hxa
    have hxg' : abscissaOfAbsConv g < (x : ℂ).re := by simpa using hxg
    have h1 : deriv (LSeries a) (x : ℂ) = -LSeries (logMul a) x := LSeries_deriv hxa'
    rw [h1, neg_neg] at hx
    rw [LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hxg')
      (LSeriesSummable_of_abscissaOfAbsConv_lt_re hxa'), ← hx, div_mul_cancel₀ _ hx0]
  have hA1 : abscissaOfAbsConv (logMul a) < ⊤ := by rwa [LSeries.abscissaOfAbsConv_logMul]
  have hA2 : abscissaOfAbsConv (g ⍟ a) < ⊤ :=
    (LSeries.abscissaOfAbsConv_convolution_le g a).trans_lt (max_lt hgA ha)
  exact LSeries.eq_of_LSeries_eventually_eq hA1 hA2 key hn

lemma convolution_one_apply (g a : ℕ → ℂ) : (g ⍟ a) 1 = g 1 * a 1 := by
  simp [LSeries.convolution_def]

lemma convolution_prime_pow (g a : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (g ⍟ a) (p ^ k) = ∑ j ∈ Finset.range (k + 1), g (p ^ j) * a (p ^ (k - j)) := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal (fun x y => g x * a y), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]

lemma log_natCast_pow (p k : ℕ) : Complex.log ((p : ℂ) ^ k) = (k : ℂ) * (Real.log p : ℂ) := by
  rw [← Nat.cast_pow, ← Complex.natCast_log, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

lemma logMul_prime_pow (a : ℕ → ℂ) (p k : ℕ) :
    logMul a (p ^ k) = ((k : ℂ) * (Real.log p : ℂ)) * a (p ^ k) := by
  simp only [LSeries.logMul]
  rw [Nat.cast_pow, log_natCast_pow]

/-! ### Existence of the dual weights (so the `IsLogDerivCoeff` hypotheses below are satisfiable)

For bounded coefficients with `a 1 = 1`, the Dirichlet inverse `b` of `a` (Mathlib's
`ArithmeticFunction.dirichletInverseFun`) grows at most polynomially, and `g := (a · log) ⍟ b`
represents `-L'(a)/L(a)`. -/

lemma sum_Icc_inv_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ e ∈ Finset.Icc 2 n, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1 - 1 / n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
      have h1 := ih hpos
      have hn' : (0 : ℝ) < n := by exact_mod_cast hpos
      have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / (n + 1) := by
        rw [div_sub_div _ _ hn'.ne' (by positivity), one_mul, mul_one]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

lemma properDivisors_div_facts {n d : ℕ} (hd : d ∈ n.properDivisors) :
    2 ≤ n / d ∧ n / d ≤ n ∧ d * (n / d) = n ∧ d ≠ 0 := by
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hn0 : n ≠ 0 := by omega
  have hd0 : d ≠ 0 := by rintro rfl; exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  refine ⟨?_, Nat.div_le_self n d, hmul, hd0⟩
  by_contra h
  have : n / d ≤ 1 := by omega
  have : n ≤ d := by
    calc n = d * (n / d) := hmul.symm
      _ ≤ d * 1 := Nat.mul_le_mul_left d this
      _ = d := mul_one d
  omega

/-- The key divisor-sum bound: `M Σ_{d ∣ n, d < n} d^{A+2} ≤ n^{A+2}` when `M ≤ 2^A`. -/
lemma properDivisors_pow_sum_le {M : ℝ} {A : ℕ} (hAM : M ≤ (2 : ℝ) ^ A) {n : ℕ} (hn : 1 ≤ n) :
    M * ∑ d ∈ n.properDivisors, (d : ℝ) ^ (A + 2) ≤ (n : ℝ) ^ (A + 2) := by
  have hterm : ∀ d ∈ n.properDivisors,
      M * (d : ℝ) ^ (A + 2) ≤ (n : ℝ) ^ (A + 2) * (1 / (((n / d : ℕ) : ℝ)) ^ 2) := by
    intro d hd
    obtain ⟨he2, -, hmul, -⟩ := properDivisors_div_facts hd
    set e := n / d with he
    have he2' : (2 : ℝ) ≤ e := by exact_mod_cast he2
    have hepos : (0 : ℝ) < e := by linarith
    have hn' : (n : ℝ) = d * e := by exact_mod_cast hmul.symm
    have hMe : M ≤ (e : ℝ) ^ A :=
      hAM.trans (pow_le_pow_left₀ (by norm_num) he2' A)
    rw [hn', mul_pow]
    have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ (A + 2) := by positivity
    have : (e : ℝ) ^ (A + 2) * (1 / (e : ℝ) ^ 2) = (e : ℝ) ^ A := by
      rw [pow_add]; field_simp
    calc M * (d : ℝ) ^ (A + 2) ≤ (e : ℝ) ^ A * (d : ℝ) ^ (A + 2) :=
          mul_le_mul_of_nonneg_right hMe hd0
      _ = (d : ℝ) ^ (A + 2) * ((e : ℝ) ^ (A + 2) * (1 / (e : ℝ) ^ 2)) := by rw [this]; ring
      _ = (d : ℝ) ^ (A + 2) * (e : ℝ) ^ (A + 2) * (1 / (e : ℝ) ^ 2) := by ring
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hinj : ∀ x ∈ n.properDivisors, ∀ y ∈ n.properDivisors, n / x = n / y → x = y := by
    intro x hx y hy hxy
    have hn0 : n ≠ 0 := by omega
    rw [← Nat.div_div_self (Nat.mem_properDivisors.mp hx).1 hn0,
      ← Nat.div_div_self (Nat.mem_properDivisors.mp hy).1 hn0, hxy]
  have himg : n.properDivisors.image (fun d => n / d) ⊆ Finset.Icc 2 n := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨h2, hle, -, -⟩ := properDivisors_div_facts hd
    exact Finset.mem_Icc.mpr ⟨h2, hle⟩
  have hsum : ∑ d ∈ n.properDivisors, (1 : ℝ) / (((n / d : ℕ) : ℝ)) ^ 2 ≤ 1 := by
    rw [← Finset.sum_image (f := fun e : ℕ => (1 : ℝ) / (e : ℝ) ^ 2) hinj]
    refine (Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity).trans ?_
    have := sum_Icc_inv_sq_le n hn
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hnA : (0 : ℝ) ≤ (n : ℝ) ^ (A + 2) := by positivity
  calc (n : ℝ) ^ (A + 2) * ∑ d ∈ n.properDivisors, (1 : ℝ) / (((n / d : ℕ) : ℝ)) ^ 2
      ≤ (n : ℝ) ^ (A + 2) * 1 := mul_le_mul_of_nonneg_left hsum hnA
    _ = (n : ℝ) ^ (A + 2) := mul_one _

/-- The Dirichlet inverse of a bounded sequence with `a 1 = 1` grows at most polynomially. -/
lemma dirichletInverse_norm_le {a : ℕ → ℂ} (hinv : Invertible (a 1)) (ha1 : a 1 = 1)
    {M : ℝ} (hM : ∀ n, n ≠ 0 → ‖a n‖ ≤ M) {A : ℕ} (hAM : M ≤ (2 : ℝ) ^ A) :
    ∀ n, n ≠ 0 → ‖ArithmeticFunction.dirichletInverseFun a hinv n‖ ≤ (n : ℝ) ^ (A + 2) := by
  have hone : (⅟(a 1) : ℂ) = 1 := invOf_eq_right_inv (by rw [ha1, one_mul])
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ArithmeticFunction.dirichletInverseFun_apply_one, hone]; simp
    · rw [ArithmeticFunction.dirichletInverseFun_apply_ne a hinv hn0 hn1, hone, neg_one_mul,
        norm_neg]
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_ne_zero)
      calc ‖∑ d ∈ n.properDivisors, a (n / d) * ArithmeticFunction.dirichletInverseFun a hinv d‖
          ≤ ∑ d ∈ n.properDivisors,
              ‖a (n / d) * ArithmeticFunction.dirichletInverseFun a hinv d‖ := norm_sum_le _ _
        _ ≤ ∑ d ∈ n.properDivisors, M * (d : ℝ) ^ (A + 2) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨he2, -, -, hd0⟩ := properDivisors_div_facts hd
          rw [norm_mul]
          have hdlt : d < n := (Nat.mem_properDivisors.mp hd).2
          exact mul_le_mul (hM _ (by omega)) (ih d hdlt hd0) (norm_nonneg _) hM0
        _ = M * ∑ d ∈ n.properDivisors, (d : ℝ) ^ (A + 2) := by rw [Finset.mul_sum]
        _ ≤ (n : ℝ) ^ (A + 2) := properDivisors_pow_sum_le hAM (by omega)

/-- **Existence of `Λ_F` (kernel).** Every Dirichlet series with `a 1 = 1` and bounded
coefficients has a log-derivative Dirichlet series: `∃ g, IsLogDerivCoeff (LSeries a) g`. -/
theorem exists_isLogDerivCoeff_of_bounded {a : ℕ → ℂ} (ha1 : a 1 = 1) {M : ℝ}
    (hM : ∀ n, n ≠ 0 → ‖a n‖ ≤ M) : ∃ g : ℕ → ℂ, IsLogDerivCoeff (LSeries a) g := by
  set F : ArithmeticFunction ℂ := toArithmeticFunction a with hFdef
  have hF1 : F 1 = 1 := by simp [hFdef, toArithmeticFunction, ha1]
  have hFM : ∀ n, n ≠ 0 → ‖F n‖ ≤ M := by
    intro n hn; simp only [hFdef, toArithmeticFunction, ArithmeticFunction.coe_mk, hn,
      if_false]; exact hM n hn
  have hinv : Invertible (F 1) := ⟨1, by rw [hF1, one_mul], by rw [hF1, one_mul]⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, M ≤ (2 : ℝ) ^ A := by
    obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
    exact ⟨A, hA.le⟩
  set b : ℕ → ℂ := ArithmeticFunction.dirichletInverseFun (⇑F) hinv with hb
  have hbnd := dirichletInverse_norm_le hinv hF1 hFM hA
  have haA : abscissaOfAbsConv a < ⊤ :=
    (LSeries.abscissaOfAbsConv_le_of_le_const ⟨M, hM⟩).trans_lt
      (by exact_mod_cast EReal.coe_lt_top 1)
  have hbA : abscissaOfAbsConv b < ⊤ := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := ((A + 2 : ℕ) : ℝ))
      ⟨1, fun n hn => ?_⟩).trans_lt (by exact_mod_cast EReal.coe_lt_top _)
    rw [one_mul, Real.rpow_natCast]
    exact hbnd n hn
  have hconv : a ⍟ b = LSeries.delta := by
    have hFb : toArithmeticFunction b = ArithmeticFunction.dirichletInverse (⇑F) hinv := by
      ext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [toArithmeticFunction]
      · simp [toArithmeticFunction, hn, hb]
    have key := ArithmeticFunction.self_mul_dirichletInverse F hinv
    funext n
    simp only [LSeries.convolution]
    rw [← hFdef, hFb, key, ArithmeticFunction.one_apply]
    simp [LSeries.delta]
  refine ⟨logMul a ⍟ b, ?_, ?_⟩
  · exact (LSeries.abscissaOfAbsConv_convolution_le _ _).trans_lt
      (max_lt (by rwa [LSeries.abscissaOfAbsConv_logMul]) hbA)
  · filter_upwards [eventually_coe_gt (max_lt haA hbA)] with x hx
    have hxa : abscissaOfAbsConv a < (x : ℂ).re := by
      simpa using (le_max_left _ _).trans_lt hx
    have hxb : abscissaOfAbsConv b < (x : ℂ).re := by
      simpa using (le_max_right _ _).trans_lt hx
    have hxl : abscissaOfAbsConv (logMul a) < (x : ℂ).re := by
      rwa [LSeries.abscissaOfAbsConv_logMul]
    have hprod : LSeries a x * LSeries b x = 1 := by
      rw [← LSeries_convolution hxa hxb, hconv, LSeries_delta]
      rfl
    have hne : LSeries a x ≠ 0 := left_ne_zero_of_mul_eq_one hprod
    rw [LSeries_convolution hxl hxb, LSeries_deriv hxa, neg_neg, div_eq_iff hne]
    linear_combination (-LSeries (logMul a) x) * hprod

/-- The divisors of a product of two distinct primes. -/
lemma divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -⟩
    obtain ⟨d1, d2, hd1, hd2, rfl⟩ := dvd_mul.mp hd
    rcases (Nat.dvd_prime hp).mp hd1 with rfl | rfl <;>
      rcases (Nat.dvd_prime hq).mp hd2 with rfl | rfl <;> simp
  · have h0 : p * q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨one_dvd _, h0⟩
    · exact ⟨dvd_mul_right _ _, h0⟩
    · exact ⟨dvd_mul_left _ _, h0⟩
    · exact ⟨dvd_refl _, h0⟩

/-- The Dirichlet convolution at a product of two distinct primes. -/
lemma convolution_mul_primes (g a : ℕ → ℂ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    (g ⍟ a) (p * q) = g 1 * a (p * q) + g p * a q + g q * a p + g (p * q) * a 1 := by
  rw [LSeries.convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal (fun x y => g x * a y), divisors_mul_primes hp hq]
  have hp1 : (1 : ℕ) < p := hp.one_lt
  have hq1 : (1 : ℕ) < q := hq.one_lt
  have hpq_p : p * q ≠ p := by
    intro h; have : p * q = p * 1 := by rw [h, mul_one]
    exact (Nat.ne_of_gt hq1) (Nat.eq_of_mul_eq_mul_left hp.pos this)
  have hpq_q : p * q ≠ q := by
    intro h; have : p * q = 1 * q := by rw [h, one_mul]
    exact (Nat.ne_of_gt hp1) (Nat.eq_of_mul_eq_mul_right hq.pos this)
  have hpq_1 : p * q ≠ 1 := by
    intro h; exact (Nat.ne_of_gt hp1) (Nat.eq_one_of_mul_eq_one_right h)
  rw [Finset.sum_insert (by simp [hp1.ne, hq1.ne, hpq_1.symm]),
    Finset.sum_insert (by simp [hpq, hpq_p.symm]),
    Finset.sum_insert (by simp [hpq_q.symm]), Finset.sum_singleton,
    Nat.div_one, Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel _ hq.pos,
    Nat.div_self (Nat.mul_pos hp.pos hq.pos)]
  ring

/-- The defining recursion `a · log = g ⍟ a` of the dual weights `g = Λ_F` of `F = L a`. -/
def LogConv (a g : ℕ → ℂ) : Prop := ∀ n : ℕ, n ≠ 0 → logMul a n = (g ⍟ a) n

theorem logConv_of_isLogDerivCoeff {a g : ℕ → ℂ} (ha : abscissaOfAbsConv a < ⊤)
    (ha1 : a 1 = 1) (hg : IsLogDerivCoeff (LSeries a) g) : LogConv a g :=
  fun _ hn => logMul_eq_convolution ha ha1 hg hn

theorem LogConv.one {a g : ℕ → ℂ} (ha1 : a 1 = 1) (h : LogConv a g) : g 1 = 0 := by
  have h1 := h 1 one_ne_zero
  rw [convolution_one_apply, ha1, mul_one] at h1
  rw [← h1]
  simp [LSeries.logMul]

theorem LogConv.prime {a g : ℕ → ℂ} (ha1 : a 1 = 1) (h : LogConv a g) {p : ℕ}
    (hp : p.Prime) : g p = (Real.log p : ℂ) * a p := by
  have hh := h (p ^ 1) (pow_ne_zero 1 hp.ne_zero)
  have h1 := h.one ha1
  rw [convolution_prime_pow g a hp 1, logMul_prime_pow] at hh
  simp [Finset.sum_range_succ, h1, ha1] at hh
  rw [Complex.natCast_log, ← hh]

/-- `Λ_F(p²) = log p · (2 a(p²) - a(p)²)`. -/
theorem LogConv.prime_sq {a g : ℕ → ℂ} (ha1 : a 1 = 1) (h : LogConv a g) {p : ℕ}
    (hp : p.Prime) : g (p ^ 2) = (Real.log p : ℂ) * (2 * a (p ^ 2) - a p ^ 2) := by
  have hh := h (p ^ 2) (pow_ne_zero 2 hp.ne_zero)
  have h1 := h.one ha1
  have hp1 := h.prime ha1 hp
  rw [convolution_prime_pow g a hp 2, logMul_prime_pow] at hh
  simp [Finset.sum_range_succ, h1, ha1, hp1] at hh
  rw [Complex.natCast_log]
  linear_combination -hh

/-- **The two-prime lemma.** For distinct primes `p ≠ q`,
`Λ_F(pq) = log(pq) · (a(pq) - a(p) a(q))`. So the dual has an atom at the non-prime-power
frequency `log(pq)` exactly when the coefficients fail to be multiplicative at `(p, q)`. -/
theorem LogConv.mul_primes {a g : ℕ → ℂ} (ha1 : a 1 = 1) (h : LogConv a g) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    g (p * q) = (Real.log (p * q : ℕ) : ℂ) * (a (p * q) - a p * a q) := by
  have hh := h (p * q) (mul_ne_zero hp.ne_zero hq.ne_zero)
  have h1 := h.one ha1
  have hgp := h.prime ha1 hp
  have hgq := h.prime ha1 hq
  rw [convolution_mul_primes g a hp hq hpq, h1, hgp, hgq, ha1] at hh
  simp only [LSeries.logMul] at hh
  have hlog : (Real.log (p * q : ℕ) : ℂ) = (Real.log p : ℂ) + (Real.log q : ℂ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hq.ne_zero)]
    push_cast; ring
  rw [← Complex.natCast_log] at hh
  rw [hlog]
  rw [hlog] at hh
  linear_combination -hh

/-- The dual atom at `log(pq)` vanishes iff the coefficients are multiplicative at `(p, q)`. -/
theorem LogConv.mul_primes_eq_zero_iff {a g : ℕ → ℂ} (ha1 : a 1 = 1) (h : LogConv a g)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    g (p * q) = 0 ↔ a (p * q) = a p * a q := by
  rw [h.mul_primes ha1 hp hq hpq]
  have hl : (Real.log (p * q : ℕ) : ℂ) ≠ 0 := by
    have : (1 : ℝ) < (p * q : ℕ) := by
      have := Nat.mul_le_mul hp.two_le hq.two_le
      exact_mod_cast (show 1 < p * q by omega)
    exact_mod_cast (Real.log_pos this).ne'
  rw [mul_eq_zero, sub_eq_zero]
  exact ⟨fun h' => h'.resolve_left hl, Or.inr⟩

/-- A product of two distinct primes is not a prime power. -/
theorem not_isPrimePow_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsPrimePow (p * q) := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨r, ⟨-, -⟩, hr⟩
  have e1 := hr p ⟨hp, dvd_mul_right p q⟩
  have e2 := hr q ⟨hq, dvd_mul_left q p⟩
  exact hpq (e1.trans e2.symm)

/-! ## B. Davenport-Heilbronn: the dual is signed and not carried by prime powers

`D(s) = Σ c(n) n^{-s}` with `c` periodic mod 5, `(c(1),...,c(5)) = (1, κ, -κ, -1, 0)`,
`κ = (√(10-2√5) - 2)/(√5 - 1)`. Its functional equation is classical and is NOT formalized here
(it was checked numerically in the seat's notes to `1.8e-29`). What is kernel-checked: EVERY
Dirichlet series `g` representing `-D'/D` has `g(2) = κ log 2`, `g(3) = -κ log 3 < 0`,
`g(4) = -(2+κ²) log 2`, and `g(6) = (1+κ²) log 6 ≠ 0` although `6` is not a prime power. -/

/-- Davenport-Heilbronn's `κ`. -/
def dhK : ℝ := (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

lemma sqrt5_gt_two : 2 < Real.sqrt 5 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [Real.sqrt_nonneg 5]

lemma dhK_pos : 0 < dhK := by
  have h5a := sqrt5_gt_two
  have h5b := sqrt5_lt_three
  have hu := Real.sq_sqrt (show (0 : ℝ) ≤ 10 - 2 * Real.sqrt 5 by linarith)
  have hu0 := Real.sqrt_nonneg (10 - 2 * Real.sqrt 5)
  have hnum : 2 < Real.sqrt (10 - 2 * Real.sqrt 5) := by nlinarith
  unfold dhK
  apply div_pos <;> linarith

lemma dhK_lt_one : dhK < 1 := by
  have h5a := sqrt5_gt_two
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hu := Real.sq_sqrt (show (0 : ℝ) ≤ 10 - 2 * Real.sqrt 5 by nlinarith)
  have hu0 := Real.sqrt_nonneg (10 - 2 * Real.sqrt 5)
  have hlt : Real.sqrt (10 - 2 * Real.sqrt 5) < Real.sqrt 5 + 1 := by nlinarith
  unfold dhK
  rw [div_lt_one (by linarith)]
  linarith

/-- The Davenport-Heilbronn coefficients, periodic mod 5. -/
def dhCoeff (n : ℕ) : ℂ :=
  if n % 5 = 1 then 1 else if n % 5 = 2 then (dhK : ℂ) else if n % 5 = 3 then -(dhK : ℂ)
  else if n % 5 = 4 then -1 else 0

lemma dhCoeff_one : dhCoeff 1 = 1 := by simp [dhCoeff]
lemma dhCoeff_two : dhCoeff 2 = dhK := by simp [dhCoeff]
lemma dhCoeff_three : dhCoeff 3 = -dhK := by simp [dhCoeff]
lemma dhCoeff_four : dhCoeff 4 = -1 := by simp [dhCoeff]
lemma dhCoeff_six : dhCoeff 6 = 1 := by simp [dhCoeff]

lemma dhCoeff_norm_le (n : ℕ) : ‖dhCoeff n‖ ≤ 1 := by
  have hk : |dhK| ≤ 1 := by rw [abs_of_pos dhK_pos]; exact dhK_lt_one.le
  unfold dhCoeff
  split_ifs <;> simp [hk]

lemma dhCoeff_abscissa : abscissaOfAbsConv dhCoeff < ⊤ :=
  (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => dhCoeff_norm_le n⟩).trans_lt
    (by exact_mod_cast EReal.coe_lt_top 1)

/-- **Davenport-Heilbronn's dual weights (kernel).** Every Dirichlet series `g` representing
`-D'/D` has these values. -/
theorem dh_dual_values {g : ℕ → ℂ} (hg : IsLogDerivCoeff (LSeries dhCoeff) g) :
    g 2 = ((dhK * Real.log 2 : ℝ) : ℂ) ∧ g 3 = ((-(dhK * Real.log 3) : ℝ) : ℂ) ∧
    g 4 = ((-((2 + dhK ^ 2) * Real.log 2) : ℝ) : ℂ) ∧
    g 6 = (((1 + dhK ^ 2) * Real.log 6 : ℝ) : ℂ) := by
  have hc := logConv_of_isLogDerivCoeff dhCoeff_abscissa dhCoeff_one hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.prime dhCoeff_one Nat.prime_two, dhCoeff_two]; push_cast; ring
  · rw [hc.prime dhCoeff_one Nat.prime_three, dhCoeff_three]; push_cast; ring
  · have h4 := hc.prime_sq dhCoeff_one Nat.prime_two
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, dhCoeff_four, dhCoeff_two] at h4
    rw [h4]; push_cast; ring
  · have h6 := hc.mul_primes dhCoeff_one Nat.prime_two Nat.prime_three (by norm_num)
    rw [show (2 : ℕ) * 3 = 6 by norm_num, dhCoeff_six, dhCoeff_two, dhCoeff_three] at h6
    rw [h6]; push_cast; ring

/-- The DH dual is SIGNED: the atom at `log 3` is a negative real. -/
theorem dh_dual_negative_atom {g : ℕ → ℂ} (hg : IsLogDerivCoeff (LSeries dhCoeff) g) :
    (g 3).im = 0 ∧ (g 3).re < 0 := by
  rw [(dh_dual_values hg).2.1]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  nlinarith [dhK_pos]

/-- The DH dual is NOT carried by prime powers: `g 6 ≠ 0` and `6` is not a prime power. -/
theorem dh_dual_off_prime_powers {g : ℕ → ℂ} (hg : IsLogDerivCoeff (LSeries dhCoeff) g) :
    g 6 ≠ 0 ∧ ¬ IsPrimePow 6 := by
  refine ⟨?_, ?_⟩
  · rw [(dh_dual_values hg).2.2.2]
    have h6 := Real.log_pos (show (1 : ℝ) < 6 by norm_num)
    have : (0 : ℝ) < (1 + dhK ^ 2) * Real.log 6 := by positivity
    exact_mod_cast this.ne'
  · exact not_isPrimePow_mul_primes (p := 2) (q := 3) Nat.prime_two Nat.prime_three (by norm_num)

/-- **DH's dual exists and is signed and off prime powers (kernel, non-vacuous form).** -/
theorem dh_dual_exists : ∃ g : ℕ → ℂ, IsLogDerivCoeff (LSeries dhCoeff) g ∧
    g 6 = (((1 + dhK ^ 2) * Real.log 6 : ℝ) : ℂ) ∧ g 6 ≠ 0 ∧ ¬ IsPrimePow 6 ∧
    (g 3).im = 0 ∧ (g 3).re < 0 := by
  obtain ⟨g, hg⟩ := exists_isLogDerivCoeff_of_bounded dhCoeff_one (fun n _ => dhCoeff_norm_le n)
  exact ⟨g, hg, (dh_dual_values hg).2.2.2, (dh_dual_off_prime_powers hg).1,
    (dh_dual_off_prime_powers hg).2, (dh_dual_negative_atom hg).1, (dh_dual_negative_atom hg).2⟩

/-! ## C. The fooling-lemma control W2: Lee-Yang is `|a| ≤ 1`, Euler is `a² = 1`

W2 `= ζ(s) E_a(s)`, `E_a(s) = 1 + a (p₁^{1/2-s} + p₂^{1/2-s}) + (p₁p₂)^{1/2-s}`, is the restriction
of the multi-affine polynomial `LY2 a z w = 1 + a(z + w) + z w` to the torus orbit
`(z, w) = (p₁^{1/2-s}, p₂^{1/2-s})`. CORRECTION to the seat's claim 8 ("Lee-Yang iff `a = 1`"):
for real `a` the polynomial is Lee-Yang iff `|a| ≤ 1` (`LY2_leeYang_iff`), while it factors as an
Euler factor `(1 + u z)(1 + v w)` iff `a² = 1` (`LY2_factor_iff`). For `|a| < 1` it is Lee-Yang,
so `E_a` has all its zeros on `Re s = 1/2` (`Ea_zero_re_of_leeYang`), yet it is not
multiplicative (`W2_dual_defect`). The fooling parameter `a = 1 + 10⁻⁴` fails both. -/

/-- The two-variable multi-affine symmetric polynomial of W2's finite factor. -/
def LY2 (a : ℝ) (z w : ℂ) : ℂ := 1 + a * (z + w) + z * w

/-- The Lee-Yang property (Alon-Cohen-Vinzant, Kurasov-Sarnak): no zero with both variables in
the open unit disc, and none with both outside the closed unit disc. -/
def IsLeeYang2 (P : ℂ → ℂ → ℂ) : Prop :=
  (∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → P z w ≠ 0) ∧ (∀ z w : ℂ, 1 < ‖z‖ → 1 < ‖w‖ → P z w ≠ 0)

lemma normSq_one_add_mul_sub (a : ℝ) (z : ℂ) :
    Complex.normSq (1 + a * z) - Complex.normSq (a + z) =
      (1 - a ^ 2) * (1 - Complex.normSq z) := by
  simp [Complex.normSq_apply]; ring

lemma LY2_ne_zero_of_lt_one {a : ℝ} (ha : |a| ≤ 1) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    LY2 a z w ≠ 0 := by
  intro h
  have hkey : w * (a + z) = -(1 + a * z) := by unfold LY2 at h; linear_combination h
  have hns : Complex.normSq w * Complex.normSq (a + z) = Complex.normSq (1 + a * z) := by
    rw [← Complex.normSq_mul, hkey, Complex.normSq_neg]
  have hid := normSq_one_add_mul_sub a z
  have hz2 : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hw2 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.mp ha; nlinarith
  have hA := Complex.normSq_nonneg (a + z)
  have hE : 0 ≤ (1 - a ^ 2) * (1 - Complex.normSq z) :=
    mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hz2.le)
  have hprod : Complex.normSq (a + z) * (1 - Complex.normSq w) ≤ 0 := by nlinarith
  have hA0 : Complex.normSq (a + z) = 0 := by
    refine le_antisymm ?_ hA
    by_contra hc
    have := mul_pos (not_le.mp hc) (sub_pos.mpr hw2)
    linarith
  have h1 : (1 - a ^ 2) * (1 - Complex.normSq z) = 0 := by
    rw [← hid, ← hns, hA0]; ring
  have ha2' : a ^ 2 = 1 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · linarith
    · linarith
  have hz' : z = -(a : ℂ) := by
    have := Complex.normSq_eq_zero.mp hA0; linear_combination this
  rw [hz', Complex.normSq_neg, Complex.normSq_ofReal] at hz2
  nlinarith

lemma LY2_inv (a : ℝ) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    LY2 a z w = z * w * LY2 a z⁻¹ w⁻¹ := by
  unfold LY2; field_simp; ring

theorem LY2_leeYang_of_abs_le_one {a : ℝ} (ha : |a| ≤ 1) : IsLeeYang2 (LY2 a) := by
  refine ⟨fun z w hz hw => LY2_ne_zero_of_lt_one ha hz hw, fun z w hz hw => ?_⟩
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
  rw [LY2_inv a hz0 hw0]
  refine mul_ne_zero (mul_ne_zero hz0 hw0) (LY2_ne_zero_of_lt_one ha ?_ ?_)
  · rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz
  · rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw

theorem LY2_not_leeYang {a : ℝ} (ha : 1 < |a|) : ¬ IsLeeYang2 (LY2 a) := by
  rintro ⟨hin, -⟩
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℝ, |r| < 1 ∧ 1 + 2 * a * r + r ^ 2 = 0 := by
    have hS := Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 1 by nlinarith [sq_abs a])
    have hS0 := Real.sqrt_nonneg (a ^ 2 - 1)
    rcases lt_abs.mp ha with h | h
    · refine ⟨-a + Real.sqrt (a ^ 2 - 1), ?_, by nlinarith⟩
      rw [abs_lt]; constructor <;> nlinarith
    · refine ⟨-a - Real.sqrt (a ^ 2 - 1), ?_, by nlinarith⟩
      rw [abs_lt]; constructor <;> nlinarith
  have hrn : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  apply hin r r hrn hrn
  unfold LY2
  have : ((1 + 2 * a * r + r ^ 2 : ℝ) : ℂ) = 0 := by rw [hr]; simp
  push_cast at this
  linear_combination this

/-- **Lee-Yang for W2's factor (kernel).** For real `a`: Lee-Yang iff `|a| ≤ 1`. -/
theorem LY2_leeYang_iff (a : ℝ) : IsLeeYang2 (LY2 a) ↔ |a| ≤ 1 :=
  ⟨fun h => not_lt.mp fun ha => LY2_not_leeYang ha h, LY2_leeYang_of_abs_le_one⟩

/-- **Euler factorization of W2's factor (kernel).** `LY2 a` splits as `(1 + u z)(1 + v w)` iff
`a² = 1`. -/
theorem LY2_factor_iff (a : ℝ) :
    (∃ u v : ℂ, ∀ z w : ℂ, LY2 a z w = (1 + u * z) * (1 + v * w)) ↔ a ^ 2 = 1 := by
  constructor
  · rintro ⟨u, v, h⟩
    have h1 := h 1 0
    have h2 := h 0 1
    have h3 := h 1 1
    simp only [LY2] at h1 h2 h3
    have hu : u = (a : ℂ) := by linear_combination -h1
    have hv : v = (a : ℂ) := by linear_combination -h2
    rw [hu, hv] at h3
    have : ((a ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination -h3
    exact_mod_cast this
  · intro ha
    have hfac : (a - 1) * (a + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp hfac with h | h
    · have : a = 1 := by linarith
      subst this
      exact ⟨1, 1, fun z w => by unfold LY2; push_cast; ring⟩
    · have : a = -1 := by linarith
      subst this
      exact ⟨-1, -1, fun z w => by unfold LY2; push_cast; ring⟩

/-- W2's finite factor on the torus orbit: `E_a(s) = LY2 a (p₁^{1/2-s}) (p₂^{1/2-s})`. -/
def Ea (a p1 p2 : ℝ) (s : ℂ) : ℂ :=
  LY2 a ((p1 : ℂ) ^ ((1 : ℂ) / 2 - s)) ((p2 : ℂ) ^ ((1 : ℂ) / 2 - s))

lemma norm_cpow_half_sub {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ ((1 : ℂ) / 2 - s)‖ = p ^ ((1 : ℝ) / 2 - s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  congr 1
  simp

/-- **Finite-rank Lee-Yang ⟹ real zeros (kernel; the easy direction of ACV).** If `|a| ≤ 1` then
every zero of `E_a` lies on `Re s = 1/2`, although `E_a` is not multiplicative for `a² ≠ 1`. -/
theorem Ea_zero_re_of_leeYang {a p1 p2 : ℝ} (ha : |a| ≤ 1) (hp1 : 1 < p1) (hp2 : 1 < p2)
    {s : ℂ} (h : Ea a p1 p2 s = 0) : s.re = 1 / 2 := by
  obtain ⟨hin, hout⟩ := LY2_leeYang_of_abs_le_one ha
  rcases lt_trichotomy s.re (1 / 2) with hs | hs | hs
  · exfalso
    refine hout _ _ ?_ ?_ h
    · rw [norm_cpow_half_sub (by linarith)]; exact Real.one_lt_rpow hp1 (by linarith)
    · rw [norm_cpow_half_sub (by linarith)]; exact Real.one_lt_rpow hp2 (by linarith)
  · exact hs
  · exfalso
    refine hin _ _ ?_ ?_ h
    · rw [norm_cpow_half_sub (by linarith)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    · rw [norm_cpow_half_sub (by linarith)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp2 (by linarith)

/-- The Dirichlet coefficients of `W2 = ζ(s) E_a(s)` for two primes `p₁ ≠ p₂`:
`c(n) = 1 + a√p₁ [p₁ ∣ n] + a√p₂ [p₂ ∣ n] + √(p₁p₂) [p₁p₂ ∣ n]`. -/
def w2Coeff (a : ℝ) (p1 p2 : ℕ) (n : ℕ) : ℂ :=
  1 + (if p1 ∣ n then ((a * Real.sqrt p1 : ℝ) : ℂ) else 0)
    + (if p2 ∣ n then ((a * Real.sqrt p2 : ℝ) : ℂ) else 0)
    + (if p1 * p2 ∣ n then ((Real.sqrt (p1 * p2 : ℕ) : ℝ) : ℂ) else 0)

lemma w2Coeff_norm_le (a : ℝ) (p1 p2 n : ℕ) :
    ‖w2Coeff a p1 p2 n‖ ≤ 1 + |a * Real.sqrt p1| + |a * Real.sqrt p2| + Real.sqrt (p1 * p2 : ℕ) := by
  unfold w2Coeff
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (by simp) ?_)) ?_)) ?_
  · split_ifs
    · simp
    · simp only [norm_zero]; positivity
  · split_ifs
    · simp
    · simp only [norm_zero]; positivity
  · split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    · simp only [norm_zero]; positivity

lemma w2Coeff_abscissa (a : ℝ) (p1 p2 : ℕ) : abscissaOfAbsConv (w2Coeff a p1 p2) < ⊤ :=
  (LSeries.abscissaOfAbsConv_le_of_le_const ⟨_, fun n _ => w2Coeff_norm_le a p1 p2 n⟩).trans_lt
    (by exact_mod_cast EReal.coe_lt_top 1)

lemma w2Coeff_values {a : ℝ} {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime) (h12 : p1 ≠ p2) :
    w2Coeff a p1 p2 1 = 1 ∧ w2Coeff a p1 p2 p1 = 1 + ((a * Real.sqrt p1 : ℝ) : ℂ) ∧
    w2Coeff a p1 p2 p2 = 1 + ((a * Real.sqrt p2 : ℝ) : ℂ) ∧
    w2Coeff a p1 p2 (p1 * p2) = 1 + ((a * Real.sqrt p1 : ℝ) : ℂ) + ((a * Real.sqrt p2 : ℝ) : ℂ)
      + ((Real.sqrt (p1 * p2 : ℕ) : ℝ) : ℂ) := by
  have n1 : ¬ p1 ∣ 1 := Nat.Prime.not_dvd_one hp1
  have n2 : ¬ p2 ∣ 1 := Nat.Prime.not_dvd_one hp2
  have n12 : ¬ p1 * p2 ∣ 1 := fun h => n1 (dvd_trans (dvd_mul_right p1 p2) h)
  have d21 : ¬ p2 ∣ p1 := fun h => h12 ((Nat.prime_dvd_prime_iff_eq hp2 hp1).mp h).symm
  have d12 : ¬ p1 ∣ p2 := fun h => h12 ((Nat.prime_dvd_prime_iff_eq hp1 hp2).mp h)
  have e1 : ¬ p1 * p2 ∣ p1 := by
    intro h
    have : p1 * p2 ∣ p1 * 1 := by rwa [mul_one]
    exact n2 (Nat.dvd_of_mul_dvd_mul_left hp1.pos this)
  have e2 : ¬ p1 * p2 ∣ p2 := by
    intro h
    have : p2 * p1 ∣ p2 * 1 := by rwa [mul_one, mul_comm]
    exact n1 (Nat.dvd_of_mul_dvd_mul_left hp2.pos this)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [w2Coeff, n1, n2, n12]
  · simp [w2Coeff, d21, e1]
  · simp [w2Coeff, d12, e2]
  · simp [w2Coeff, dvd_mul_right, dvd_mul_left]

/-! ### `L(w2Coeff) = ζ · E_a` (so `w2Coeff` really is the coefficient sequence of W2) -/

/-- The indicator of the multiples of `m` (ported from `Crux_axiso_construct.lean`). -/
def dvdInd (m : ℕ) (n : ℕ) : ℂ := if m ∣ n then 1 else 0

lemma LSeriesSummable_of_bounded {f : ℕ → ℂ} (C : ℝ) (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((LSeries.abscissaOfAbsConv_le_of_le_const ⟨C, hf⟩).trans_lt (by exact_mod_cast hs))

lemma LSeries_dvdInd {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (dvdInd m) s = (m : ℂ) ^ (-s) * riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  unfold LSeries
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun k : ℕ => m * k) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  have hsupp : Function.support (term (dvdInd m) s) ⊆ Set.range (fun k : ℕ => m * k) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hdvd : m ∣ n
    · obtain ⟨k, rfl⟩ := hdvd
      exact ⟨k, rfl⟩
    · exfalso; apply hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [term_of_ne_zero hn0]; simp [dvdInd, hdvd]
  rw [← hinj.tsum_eq hsupp]
  congr 1
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [term_of_ne_zero (mul_ne_zero hm hk), term_of_ne_zero hk]
    simp only [dvdInd, dvd_mul_right, if_true, Pi.one_apply, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow, cpow_neg]
    have h1 : (m : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hm (by exact_mod_cast h.1)
    have h2 : (k : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => hk (by exact_mod_cast h.1)
    field_simp

lemma sqrt_mul_cpow_neg {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    ((Real.sqrt p : ℝ) : ℂ) * (p : ℂ) ^ (-s) = (p : ℂ) ^ ((1 : ℂ) / 2 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg p), Complex.ofReal_natCast,
    ← cpow_add _ _ hp0]
  congr 1
  push_cast
  ring

/-- **W2 is the Dirichlet series of `w2Coeff` (kernel).** For `Re s > 1`,
`L(w2Coeff a p₁ p₂)(s) = ζ(s) E_a(s)`. -/
theorem W2_LSeries_eq (a : ℝ) {p1 p2 : ℕ} (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (w2Coeff a p1 p2) s = riemannZeta s * Ea a p1 p2 s := by
  set A1 : ℂ := ((a * Real.sqrt p1 : ℝ) : ℂ)
  set A2 : ℂ := ((a * Real.sqrt p2 : ℝ) : ℂ)
  set A12 : ℂ := ((Real.sqrt (p1 * p2 : ℕ) : ℝ) : ℂ)
  have hfun : w2Coeff a p1 p2 =
      ((1 : ℕ → ℂ) + A1 • dvdInd p1) + A2 • dvdInd p2 + A12 • dvdInd (p1 * p2) := by
    funext n
    simp only [w2Coeff, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, dvdInd, A1, A2,
      A12]
    split_ifs <;> ring
  have hb : ∀ m : ℕ, ∀ n, n ≠ 0 → ‖dvdInd m n‖ ≤ 1 := by
    intro m n _; unfold dvdInd; split_ifs <;> simp
  have s1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_of_bounded 1 (fun n _ => by simp) hs
  have sd : ∀ m : ℕ, LSeriesSummable (dvdInd m) s := fun m => LSeriesSummable_of_bounded 1 (hb m) hs
  have hp12 : p1 * p2 ≠ 0 := mul_ne_zero hp1 hp2
  rw [hfun, LSeries_add ((s1.add ((sd p1).smul A1)).add ((sd p2).smul A2)) ((sd _).smul A12),
    LSeries_add (s1.add ((sd p1).smul A1)) ((sd p2).smul A2), LSeries_add s1 ((sd p1).smul A1),
    LSeries_smul, LSeries_smul, LSeries_smul, LSeries_one_eq_riemannZeta hs,
    LSeries_dvdInd hp1 hs, LSeries_dvdInd hp2 hs, LSeries_dvdInd hp12 hs]
  have e1 : A1 * (p1 : ℂ) ^ (-s) = (a : ℂ) * (p1 : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    simp only [A1, Complex.ofReal_mul]; rw [mul_assoc, sqrt_mul_cpow_neg hp1]
  have e2 : A2 * (p2 : ℂ) ^ (-s) = (a : ℂ) * (p2 : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    simp only [A2, Complex.ofReal_mul]; rw [mul_assoc, sqrt_mul_cpow_neg hp2]
  have e12 : A12 * ((p1 * p2 : ℕ) : ℂ) ^ (-s) =
      (p1 : ℂ) ^ ((1 : ℂ) / 2 - s) * (p2 : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    simp only [A12]
    rw [sqrt_mul_cpow_neg hp12, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  unfold Ea LY2
  simp only [Complex.ofReal_natCast]
  linear_combination riemannZeta s * e1 + riemannZeta s * e2 + riemannZeta s * e12

/-- **W2's dual is not carried by prime powers (kernel).** Every Dirichlet series `g` representing
`-W2'/W2` has, at the non-prime-power `p₁p₂`, the atom `√(p₁p₂) (1 - a²) log(p₁p₂)`. -/
theorem W2_dual_defect {a : ℝ} {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime) (h12 : p1 ≠ p2)
    {g : ℕ → ℂ} (hg : IsLogDerivCoeff (LSeries (w2Coeff a p1 p2)) g) :
    g (p1 * p2) =
      ((Real.sqrt (p1 * p2 : ℕ) * (1 - a ^ 2) * Real.log (p1 * p2 : ℕ) : ℝ) : ℂ) := by
  obtain ⟨v1, vp1, vp2, v12⟩ := w2Coeff_values (a := a) hp1 hp2 h12
  have hc := logConv_of_isLogDerivCoeff (w2Coeff_abscissa a p1 p2) v1 hg
  rw [hc.mul_primes v1 hp1 hp2 h12, v12, vp1, vp2]
  have hsq : Real.sqrt (p1 * p2 : ℕ) = Real.sqrt p1 * Real.sqrt p2 := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [hsq]
  push_cast
  ring

/-- The W2 dual atom at `log(p₁p₂)` vanishes iff `a² = 1` (iff `LY2 a` is an Euler factor). -/
theorem W2_dual_defect_eq_zero_iff {a : ℝ} {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h12 : p1 ≠ p2) {g : ℕ → ℂ} (hg : IsLogDerivCoeff (LSeries (w2Coeff a p1 p2)) g) :
    g (p1 * p2) = 0 ↔ a ^ 2 = 1 := by
  rw [W2_dual_defect hp1 hp2 h12 hg]
  have hs : 0 < Real.sqrt (p1 * p2 : ℕ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos hp1.pos hp2.pos)
  have hl : 0 < Real.log (p1 * p2 : ℕ) := by
    apply Real.log_pos
    have := Nat.mul_le_mul hp1.two_le hp2.two_le
    exact_mod_cast (show 1 < p1 * p2 by omega)
  constructor
  · intro h
    have h' : Real.sqrt (p1 * p2 : ℕ) * (1 - a ^ 2) * Real.log (p1 * p2 : ℕ) = 0 := by
      exact_mod_cast h
    rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · linarith
      · linarith
    · linarith
  · intro h
    have : (1 - a ^ 2) = 0 := by linarith
    rw [this]; simp

/-- **The fooling instance (kernel).** `a = 1 + 10⁻⁴`, `p₁ = 101`, `p₂ = 10007`: the factor is not
Lee-Yang, not an Euler factor, and every representation of `-W2'/W2` has a NEGATIVE atom at the
non-prime-power `101·10007`. -/
theorem W2_fooling_instance {g : ℕ → ℂ}
    (hg : IsLogDerivCoeff (LSeries (w2Coeff (1 + 1 / 10000) 101 10007)) g) :
    ¬ IsLeeYang2 (LY2 (1 + 1 / 10000)) ∧ (1 + 1 / 10000 : ℝ) ^ 2 ≠ 1 ∧
    (g (101 * 10007)).im = 0 ∧ (g (101 * 10007)).re < 0 ∧ ¬ IsPrimePow (101 * 10007) := by
  have hp1 : Nat.Prime 101 := by norm_num
  have hp2 : Nat.Prime 10007 := by norm_num
  have ha : 1 < |(1 + 1 / 10000 : ℝ)| := by rw [abs_of_pos (by norm_num)]; norm_num
  refine ⟨LY2_not_leeYang ha, by norm_num, ?_, ?_,
    not_isPrimePow_mul_primes hp1 hp2 (by norm_num)⟩
  · rw [W2_dual_defect hp1 hp2 (by norm_num) hg]; exact Complex.ofReal_im _
  · rw [W2_dual_defect hp1 hp2 (by norm_num) hg, Complex.ofReal_re]
    have hs : 0 < Real.sqrt (101 * 10007 : ℕ) := Real.sqrt_pos.mpr (by norm_num)
    have hl : 0 < Real.log (101 * 10007 : ℕ) := Real.log_pos (by norm_num)
    have hneg : (1 - (1 + 1 / 10000 : ℝ) ^ 2) < 0 := by norm_num
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hneg) hl

/-- **W2's dual exists and has the defect atom (kernel, non-vacuous form).** -/
theorem W2_dual_exists (a : ℝ) {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime) (h12 : p1 ≠ p2) :
    ∃ g : ℕ → ℂ, IsLogDerivCoeff (LSeries (w2Coeff a p1 p2)) g ∧
      g (p1 * p2) =
        ((Real.sqrt (p1 * p2 : ℕ) * (1 - a ^ 2) * Real.log (p1 * p2 : ℕ) : ℝ) : ℂ) := by
  obtain ⟨g, hg⟩ := exists_isLogDerivCoeff_of_bounded (w2Coeff_values (a := a) hp1 hp2 h12).1
    (fun n _ => w2Coeff_norm_le a p1 p2 n)
  exact ⟨g, hg, W2_dual_defect hp1 hp2 h12 hg⟩

/-! ## D. Finite rank: tempered dual = local Lee-Yang = zeros on the line (one-prime factor)

The one-prime completed factor `Q_c(s) = p^{s-1/2} + c + p^{1/2-s}` (`c` real) has Euler form
`1 + c Y + Y²`, `Y = p^{1/2-s}`, and its dual weights at `k log p` are `-(log p) · qw c k`,
`qw c k = λ₁^k + λ₂^k` over the roots of `x² + c x + 1`. Kernel: the three conditions
(a) every zero on `Re s = 1/2`, (b) bounded (tempered) dual weights, (c) both roots on the unit
circle (local Lee-Yang / unitary Satake), are each equivalent to `|c| ≤ 2`. Round 1's golden fake
is `p = 5, c = √5` and W1 is `p = 29, c = 11/√29`: both fail all three at once. -/

/-- Normalized dual weights of the one-prime factor: `qw c k = λ₁^k + λ₂^k`,
`λ₁ + λ₂ = -c`, `λ₁ λ₂ = 1` (Newton recursion). -/
def qw (c : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => -c
  | (k + 2) => -c * qw c (k + 1) - qw c k

lemma qw_zero (c : ℝ) : qw c 0 = 2 := rfl
lemma qw_one (c : ℝ) : qw c 1 = -c := rfl
lemma qw_succ_succ (c : ℝ) (k : ℕ) : qw c (k + 2) = -c * qw c (k + 1) - qw c k := rfl

theorem qw_cos (θ : ℝ) : ∀ k : ℕ, qw (-2 * Real.cos θ) k = 2 * Real.cos (k * θ)
  | 0 => by simp [qw_zero]
  | 1 => by simp [qw_one]
  | (k + 2) => by
    rw [qw_succ_succ, qw_cos θ (k + 1), qw_cos θ k]
    have e1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e0 : (k : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e1, e0, Real.cos_add, Real.cos_sub]
    ring

theorem qw_neg (c : ℝ) : ∀ k : ℕ, qw (-c) k = (-1) ^ k * qw c k
  | 0 => by simp [qw_zero]
  | 1 => by simp [qw_one]
  | (k + 2) => by
    rw [qw_succ_succ, qw_succ_succ, qw_neg c (k + 1), qw_neg c k]
    ring

theorem qw_hyp {r : ℝ} (hr : r ≠ 0) : ∀ k : ℕ, qw (-(r + r⁻¹)) k = r ^ k + r⁻¹ ^ k
  | 0 => by rw [qw_zero]; norm_num
  | 1 => by rw [qw_one]; ring
  | (k + 2) => by
    rw [qw_succ_succ, qw_hyp hr (k + 1), qw_hyp hr k]
    have hu : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    linear_combination (r⁻¹ ^ k + r ^ k) * hu

theorem qw_bounded_of_abs_le_two {c : ℝ} (hc : |c| ≤ 2) (k : ℕ) : |qw c k| ≤ 2 := by
  have h1 : -1 ≤ -c / 2 := by have := abs_le.mp hc; linarith
  have h2 : -c / 2 ≤ 1 := by have := abs_le.mp hc; linarith
  have hc' : c = -2 * Real.cos (Real.arccos (-c / 2)) := by
    rw [Real.cos_arccos h1 h2]; ring
  have hq : qw c k = 2 * Real.cos (k * Real.arccos (-c / 2)) := by
    conv_lhs => rw [hc']
    exact qw_cos _ k
  rw [hq, abs_mul, abs_two]
  have := Real.abs_cos_le_one (k * Real.arccos (-c / 2))
  linarith

/-- For `|c| > 2` the weights are `±(r^k + r^{-k})` with `r + r⁻¹ = |c|`, `r > 1`. -/
theorem qw_abs_eq_of_two_lt {c : ℝ} (hc : 2 < |c|) :
    ∃ r : ℝ, 1 < r ∧ ∀ k : ℕ, |qw c k| = r ^ k + r⁻¹ ^ k := by
  set b := |c| with hb
  have hS := Real.sq_sqrt (show (0 : ℝ) ≤ b ^ 2 - 4 by nlinarith)
  have hS0 := Real.sqrt_nonneg (b ^ 2 - 4)
  set r := (b + Real.sqrt (b ^ 2 - 4)) / 2 with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hr0 : r ≠ 0 := by linarith
  have hrinv : r⁻¹ = (b - Real.sqrt (b ^ 2 - 4)) / 2 := by
    rw [hr]
    have hne : b + Real.sqrt (b ^ 2 - 4) ≠ 0 := by linarith
    field_simp
    nlinarith
  have hsum : r + r⁻¹ = b := by rw [hrinv, hr]; ring
  refine ⟨r, hr1, fun k => ?_⟩
  have hpos : 0 < r ^ k + r⁻¹ ^ k := by
    have := pow_pos (show (0 : ℝ) < r by linarith) k
    have := pow_pos (inv_pos.mpr (show (0 : ℝ) < r by linarith)) k
    linarith
  rcases le_or_gt 0 c with h0 | h0
  · have hcb : c = b := by rw [hb, abs_of_nonneg h0]
    have hq : qw c k = (-1) ^ k * (r ^ k + r⁻¹ ^ k) := by
      have h := qw_neg (-c) k
      rw [neg_neg] at h
      rw [h, show -c = -(r + r⁻¹) by rw [hsum, hcb], qw_hyp hr0]
    rw [hq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hpos]
  · have hcb : c = -(r + r⁻¹) := by rw [hsum, hb, abs_of_neg h0]; ring
    rw [hcb, qw_hyp hr0, abs_of_pos hpos]

theorem qw_unbounded_of_two_lt {c : ℝ} (hc : 2 < |c|) (M : ℝ) : ∃ k : ℕ, M < |qw c k| := by
  obtain ⟨r, hr1, hr⟩ := qw_abs_eq_of_two_lt hc
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hr1
  refine ⟨k, ?_⟩
  rw [hr]
  have := pow_pos (inv_pos.mpr (show (0 : ℝ) < r by linarith)) k
  linarith

/-- **(b) Tempered dual weights iff `|c| ≤ 2` (kernel).** -/
theorem qw_bounded_iff (c : ℝ) : (∃ M : ℝ, ∀ k : ℕ, |qw c k| ≤ M) ↔ |c| ≤ 2 := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra h
    obtain ⟨k, hk⟩ := qw_unbounded_of_two_lt (not_le.mp h) M
    linarith [hM k]
  · intro hc
    exact ⟨2, qw_bounded_of_abs_le_two hc⟩

lemma quad_root_norm_one {c : ℝ} (hc : |c| ≤ 2) {X : ℂ} (h : X ^ 2 + c * X + 1 = 0) :
    ‖X‖ = 1 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hc2 : c ^ 2 ≤ 4 := by have := abs_le.mp hc; nlinarith
  have hn : X.re ^ 2 + X.im ^ 2 = 1 := by
    rcases eq_or_ne X.im 0 with hy | hy
    · rw [hy] at hre
      have h2 : 2 * X.re + c = 0 := by nlinarith [sq_nonneg (2 * X.re + c)]
      rw [hy]; nlinarith
    · have h2 : 2 * X.re + c = 0 := by
        have : X.im * (2 * X.re + c) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hy
      have h3 : X.re * (2 * X.re + c) = 0 := by rw [h2, mul_zero]
      linear_combination -hre + h3
  have hsq : ‖X‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  nlinarith [norm_nonneg X]

/-- **(c) Local Lee-Yang (unitary Satake) iff `|c| ≤ 2` (kernel).** -/
theorem quad_roots_unimodular_iff (c : ℝ) :
    (∀ X : ℂ, X ^ 2 + c * X + 1 = 0 → ‖X‖ = 1) ↔ |c| ≤ 2 := by
  constructor
  · intro h
    by_contra hc
    have hc := not_le.mp hc
    have hS := Real.sq_sqrt (show (0 : ℝ) ≤ c ^ 2 - 4 by nlinarith [sq_abs c])
    have hS0 := Real.sqrt_nonneg (c ^ 2 - 4)
    set l1 : ℝ := (-c + Real.sqrt (c ^ 2 - 4)) / 2
    set l2 : ℝ := (-c - Real.sqrt (c ^ 2 - 4)) / 2
    have e1 : ((l1 : ℂ)) ^ 2 + c * l1 + 1 = 0 := by
      have : l1 ^ 2 + c * l1 + 1 = 0 := by simp only [l1]; nlinarith
      exact_mod_cast this
    have e2 : ((l2 : ℂ)) ^ 2 + c * l2 + 1 = 0 := by
      have : l2 ^ 2 + c * l2 + 1 = 0 := by simp only [l2]; nlinarith
      exact_mod_cast this
    have n1 := h _ e1
    have n2 := h _ e2
    rw [Complex.norm_real, Real.norm_eq_abs] at n1 n2
    have hprod : l1 * l2 = 1 := by simp only [l1, l2]; nlinarith
    have hdiff : l1 - l2 = Real.sqrt (c ^ 2 - 4) := by simp only [l1, l2]; ring
    have hSpos : 0 < Real.sqrt (c ^ 2 - 4) := Real.sqrt_pos.mpr (by nlinarith [sq_abs c])
    -- |l1| = |l2| = 1 and l1 l2 = 1 force l1 = l2 = ±1, contradicting l1 - l2 > 0
    rcases abs_eq (zero_le_one' ℝ) |>.mp n1 with h1 | h1 <;>
      rcases abs_eq (zero_le_one' ℝ) |>.mp n2 with h2 | h2 <;>
      · rw [h1, h2] at hprod hdiff; linarith
  · intro hc X hX
    exact quad_root_norm_one hc hX

/-- The one-prime completed factor `Q_c(s) = p^{s-1/2} + c + p^{1/2-s}`. -/
def Qc (p c : ℝ) (s : ℂ) : ℂ := (p : ℂ) ^ (s - 1 / 2) + c + (p : ℂ) ^ ((1 : ℂ) / 2 - s)

lemma Qc_quad {p c : ℝ} (hp : 0 < p) (s : ℂ) :
    ((p : ℂ) ^ (s - 1 / 2)) ^ 2 + c * (p : ℂ) ^ (s - 1 / 2) + 1 =
      (p : ℂ) ^ (s - 1 / 2) * Qc p c s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hX0 : (p : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hp0 h.1
  have hinv : (p : ℂ) ^ ((1 : ℂ) / 2 - s) = ((p : ℂ) ^ (s - 1 / 2))⁻¹ := by
    rw [show (1 : ℂ) / 2 - s = -(s - 1 / 2) by ring, Complex.cpow_neg]
  unfold Qc
  rw [hinv]
  have hXX : (p : ℂ) ^ (s - 1 / 2) * ((p : ℂ) ^ (s - 1 / 2))⁻¹ = 1 := mul_inv_cancel₀ hX0
  linear_combination -hXX

lemma norm_cpow_sub_half {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ (s - 1 / 2)‖ = p ^ (s.re - 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  congr 1
  simp

theorem Qc_zero_re {p c : ℝ} (hp : 1 < p) (hc : |c| ≤ 2) {s : ℂ} (h : Qc p c s = 0) :
    s.re = 1 / 2 := by
  have hq := Qc_quad (c := c) (by linarith : (0 : ℝ) < p) s
  rw [h, mul_zero] at hq
  have hn := quad_root_norm_one hc hq
  rw [norm_cpow_sub_half (by linarith)] at hn
  rcases lt_trichotomy (s.re - 1 / 2) 0 with ht | ht | ht
  · have := Real.rpow_lt_one_of_one_lt_of_neg hp ht; linarith
  · linarith
  · have := Real.one_lt_rpow hp ht; linarith

theorem Qc_offline_zero {p c : ℝ} (hp : 1 < p) (hc : 2 < |c|) :
    ∃ s : ℂ, Qc p c s = 0 ∧ s.re ≠ 1 / 2 := by
  have hS := Real.sq_sqrt (show (0 : ℝ) ≤ c ^ 2 - 4 by nlinarith [sq_abs c])
  have hS0 := Real.sqrt_nonneg (c ^ 2 - 4)
  set l : ℝ := (-c + Real.sqrt (c ^ 2 - 4)) / 2 with hl
  have hleq : l ^ 2 + c * l + 1 = 0 := by rw [hl]; nlinarith
  have hl0 : l ≠ 0 := by intro h0; rw [h0] at hleq; norm_num at hleq
  have hl1 : |l| ≠ 1 := by
    intro h1
    rcases abs_eq (zero_le_one' ℝ) |>.mp h1 with h | h
    · rw [h] at hleq
      have : c = -2 := by linarith
      rw [this] at hc; norm_num at hc
    · rw [h] at hleq
      have : c = 2 := by linarith
      rw [this] at hc; norm_num at hc
  have hlogp : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  refine ⟨1 / 2 + Complex.log l / Real.log p, ?_, ?_⟩
  · have hX : (p : ℂ) ^ ((1 / 2 + Complex.log l / Real.log p) - 1 / 2) = l := by
      rw [show (1 / 2 + Complex.log l / Real.log p) - 1 / 2 = Complex.log l / Real.log p by ring,
        Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_log (by linarith : (0 : ℝ) ≤ p)]
      rw [show (Real.log p : ℂ) * (Complex.log l / Real.log p) = Complex.log l by
        field_simp]
      exact Complex.exp_log (by exact_mod_cast hl0)
    have hq := Qc_quad (c := c) (by linarith : (0 : ℝ) < p) (1 / 2 + Complex.log l / Real.log p)
    rw [hX] at hq
    have hq' : (l : ℂ) ^ 2 + c * l + 1 = 0 := by exact_mod_cast hleq
    rw [hq'] at hq
    exact (mul_eq_zero.mp hq.symm).resolve_left (by exact_mod_cast hl0)
  · have hre : (1 / 2 + Complex.log l / Real.log p).re = 1 / 2 + Real.log |l| / Real.log p := by
      simp [Complex.log_re]
    rw [hre]
    have hll : Real.log |l| ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (abs_pos.mpr hl0) hl1
    intro h
    have : Real.log |l| / Real.log p = 0 := by linarith
    rcases div_eq_zero_iff.mp this with h' | h'
    · exact hll h'
    · exact hlogp h'

/-- **(a) All zeros on the line iff `|c| ≤ 2` (kernel).** -/
theorem Qc_zeros_on_line_iff {p : ℝ} (hp : 1 < p) (c : ℝ) :
    (∀ s : ℂ, Qc p c s = 0 → s.re = 1 / 2) ↔ |c| ≤ 2 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨s, hs, hre⟩ := Qc_offline_zero hp (not_le.mp hc)
    exact hre (h s hs)
  · intro hc s hs
    exact Qc_zero_re hp hc hs

/-- **Finite-rank theorem (kernel): real zeros = tempered dual = local Lee-Yang.** For the
one-prime factor `Q_c`, the three FQ-type conditions coincide; each is `|c| ≤ 2`. -/
theorem finite_rank_realZeros_iff_tempered_iff_leeYang {p : ℝ} (hp : 1 < p) (c : ℝ) :
    ((∀ s : ℂ, Qc p c s = 0 → s.re = 1 / 2) ↔ (∃ M : ℝ, ∀ k : ℕ, |qw c k| ≤ M)) ∧
    ((∃ M : ℝ, ∀ k : ℕ, |qw c k| ≤ M) ↔ (∀ X : ℂ, X ^ 2 + c * X + 1 = 0 → ‖X‖ = 1)) := by
  rw [Qc_zeros_on_line_iff hp, qw_bounded_iff, quad_roots_unimodular_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-! ### The golden fake (`p = 5`, `c = √5`) -/

open scoped goldenRatio

lemma sqrt5_eq_gold_add_inv : Real.sqrt 5 = φ + φ⁻¹ := by
  rw [Real.inv_goldenRatio, ← sub_eq_add_neg, Real.goldenRatio_sub_goldenConj]

/-- **Golden dual weights (kernel):** `qw √5 k = (-1)^k (φ^k + φ^{-k})`, i.e. round 1's
`-2.236, 3, -4.472, 7, -11.18, 18, ...`: they grow like `φ^k`, so the dual is not tempered. -/
theorem golden_weights (k : ℕ) : qw (Real.sqrt 5) k = (-1) ^ k * (φ ^ k + φ⁻¹ ^ k) := by
  have h := qw_neg (-Real.sqrt 5) k
  rw [neg_neg] at h
  rw [h, sqrt5_eq_gold_add_inv, qw_hyp Real.goldenRatio_ne_zero]

theorem golden_weights_unbounded (M : ℝ) : ∃ k : ℕ, M < |qw (Real.sqrt 5) k| := by
  refine qw_unbounded_of_two_lt ?_ M
  rw [abs_of_pos (by positivity)]
  exact sqrt5_gt_two

/-- The golden completed factor is `Q_{√5}` at `p = 5`: `XiA(s) = 2cosh((s-1/2)log 5) + √5`. -/
theorem golden_zero_re {s : ℂ} (h : Qc 5 (Real.sqrt 5) s = 0) :
    s.re = 1 / 2 + Real.log φ / Real.log 5 ∨ s.re = 1 / 2 - Real.log φ / Real.log 5 := by
  have hq := Qc_quad (c := Real.sqrt 5) (by norm_num : (0 : ℝ) < 5) s
  rw [h, mul_zero] at hq
  set X := ((5 : ℝ) : ℂ) ^ (s - 1 / 2) with hXdef
  have e1 : ((Real.sqrt 5 : ℝ) : ℂ) = (φ : ℂ) + ((φ⁻¹ : ℝ) : ℂ) := by
    rw [sqrt5_eq_gold_add_inv, Complex.ofReal_add]
  have e2 : (φ : ℂ) * ((φ⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ Real.goldenRatio_ne_zero, Complex.ofReal_one]
  have hfac : (X + φ) * (X + ((φ⁻¹ : ℝ) : ℂ)) = 0 := by
    rw [e1] at hq
    linear_combination hq + e2
  have hnorm : ‖X‖ = (5 : ℝ) ^ (s.re - 1 / 2) := norm_cpow_sub_half (by norm_num) s
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hφ := Real.goldenRatio_pos
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    have hX : X = -(φ : ℂ) := by linear_combination h1
    rw [hX, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hφ] at hnorm
    have ht : (s.re - 1 / 2) * Real.log 5 = Real.log φ := by
      rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 5), ← hnorm]
    have : s.re - 1 / 2 = Real.log φ / Real.log 5 := by rw [eq_div_iff hl5.ne']; exact ht
    linarith
  · right
    have hX : X = -((φ⁻¹ : ℝ) : ℂ) := by linear_combination h1
    rw [hX, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hφ)]
      at hnorm
    have ht : (s.re - 1 / 2) * Real.log 5 = -Real.log φ := by
      rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 5), ← hnorm, Real.log_inv]
    have : s.re - 1 / 2 = -Real.log φ / Real.log 5 := by rw [eq_div_iff hl5.ne']; exact ht
    rw [neg_div] at this
    linarith

/-- The golden Frobenius factorization: `1 + 5T + 5T² = (1 + √5 φ T)(1 + √5 φ⁻¹ T)`, i.e.
`α = -√5 φ`, `β = -√5 φ⁻¹` with `|α|, |β| ≠ √5` (not on the Lee-Yang circle `|T| = 5^{-1/2}`). -/
theorem golden_factor (T : ℝ) :
    1 + 5 * T + 5 * T ^ 2 = (1 + Real.sqrt 5 * φ * T) * (1 + Real.sqrt 5 * φ⁻¹ * T) := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hφ : φ * φ⁻¹ = 1 := mul_inv_cancel₀ Real.goldenRatio_ne_zero
  have hsum := sqrt5_eq_gold_add_inv
  have : (1 + Real.sqrt 5 * φ * T) * (1 + Real.sqrt 5 * φ⁻¹ * T) =
      1 + Real.sqrt 5 * (φ + φ⁻¹) * T + Real.sqrt 5 ^ 2 * (φ * φ⁻¹) * T ^ 2 := by ring
  rw [this, ← hsum, hφ]
  linear_combination (-T - T ^ 2) * h5

/-- **Golden positive full dual (kernel):** the "point counts"
`N_k = 5^k + 1 - (α^k + β^k)` are positive for every `k ≥ 1` (`N_k = (1 - α^k)(1 - β^k)`). -/
theorem golden_count_pos (k : ℕ) (hk : k ≠ 0) :
    0 < (5 : ℝ) ^ k + 1 - ((-(Real.sqrt 5 * φ)) ^ k + (-(Real.sqrt 5 * φ⁻¹)) ^ k) := by
  set A := Real.sqrt 5 * φ
  set B := Real.sqrt 5 * φ⁻¹
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hAB : A * B = 5 := by
    simp only [A, B]
    have hφ : φ * φ⁻¹ = 1 := mul_inv_cancel₀ Real.goldenRatio_ne_zero
    calc Real.sqrt 5 * φ * (Real.sqrt 5 * φ⁻¹) = Real.sqrt 5 ^ 2 * (φ * φ⁻¹) := by ring
      _ = 5 := by rw [h5, hφ, mul_one]
  have hs2 := sqrt5_gt_two
  have hφ1 := Real.one_lt_goldenRatio
  have hφ2 := Real.goldenRatio_lt_two
  have hA : 1 < A := by simp only [A]; nlinarith
  have hB : 1 < B := by
    simp only [B]
    have hinv : (1 : ℝ) / 2 < φ⁻¹ := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num]
      exact inv_strictAnti₀ Real.goldenRatio_pos hφ2
    nlinarith
  have hAk : 1 < A ^ k := one_lt_pow₀ hA hk
  have hBk : 1 < B ^ k := one_lt_pow₀ hB hk
  have h5k : (5 : ℝ) ^ k = A ^ k * B ^ k := by rw [← mul_pow, hAB]
  rw [h5k, neg_pow A, neg_pow B]
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow]; nlinarith
  · rw [ho.neg_one_pow]; nlinarith

/-- Round 1's W1 factor `1 + 11·29^{-s} + 29·29^{-2s}` is `Q_c` at `p = 29`, `c = 11/√29 > 2`:
off-line zeros and unbounded dual weights (kernel, via the finite-rank theorem). -/
theorem W1_fails_finite_rank :
    2 < |(11 / Real.sqrt 29 : ℝ)| ∧ (∃ s : ℂ, Qc 29 (11 / Real.sqrt 29) s = 0 ∧ s.re ≠ 1 / 2) ∧
    ∀ M : ℝ, ∃ k : ℕ, M < |qw (11 / Real.sqrt 29) k| := by
  have h29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hpos : 0 < Real.sqrt 29 := Real.sqrt_pos.mpr (by norm_num)
  have hc : 2 < |(11 / Real.sqrt 29 : ℝ)| := by
    rw [abs_of_pos (div_pos (by norm_num) hpos), lt_div_iff₀ hpos]
    nlinarith
  exact ⟨hc, Qc_offline_zero (by norm_num) hc, qw_unbounded_of_two_lt hc⟩

/-! ## E. The imaginary-shift control `E_θ(s) = ζ(s+θ) ζ(s-θ)`

Its zero measure is zeta's translated by `±iθ` in the `γ = (s-1/2)/i` coordinate, and its dual
weights are `Λ(n)(n^θ + n^{-θ}) = 2cosh(θ log n) Λ(n)`: nonnegative, carried by prime powers, and
decaying against `√n` for `|θ| < 1/2`. It has an entire, `s ↦ 1-s` symmetric completion
`ξ(s+θ)ξ(s-θ)`. Kernel: it has off-line zeros above every height UNCONDITIONALLY (this discharges
the `hzero` hypothesis of the corpus scratch file `EisensteinShiftControl.lean`), under RH it has
NO zero on the line, and `RH ⟺ all its zeros lie on Re s = 1/2 ± θ`. What separates it from zeta
is the pole at `1 + θ` (kernel) and the shifted gamma factor (not formalized). -/

/-! ### The entire completion `xiC` of zeta (source-ported from `Crux_axiso_construct.lean`) -/

/-- `xiC u = u (u-1) Λ₀(u) + 1`, the entire completion `u(u-1)Λ(u)` of zeta. -/
def xiC (u : ℂ) : ℂ := u * (u - 1) * completedRiemannZeta₀ u + 1

lemma differentiable_xiC : Differentiable ℂ xiC :=
  ((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1

lemma xiC_one_sub (u : ℂ) : xiC (1 - u) = xiC u := by
  simp only [xiC, completedRiemannZeta₀_one_sub]
  ring

lemma xiC_eq_completed {u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) :
    xiC u = u * (u - 1) * completedRiemannZeta u := by
  have h1' : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : (u - 1) ≠ 0 := sub_ne_zero.mpr h1
  rw [completedRiemannZeta_eq, xiC]
  field_simp
  ring

lemma completed_eq_Gammaℝ_mul {u : ℂ} (h0 : u ≠ 0) (hG : Gammaℝ u ≠ 0) :
    completedRiemannZeta u = Gammaℝ u * riemannZeta u := by
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

lemma xiC_eq_zeta {u : ℂ} (h0 : u ≠ 0) (h1 : u ≠ 1) (hG : Gammaℝ u ≠ 0) :
    xiC u = u * (u - 1) * Gammaℝ u * riemannZeta u := by
  rw [xiC_eq_completed h0 h1, completed_eq_Gammaℝ_mul h0 hG]
  ring

lemma xiC_one : xiC 1 = 1 := by simp [xiC]

lemma xiC_ne_zero_of_one_le_re {u : ℂ} (hu : 1 ≤ u.re) : xiC u ≠ 0 := by
  rcases eq_or_ne u 1 with rfl | h1
  · rw [xiC_one]; exact one_ne_zero
  have h0 : u ≠ 0 := by rintro rfl; simp at hu; linarith
  have hG : Gammaℝ u ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xiC_eq_zeta h0 h1 hG]
  have hz := riemannZeta_ne_zero_of_one_le_re hu
  have h1' : u - 1 ≠ 0 := sub_ne_zero.mpr h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1') hG) hz

lemma xiC_ne_zero_of_re_nonpos {u : ℂ} (hu : u.re ≤ 0) : xiC u ≠ 0 := by
  rw [← xiC_one_sub]
  exact xiC_ne_zero_of_one_le_re (by simp; linarith)

lemma xiC_zero_strip {u : ℂ} (h : xiC u = 0) : 0 < u.re ∧ u.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hc; exact xiC_ne_zero_of_re_nonpos (not_lt.mp hc) h
  · by_contra hc; exact xiC_ne_zero_of_one_le_re (not_lt.mp hc) h

lemma xiC_eq_zero_of_zeta {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    xiC ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [xiC_eq_zeta hρ0 hρ1 (Complex.Gammaℝ_ne_zero_of_re_pos h0), hz, mul_zero]

/-- (new) A zero of `xiC` is a nontrivial zero of `ζ` in the open strip. -/
lemma zeta_eq_zero_of_xiC {u : ℂ} (h : xiC u = 0) :
    riemannZeta u = 0 ∧ 0 < u.re ∧ u.re < 1 := by
  obtain ⟨h0, h1⟩ := xiC_zero_strip h
  have hu0 : u ≠ 0 := by rintro rfl; simp at h0
  have hu1 : u ≠ 1 := by rintro rfl; simp at h1
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos h0
  rw [xiC_eq_zeta hu0 hu1 hG] at h
  refine ⟨?_, h0, h1⟩
  have hne : u * (u - 1) * Gammaℝ u ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu0 (sub_ne_zero.mpr hu1)) hG
  exact (mul_eq_zero.mp h).resolve_left hne

/-- (new) A zero of `ζ` that is not trivial is a zero of `xiC` (so it lies in the open strip). -/
lemma xiC_eq_zero_of_nontrivial {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (n + 1)) : xiC s = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
  have hs1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  have hG : Gammaℝ s ≠ 0 := by
    rw [Ne, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hs0 (by simpa using hn)
    · apply hnt
      refine ⟨n - 1, ?_⟩
      rw [hn]
      have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
  rw [xiC_eq_zeta hs0 hs1 hG, hz, mul_zero]

/-- For every height `T` there is a zero `ρ` of `ζ` with `0 < Re ρ < 1` and `Im ρ > T`.
Source-ported from `Crux_axiso_construct.lean`: re-derived from Zeta23's hypothesis-free
Riemann--von Mangoldt formula. -/
theorem exists_nontrivial_zero_above (T : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im := by
  have hRvM := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  have h1 := Zeta23.Assembly.eventually_N_ge Zeta23.zetaZeroConfig hRvM
  have h2 : ∀ᶠ T' : ℝ in atTop, 4 * Real.pi < T' * Zeta23.l T' :=
    Zeta23.Assembly.tendsto_Tl_atTop.eventually_gt_atTop _
  obtain ⟨T', ⟨hT1, hT2⟩, hT3⟩ := ((h1.and h2).and (eventually_ge_atTop T)).exists
  have hpos : (0 : ℝ) < (Zeta23.zetaZeroConfig.N T' (2 * T') : ℝ) := by
    refine lt_of_lt_of_le ?_ hT1
    rw [lt_div_iff₀ (by positivity), zero_mul]
    linarith [Real.pi_pos]
  have hne : (Zeta23.zetaZeroConfig.window T' (2 * T')).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [Zeta23.ZeroConfig.N, h] at hpos
  obtain ⟨ρ, hρ, hρT, -⟩ := hne
  have hρ' : Zeta23.IsNontrivialZero ρ := hρ
  exact ⟨ρ, hρ'.1, hρ'.2.1, hρ'.2.2, lt_of_le_of_lt hT3 hρT⟩

/-! ### The control and its completion -/

/-- The imaginary-shift control `E_θ(s) = ζ(s+θ) ζ(s-θ)`. -/
def Etheta (θ : ℝ) (s : ℂ) : ℂ := riemannZeta (s + θ) * riemannZeta (s - θ)

/-- Its entire completion `ξ(s+θ) ξ(s-θ)`. -/
def XiTheta (θ : ℝ) (s : ℂ) : ℂ := xiC (s + θ) * xiC (s - θ)

theorem XiTheta_entire (θ : ℝ) : Differentiable ℂ (XiTheta θ) :=
  (differentiable_xiC.comp (differentiable_id.add_const _)).mul
    (differentiable_xiC.comp (differentiable_id.sub_const _))

/-- The completion is self-dual: `XiTheta θ (1 - s) = XiTheta θ s`. -/
theorem XiTheta_one_sub (θ : ℝ) (s : ℂ) : XiTheta θ (1 - s) = XiTheta θ s := by
  unfold XiTheta
  have e1 : 1 - s + (θ : ℂ) = 1 - (s - θ) := by ring
  have e2 : 1 - s - (θ : ℂ) = 1 - (s + θ) := by ring
  rw [e1, e2, xiC_one_sub, xiC_one_sub, mul_comm]

/-- The completion identity: `XiTheta = [(s+θ)(s+θ-1)Γ_ℝ(s+θ)] [(s-θ)(s-θ-1)Γ_ℝ(s-θ)] E_θ`,
i.e. the gamma factor is `Γ_ℝ(s+θ) Γ_ℝ(s-θ)` (shifted spectral parameters `±θ/2`). -/
theorem XiTheta_eq_completion {θ : ℝ} {s : ℂ} (hs : |θ| < s.re) (h1 : s + θ ≠ 1)
    (h2 : s - θ ≠ 1) :
    XiTheta θ s = ((s + θ) * (s + θ - 1) * Gammaℝ (s + θ)) *
      ((s - θ) * (s - θ - 1) * Gammaℝ (s - θ)) * Etheta θ s := by
  have hp : 0 < (s + θ).re := by simp; linarith [neg_abs_le θ]
  have hm : 0 < (s - θ).re := by simp; linarith [le_abs_self θ]
  have hp0 : s + θ ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hm0 : s - θ ≠ 0 := by intro h; rw [h] at hm; simp at hm
  unfold XiTheta Etheta
  rw [xiC_eq_zeta hp0 h1 (Complex.Gammaℝ_ne_zero_of_re_pos hp),
    xiC_eq_zeta hm0 h2 (Complex.Gammaℝ_ne_zero_of_re_pos hm)]
  ring

/-- Every zero of the completion lies in `-|θ| < Re s < 1 + |θ|`: strictly LEFT of the real pole
at `1 + |θ|` (Landau's pole shadow, for this control). -/
theorem XiTheta_zero_re_bounds {θ : ℝ} {s : ℂ} (h : XiTheta θ s = 0) :
    -|θ| < s.re ∧ s.re < 1 + |θ| := by
  have h1 := le_abs_self θ
  have h2 := neg_abs_le θ
  rcases mul_eq_zero.mp h with h' | h'
  · obtain ⟨a, b⟩ := xiC_zero_strip h'
    simp at a b
    constructor <;> linarith
  · obtain ⟨a, b⟩ := xiC_zero_strip h'
    simp at a b
    constructor <;> linarith

/-- Zero transfer: each nontrivial zero `ρ` of `ζ` gives zeros of `XiTheta` and `E_θ` at
`ρ - θ` and `ρ + θ` (the zero measure is translated by `±iθ` in `γ`-coordinates). -/
theorem XiTheta_zero_of_zeta_zero (θ : ℝ) {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    XiTheta θ (ρ - θ) = 0 ∧ XiTheta θ (ρ + θ) = 0 ∧ Etheta θ (ρ - θ) = 0 ∧
      Etheta θ (ρ + θ) = 0 := by
  have hx := xiC_eq_zero_of_zeta hz h0 h1
  have e1 : ρ - (θ : ℂ) + θ = ρ := by ring
  have e2 : ρ + (θ : ℂ) - θ = ρ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold XiTheta; rw [e1, hx, zero_mul]
  · unfold XiTheta; rw [e2, hx, mul_zero]
  · unfold Etheta; rw [e1, hz, zero_mul]
  · unfold Etheta; rw [e2, hz, mul_zero]

/-- **Unconditional off-line zeros of the shift control (kernel).** For `θ ≠ 0`, above every
height `T` there is a zero of `XiTheta θ` (and of `E_θ`) off `Re s = 1/2`. No Hardy input: of
`ρ ± θ` at most one lies on the line. -/
theorem Etheta_offline_zeros {θ : ℝ} (hθ : θ ≠ 0) (T : ℝ) :
    ∃ s : ℂ, XiTheta θ s = 0 ∧ Etheta θ s = 0 ∧ s.re ≠ 1 / 2 ∧ T < s.im := by
  obtain ⟨ρ, hz, h0, h1, hT⟩ := exists_nontrivial_zero_above T
  obtain ⟨hm, hp, hEm, hEp⟩ := XiTheta_zero_of_zeta_zero θ hz h0 h1
  by_cases h : (ρ + θ).re = 1 / 2
  · refine ⟨ρ - θ, hm, hEm, ?_, by simpa using hT⟩
    simp only [Complex.add_re, Complex.ofReal_re] at h
    simp only [Complex.sub_re, Complex.ofReal_re]
    intro h'; apply hθ; linarith
  · exact ⟨ρ + θ, hp, hEp, h, by simpa using hT⟩

/-- **The corpus scratch statement `eisShift_violates_RH_analogue'` with its `hzero` hypothesis
discharged** (xiC normalization; FE-symmetric, and a zero off `Re s = 1/2`). -/
theorem eisShift_violates_RH_analogue_unconditional {θ : ℝ} (hθ : θ ≠ 0) :
    (∀ s : ℂ, XiTheta θ (1 - s) = XiTheta θ s) ∧ ∃ s : ℂ, XiTheta θ s = 0 ∧ s.re ≠ 1 / 2 := by
  refine ⟨XiTheta_one_sub θ, ?_⟩
  obtain ⟨s, hs, -, hre, -⟩ := Etheta_offline_zeros hθ 0
  exact ⟨s, hs, hre⟩

/-- Under RH every zero of `XiTheta θ` lies on `Re s = 1/2 - θ` or `Re s = 1/2 + θ`. -/
theorem XiTheta_zeros_of_RH (hRH : RiemannHypothesis) {θ : ℝ} {s : ℂ} (h : XiTheta θ s = 0) :
    s.re = 1 / 2 - θ ∨ s.re = 1 / 2 + θ := by
  have key : ∀ u : ℂ, xiC u = 0 → u.re = 1 / 2 := by
    intro u hu
    obtain ⟨hz, h0, h1⟩ := zeta_eq_zero_of_xiC hu
    refine hRH u hz ?_ ?_
    · rintro ⟨n, hn⟩
      rw [hn] at h0
      simp at h0
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rintro rfl; simp at h1
  rcases mul_eq_zero.mp h with h' | h'
  · left
    have := key _ h'
    simp at this
    linarith
  · right
    have := key _ h'
    simp at this
    linarith

/-- **Under RH, NO zero of the shift control lies on its critical line (kernel).** -/
theorem XiTheta_no_zero_on_line_of_RH (hRH : RiemannHypothesis) {θ : ℝ} (hθ : θ ≠ 0)
    {s : ℂ} (h : XiTheta θ s = 0) : s.re ≠ 1 / 2 := by
  rcases XiTheta_zeros_of_RH hRH h with h' | h' <;>
  · intro h''; apply hθ; linarith

/-- **Shift-conjugated RH (kernel).** For `θ ≠ 0`: RH holds iff every zero of `XiTheta θ` lies
on one of the two lines `Re s = 1/2 ± θ`. So the control's correct "RH" is RH for `ζ` itself,
translated; the naive "all zeros on `Re s = 1/2`" is false unconditionally. -/
theorem RH_iff_XiTheta_two_lines {θ : ℝ} (hθ : θ ≠ 0) :
    RiemannHypothesis ↔ ∀ s : ℂ, XiTheta θ s = 0 → s.re = 1 / 2 - θ ∨ s.re = 1 / 2 + θ := by
  refine ⟨fun hRH s hs => XiTheta_zeros_of_RH hRH hs, fun h => ?_⟩
  intro s hz hnt _
  have hx := xiC_eq_zero_of_nontrivial hz hnt
  have e1 : XiTheta θ (s - θ) = 0 := by
    unfold XiTheta
    rw [show s - (θ : ℂ) + θ = s by ring, hx, zero_mul]
  have e2 : XiTheta θ (s + θ) = 0 := by
    unfold XiTheta
    rw [show s + (θ : ℂ) - θ = s by ring, hx, mul_zero]
  have r1 := h _ e1
  have r2 := h _ e2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at r1 r2
  rcases r1 with r1 | r1 <;> rcases r2 with r2 | r2
  · linarith
  · linarith
  · exfalso; apply hθ; linarith
  · linarith

/-! ### The dual of the shift control: `ν_{E_θ} = 2cosh(θ x) ν_ζ` -/

/-- Dual weights of `E_θ`: `Λ_θ(n) = Λ(n) (n^θ + n^{-θ})`. -/
def LambdaTheta (θ : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ θ + (n : ℝ) ^ (-θ))

theorem LambdaTheta_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ LambdaTheta θ n := by
  unfold LambdaTheta
  have h1 := Real.rpow_nonneg (Nat.cast_nonneg n) θ
  have h2 := Real.rpow_nonneg (Nat.cast_nonneg n) (-θ)
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith)

/-- `Λ_θ(n) = 2 cosh(θ log n) Λ(n)`: the dual of `E_θ` is `2cosh(θx)` times zeta's. -/
theorem LambdaTheta_eq_cosh (θ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LambdaTheta θ n = 2 * Real.cosh (θ * Real.log n) * ArithmeticFunction.vonMangoldt n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold LambdaTheta
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos, Real.cosh_eq]
  have e1 : Real.log n * θ = θ * Real.log n := by ring
  have e2 : Real.log n * -θ = -(θ * Real.log n) := by ring
  rw [e1, e2]
  ring

/-- The dual of `E_θ` is carried by prime powers, exactly like zeta's. -/
theorem LambdaTheta_ne_zero_iff (θ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LambdaTheta θ n ≠ 0 ↔ IsPrimePow n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : (n : ℝ) ^ θ + (n : ℝ) ^ (-θ) ≠ 0 := by
    have := Real.rpow_pos_of_pos hpos θ
    have := Real.rpow_pos_of_pos hpos (-θ)
    linarith
  unfold LambdaTheta
  rw [← ArithmeticFunction.vonMangoldt_ne_zero_iff]
  exact ⟨fun h h' => h (by rw [h', zero_mul]), fun h => mul_ne_zero h hs⟩

/-- The log-derivative of `E_θ` splits as zeta's at `s ± θ`. -/
lemma Etheta_logDeriv_split {θ : ℝ} {s : ℂ} (hs : 1 + |θ| < s.re) :
    -deriv (Etheta θ) s / Etheta θ s =
      (-deriv riemannZeta (s + θ) / riemannZeta (s + θ)) +
        (-deriv riemannZeta (s - θ) / riemannZeta (s - θ)) := by
  have hwre : 1 < (s + (θ : ℂ)).re := by simp; linarith [neg_abs_le θ]
  have hvre : 1 < (s - (θ : ℂ)).re := by simp; linarith [le_abs_self θ]
  have hw1 : s + (θ : ℂ) ≠ 1 := by rintro h; rw [h] at hwre; simp at hwre
  have hv1 : s - (θ : ℂ) ≠ 1 := by rintro h; rw [h] at hvre; simp at hvre
  have hdw : HasDerivAt (fun z : ℂ => riemannZeta (z + θ))
      (deriv riemannZeta (s + θ) * 1) s :=
    (differentiableAt_riemannZeta hw1).hasDerivAt.comp s ((hasDerivAt_id' s).add_const _)
  have hdv : HasDerivAt (fun z : ℂ => riemannZeta (z - θ))
      (deriv riemannZeta (s - θ) * 1) s :=
    (differentiableAt_riemannZeta hv1).hasDerivAt.comp s ((hasDerivAt_id' s).sub_const _)
  have hF : HasDerivAt (Etheta θ) (deriv riemannZeta (s + θ) * 1 * riemannZeta (s - θ) +
      riemannZeta (s + θ) * (deriv riemannZeta (s - θ) * 1)) s := hdw.mul hdv
  rw [hF.deriv]
  have hzw : riemannZeta (s + θ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre.le
  have hzv : riemannZeta (s - θ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hvre.le
  simp only [Etheta, mul_one]
  field_simp
  ring

/-- Termwise: `Λ_θ(n) n^{-s} = Λ(n) n^{-(s+θ)} + Λ(n) n^{-(s-θ)}`. -/
lemma LambdaTheta_term (θ : ℝ) (s : ℂ) (n : ℕ) :
    ((LambdaTheta θ n : ℝ) : ℂ) * (n : ℂ) ^ (-s) =
      term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (s + θ) n +
        term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (s - θ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LambdaTheta]
  rw [term_of_ne_zero hn, term_of_ne_zero hn]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hS0 : (n : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hn0 h.1
  have hN0 : (n : ℂ) ^ (θ : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hn0 h.1
  have ew : (n : ℂ) ^ (s + (θ : ℂ)) = (n : ℂ) ^ s * (n : ℂ) ^ (θ : ℂ) := cpow_add _ _ hn0
  have ev : (n : ℂ) ^ (s - (θ : ℂ)) = (n : ℂ) ^ s / (n : ℂ) ^ (θ : ℂ) := cpow_sub _ _ hn0
  have e1 : (((n : ℝ) ^ θ : ℝ) : ℂ) = (n : ℂ) ^ (θ : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have e2 : (((n : ℝ) ^ (-θ) : ℝ) : ℂ) = ((n : ℂ) ^ (θ : ℂ))⁻¹ := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
      cpow_neg]
  have e3 : (n : ℂ) ^ (-s) = ((n : ℂ) ^ s)⁻¹ := cpow_neg _ _
  have hL : ((LambdaTheta θ n : ℝ) : ℂ) =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        ((n : ℂ) ^ (θ : ℂ) + ((n : ℂ) ^ (θ : ℂ))⁻¹) := by
    rw [LambdaTheta, Complex.ofReal_mul, Complex.ofReal_add, e1, e2]
  rw [hL, e3, ew, ev]
  field_simp
  ring

/-- **Euler / dual identity for `E_θ` (kernel).** For `Re s > 1 + |θ|`,
`-E_θ'(s)/E_θ(s) = Σ Λ(n)(n^θ + n^{-θ}) n^{-s}`. -/
theorem Etheta_logDeriv_hasSum {θ : ℝ} {s : ℂ} (hs : 1 + |θ| < s.re) :
    HasSum (fun n : ℕ => ((LambdaTheta θ n : ℝ) : ℂ) * (n : ℂ) ^ (-s))
      (-deriv (Etheta θ) s / Etheta θ s) := by
  have hwre : 1 < (s + (θ : ℂ)).re := by simp; linarith [neg_abs_le θ]
  have hvre : 1 < (s - (θ : ℂ)).re := by simp; linarith [le_abs_self θ]
  have hsplit := Etheta_logDeriv_split hs
  have hterm := LambdaTheta_term θ s
  -- make `s + θ` and `s - θ` opaque, so that no defeq check unfolds real arithmetic
  generalize s + (θ : ℂ) = w at hwre hsplit hterm
  generalize s - (θ : ℂ) = v at hvre hsplit hterm
  rw [hsplit, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hwre,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hvre]
  have hfun : (fun n : ℕ => ((LambdaTheta θ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) = fun n =>
      term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) w n +
        term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) v n := funext hterm
  rw [hfun]
  have hsw : HasSum (term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) w)
      (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) w) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hwre).LSeriesHasSum
  have hsv : HasSum (term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) v)
      (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) v) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hvre).LSeriesHasSum
  exact HasSum.add hsw hsv

/-- `E_θ` has dual weights in the sense of `IsLogDerivCoeff`, all nonnegative. -/
theorem Etheta_isLogDerivCoeff (θ : ℝ) :
    IsLogDerivCoeff (Etheta θ) (fun n => ((LambdaTheta θ n : ℝ) : ℂ)) ∧
      ∀ n, (0 : ℂ) ≤ ((LambdaTheta θ n : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, fun n => Complex.zero_le_real.mpr (LambdaTheta_nonneg θ n)⟩
  · have hs : 1 + |θ| < ((2 + |θ| : ℝ) : ℂ).re := by simp
    have hsum := (Etheta_logDeriv_hasSum hs)
    have hsm : LSeriesSummable (fun n => ((LambdaTheta θ n : ℝ) : ℂ)) ((2 + |θ| : ℝ) : ℂ) := by
      refine (summable_congr fun n => ?_).mp hsum.summable
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LambdaTheta]
      · rw [term_of_ne_zero hn, div_eq_mul_inv, cpow_neg]
    exact hsm.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast EReal.coe_lt_top _)
  · filter_upwards [eventually_gt_atTop (1 + |θ|)] with x hx
    have hs : 1 + |θ| < (x : ℂ).re := by simpa using hx
    rw [← (Etheta_logDeriv_hasSum hs).tsum_eq]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LambdaTheta]
    · rw [term_of_ne_zero hn, div_eq_mul_inv, cpow_neg]

/-- **The dual weights of `E_θ` decay against `√n` for `|θ| < 1/2` (kernel).** -/
theorem LambdaTheta_weight_tendsto_zero {θ : ℝ} (hθ : |θ| < 1 / 2) :
    Tendsto (fun n : ℕ => LambdaTheta θ n / Real.sqrt n) atTop (𝓝 0) := by
  set ε := 1 / 2 - |θ| with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlim : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε0).tendsto_div_nhds_zero
  have hlimN : Tendsto (fun n : ℕ => 2 * (Real.log n / (n : ℝ) ^ ε)) atTop (𝓝 0) := by
    have := (hlim.comp tendsto_natCast_atTop_atTop).const_mul 2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimN ?_ ?_
  · exact Eventually.of_forall fun n =>
      div_nonneg (LambdaTheta_nonneg θ n) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hp1 : (n : ℝ) ^ θ ≤ (n : ℝ) ^ |θ| :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_abs_self θ)
    have hp2 : (n : ℝ) ^ (-θ) ≤ (n : ℝ) ^ |θ| :=
      Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_abs θ)
    have hsq : Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow n
    have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsplit : (n : ℝ) ^ |θ| = (n : ℝ) ^ ((1 : ℝ) / 2) / (n : ℝ) ^ ε := by
      rw [← Real.rpow_sub hnpos]; congr 1; rw [hε]; ring
    have hεpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
    have hbound : LambdaTheta θ n ≤ Real.log n * (2 * (n : ℝ) ^ |θ|) := by
      unfold LambdaTheta
      have h0 : 0 ≤ (n : ℝ) ^ θ + (n : ℝ) ^ (-θ) := by
        have := Real.rpow_nonneg hnpos.le θ
        have := Real.rpow_nonneg hnpos.le (-θ)
        linarith
      calc ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ θ + (n : ℝ) ^ (-θ))
          ≤ Real.log n * ((n : ℝ) ^ θ + (n : ℝ) ^ (-θ)) := mul_le_mul_of_nonneg_right hΛ h0
        _ ≤ Real.log n * (2 * (n : ℝ) ^ |θ|) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg hn1)
    rw [div_le_iff₀ hsqpos]
    calc LambdaTheta θ n ≤ Real.log n * (2 * (n : ℝ) ^ |θ|) := hbound
      _ = 2 * (Real.log n / (n : ℝ) ^ ε) * Real.sqrt n := by
        rw [hsplit, hsq]; field_simp

/-- **The pole axiom fails for `E_θ` (kernel).** For `θ > 0`, `E_θ` has a genuine pole at
`1 + θ ≠ 1`: `(s - (1+θ)) E_θ(s) → ζ(1+2θ) ≠ 0`. -/
theorem Etheta_pole {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun s : ℂ => (s - (1 + θ)) * Etheta θ s) (𝓝[≠] (1 + θ))
      (𝓝 (riemannZeta (1 + 2 * θ))) ∧ riemannZeta (1 + 2 * θ) ≠ 0 := by
  refine ⟨?_, riemannZeta_ne_zero_of_one_le_re (by simp; linarith)⟩
  have hmap : Tendsto (fun s : ℂ => s - θ) (𝓝[≠] (1 + θ)) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun s : ℂ => s - θ) (𝓝 (1 + θ)) (𝓝 ((1 + θ) - θ)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [show ((1 : ℂ) + θ) - θ = 1 by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h
      apply hs
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h
  have h1 := riemannZeta_residue_one.comp hmap
  have h2 : Tendsto (fun s : ℂ => riemannZeta (s + θ)) (𝓝[≠] (1 + θ))
      (𝓝 (riemannZeta (1 + 2 * θ))) := by
    have hne : (1 : ℂ) + 2 * θ ≠ 1 := by
      intro h
      have : ((2 * θ : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
      have : (2 * θ : ℝ) = 0 := by exact_mod_cast this
      linarith
    have hc : ContinuousAt riemannZeta (1 + 2 * θ) :=
      (differentiableAt_riemannZeta hne).continuousAt
    have h : Tendsto (fun s : ℂ => s + θ) (𝓝 (1 + θ)) (𝓝 ((1 + θ) + θ)) :=
      (continuous_id.add continuous_const).tendsto _
    rw [show ((1 : ℂ) + θ) + θ = 1 + 2 * θ by ring] at h
    exact (hc.tendsto.comp h).mono_left nhdsWithin_le_nhds
  have hlim := h2.mul h1
  rw [mul_one] at hlim
  refine hlim.congr (fun s => ?_)
  simp only [Etheta, Function.comp_apply]
  ring_nf

/-- **Capstone for the shift control (kernel).** For `0 < θ < 1/2`, `E_θ` has: an entire
self-dual completion; nonnegative dual weights carried by prime powers, decaying against `√n`,
representing `-E_θ'/E_θ`; off-line zeros above every height unconditionally; under RH no zero on
the line; and `RH ⟺ zeros on Re s = 1/2 ± θ`. It fails the pole axiom (pole at `1 + θ`). -/
theorem Etheta_shift_control {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) :
    Differentiable ℂ (XiTheta θ) ∧ (∀ s, XiTheta θ (1 - s) = XiTheta θ s) ∧
    (∀ n, 0 ≤ LambdaTheta θ n) ∧ (∀ n, n ≠ 0 → (LambdaTheta θ n ≠ 0 ↔ IsPrimePow n)) ∧
    Tendsto (fun n : ℕ => LambdaTheta θ n / Real.sqrt n) atTop (𝓝 0) ∧
    IsLogDerivCoeff (Etheta θ) (fun n => ((LambdaTheta θ n : ℝ) : ℂ)) ∧
    (∀ T : ℝ, ∃ s : ℂ, XiTheta θ s = 0 ∧ Etheta θ s = 0 ∧ s.re ≠ 1 / 2 ∧ T < s.im) ∧
    (RiemannHypothesis → ∀ s : ℂ, XiTheta θ s = 0 → s.re ≠ 1 / 2) ∧
    (RiemannHypothesis ↔ ∀ s : ℂ, XiTheta θ s = 0 → s.re = 1 / 2 - θ ∨ s.re = 1 / 2 + θ) ∧
    riemannZeta (1 + 2 * θ) ≠ 0 ∧
    Tendsto (fun s : ℂ => (s - (1 + θ)) * Etheta θ s) (𝓝[≠] (1 + θ))
      (𝓝 (riemannZeta (1 + 2 * θ))) := by
  have hθ : θ ≠ 0 := hθ0.ne'
  have habs : |θ| < 1 / 2 := by rw [abs_of_pos hθ0]; exact hθ1
  exact ⟨XiTheta_entire θ, XiTheta_one_sub θ, LambdaTheta_nonneg θ,
    fun n hn => LambdaTheta_ne_zero_iff θ hn, LambdaTheta_weight_tendsto_zero habs,
    (Etheta_isLogDerivCoeff θ).1, Etheta_offline_zeros hθ,
    fun hRH s hs => XiTheta_no_zero_on_line_of_RH hRH hθ hs, RH_iff_XiTheta_two_lines hθ,
    (Etheta_pole hθ0).2, (Etheta_pole hθ0).1⟩

/-! ## F. Finite rank: the Fourier-Laplace dual is tempered iff the configuration is real

The seat's claim 2 (paper proof, class-`C` form): the Fourier-Laplace dual of the zero measure,
`x ↦ Σ m(ρ) e^{i γ_ρ x}` on test functions, is tempered iff every `γ_ρ` is real (RH_F). The
kernel proves the finite-rank form with positive multiplicities: for finitely many points
`γ_j ∈ ℂ`, the exponential sum `Σ m_j e^{i γ_j x}` is polynomially bounded on `ℝ` iff every
`γ_j` is real. No positivity of a dual, no Euler product, no conductor is used, so
"tempered dual" is a relabeling of "real support" for every control alike. Proof: Cesàro means
of `e^{-(d + i t) n} Σ_j m_j e^{i γ_j n}` along `n ∈ ℕ`, `d` the maximal `-Im γ_j`. -/

/-- The Fourier-Laplace dual `x ↦ Σ_j m_j e^{i γ_j x}` of a finite configuration
`Σ_j m_j δ_{γ_j}`, `γ_j ∈ ℂ` (zeros in the coordinate `γ = (ρ - 1/2)/i`). -/
def dualSum {ι : Type*} [Fintype ι] (m : ι → ℝ) (γ : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ j, (m j : ℂ) * Complex.exp (I * γ j * x)

lemma geom_sum_re_lower {q : ℂ} (hq : ‖q‖ ≤ 1) (N : ℕ) :
    -(if q = 1 then 0 else 2 / ‖q - 1‖) ≤ (∑ n ∈ Finset.range N, q ^ n).re := by
  split_ifs with h
  · subst h; simp
  · rw [geom_sum_eq h N]
    have hnorm : ‖(q ^ N - 1) / (q - 1)‖ ≤ 2 / ‖q - 1‖ := by
      rw [norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      calc ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_pow, norm_one]
          have := pow_le_one₀ (norm_nonneg q) hq (n := N)
          linarith
        _ = 2 := by norm_num
    have := Complex.abs_re_le_norm ((q ^ N - 1) / (q - 1))
    have := (abs_le.mp this).1
    linarith

lemma geom_partial_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, r ^ n ≤ 1 / (1 - r) := by
  have h := geom_sum_mul r N
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  have hrN : 0 ≤ r ^ N := pow_nonneg hr0 N
  nlinarith

lemma poly_le_exp_bound {d : ℝ} (hd : 0 < d) (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ k ≤ (k.factorial : ℝ) * Real.exp (d / 2) / (d / 2) ^ k * Real.exp (d / 2 * y) := by
  have hx : 0 ≤ d / 2 * (1 + y) := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hdk : (0 : ℝ) < (d / 2) ^ k := by positivity
  rw [div_le_iff₀ hfac, mul_pow] at h
  have hexp : Real.exp (d / 2 * (1 + y)) = Real.exp (d / 2) * Real.exp (d / 2 * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
  nlinarith

/-- **One-sided finite-rank temperedness (kernel).** If `m_j > 0` and the dual is polynomially
bounded along `n ∈ ℕ`, then no point lies strictly below the real axis: `Im γ_j ≥ 0`. -/
theorem im_nonneg_of_polyBounded_nat {ι : Type*} [Fintype ι] {m : ι → ℝ} (hm : ∀ j, 0 < m j)
    {γ : ι → ℂ} {C : ℝ} {k : ℕ} (hb : ∀ n : ℕ, ‖dualSum m γ n‖ ≤ C * (1 + n) ^ k) :
    ∀ j, 0 ≤ (γ j).im := by
  by_contra hneg
  obtain ⟨j0, hj0⟩ := not_forall.mp hneg
  have hj0' : (γ j0).im < 0 := not_le.mp hj0
  obtain ⟨j1, -, hj1⟩ :=
    Finset.exists_max_image Finset.univ (fun j => -(γ j).im) ⟨j0, Finset.mem_univ _⟩
  set d := -(γ j1).im with hd
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith) (hj1 j0 (Finset.mem_univ _))
  set t := (γ j1).re with ht
  have hC : 0 ≤ C := by
    have h0 := hb 0
    simp only [Nat.cast_zero, add_zero, one_pow, mul_one] at h0
    exact (norm_nonneg _).trans h0
  -- the rotated points z_j and ratios q_j
  set z : ι → ℂ := fun j => I * γ j - d - I * t with hz
  set q : ι → ℂ := fun j => Complex.exp (z j) with hq
  have hzre : ∀ j, (z j).re = -(γ j).im - d := by
    intro j; simp [hz, Complex.mul_re]
  have hqn : ∀ j, ‖q j‖ ≤ 1 := by
    intro j
    rw [hq, Complex.norm_exp, hzre, Real.exp_le_one_iff]
    linarith [hj1 j (Finset.mem_univ _)]
  have hz1 : z j1 = 0 := by
    apply Complex.ext
    · rw [hzre]; simp [hd]
    · simp [hz, Complex.mul_im, ht]
  have hq1 : q j1 = 1 := by simp [hq, hz1]
  -- sampled, rotated dual
  have hterm : ∀ n : ℕ, Complex.exp (-((d : ℂ) + I * t) * n) * dualSum m γ n =
      ∑ j, (m j : ℂ) * q j ^ n := by
    intro n
    unfold dualSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [hz]
    push_cast
    ring
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, ∑ j, (m j : ℂ) * q j ^ n with hS
  -- lower bound on the real part
  set Kc : ι → ℝ := fun j => if q j = 1 then 0 else 2 / ‖q j - 1‖ with hKc
  have hKc0 : ∀ j, 0 ≤ Kc j := by
    intro j; simp only [hKc]; split_ifs <;> positivity
  set K := ∑ j, m j * Kc j with hK
  have hlow : ∀ N : ℕ, m j1 * N - K ≤ (S N).re := by
    intro N
    have hswap : S N = ∑ j, (m j : ℂ) * ∑ n ∈ Finset.range N, q j ^ n := by
      simp only [hS]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    have hre : (S N).re = ∑ j, m j * (∑ n ∈ Finset.range N, q j ^ n).re := by
      rw [hswap, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_ofReal_mul]
    have hnonneg : ∀ j ∈ Finset.univ,
        0 ≤ m j * ((∑ n ∈ Finset.range N, q j ^ n).re + Kc j) := by
      intro j _
      exact mul_nonneg (hm j).le (by linarith [geom_sum_re_lower (hqn j) N])
    have hsingle := Finset.single_le_sum hnonneg (Finset.mem_univ j1)
    have hj1val : (∑ n ∈ Finset.range N, q j1 ^ n).re + Kc j1 = N := by
      simp [hq1, hKc]
    rw [hj1val] at hsingle
    have hsplit : ∑ j, m j * ((∑ n ∈ Finset.range N, q j ^ n).re + Kc j) =
        (S N).re + K := by
      rw [hre, hK, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith
  -- upper bound on the norm
  set r := Real.exp (-(d / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(d / 2) < 0 by linarith)
    rwa [Real.exp_zero] at h
  set B0 := (k.factorial : ℝ) * Real.exp (d / 2) / (d / 2) ^ k with hB0
  have hB0pos : 0 ≤ B0 := by positivity
  have hup : ∀ N : ℕ, ‖S N‖ ≤ C * B0 * (1 / (1 - r)) := by
    intro N
    have hSN : S N = ∑ n ∈ Finset.range N,
        Complex.exp (-((d : ℂ) + I * t) * n) * dualSum m γ n := by
      simp only [hS]
      exact Finset.sum_congr rfl fun n _ => (hterm n).symm
    rw [hSN]
    refine (norm_sum_le _ _).trans ?_
    have hbd : ∀ n ∈ Finset.range N,
        ‖Complex.exp (-((d : ℂ) + I * t) * n) * dualSum m γ n‖ ≤ C * B0 * r ^ n := by
      intro n _
      rw [norm_mul, Complex.norm_exp]
      have hre : (-((d : ℂ) + I * t) * n).re = -(d * n) := by simp
      rw [hre]
      have h1 := hb n
      have h2 := poly_le_exp_bound hdpos k (Nat.cast_nonneg n)
      have hrn : r ^ n = Real.exp (-(d / 2) * n) := by
        rw [hr, ← Real.exp_nat_mul]; ring_nf
      rw [hrn]
      have he : Real.exp (-(d * n)) * Real.exp (d / 2 * n) = Real.exp (-(d / 2) * n) := by
        rw [← Real.exp_add]; ring_nf
      have hexp0 := Real.exp_pos (-(d * n))
      calc Real.exp (-(d * n)) * ‖dualSum m γ n‖
          ≤ Real.exp (-(d * n)) * (C * (1 + n) ^ k) := mul_le_mul_of_nonneg_left h1 hexp0.le
        _ ≤ Real.exp (-(d * n)) * (C * (B0 * Real.exp (d / 2 * n))) := by
          apply mul_le_mul_of_nonneg_left _ hexp0.le
          exact mul_le_mul_of_nonneg_left h2 hC
        _ = C * B0 * (Real.exp (-(d * n)) * Real.exp (d / 2 * n)) := by ring
        _ = C * B0 * Real.exp (-(d / 2) * n) := by rw [he]
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (geom_partial_le hr0 hr1 N) (mul_nonneg hC hB0pos)
  -- contradiction for large N
  obtain ⟨N, hN⟩ := exists_nat_gt ((K + C * B0 * (1 / (1 - r))) / m j1)
  have h1 := hlow N
  have h2 := hup N
  have h3 : (S N).re ≤ ‖S N‖ := by
    have := Complex.abs_re_le_norm (S N)
    exact (le_abs_self _).trans this
  have hmj := hm j1
  rw [div_lt_iff₀ hmj] at hN
  nlinarith

/-- **Finite-rank temperedness = real support (kernel).** For positive multiplicities, the
Fourier-Laplace dual `Σ m_j e^{i γ_j x}` is polynomially bounded on `ℝ` iff every `γ_j` is real. -/
theorem dualSum_polyBounded_iff_real {ι : Type*} [Fintype ι] {m : ι → ℝ} (hm : ∀ j, 0 < m j)
    (γ : ι → ℂ) :
    (∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, ‖dualSum m γ x‖ ≤ C * (1 + |x|) ^ k) ↔ ∀ j, (γ j).im = 0 := by
  constructor
  · rintro ⟨C, k, hb⟩
    have hpos := im_nonneg_of_polyBounded_nat hm (C := C) (k := k) fun n => by
      have := hb n
      rwa [abs_of_nonneg (Nat.cast_nonneg n)] at this
    have hneg := im_nonneg_of_polyBounded_nat hm (γ := fun j => -γ j) (C := C) (k := k)
      fun n => by
        have h := hb (-(n : ℝ))
        rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)] at h
        have heq : dualSum m (fun j => -γ j) n = dualSum m γ (-(n : ℝ)) := by
          unfold dualSum
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 2
          push_cast
          ring
        rw [heq]
        exact h
    intro j
    have h1 := hpos j
    have h2 := hneg j
    simp only [Complex.neg_im] at h2
    linarith
  · intro hreal
    refine ⟨∑ j, m j, 0, fun x => ?_⟩
    rw [pow_zero, mul_one]
    unfold dualSum
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hm j)]
    have : (I * γ j * x).re = 0 := by simp [Complex.mul_re, hreal j]
    rw [this, Real.exp_zero, mul_one]

/-! ## Capstone -/

/-- **Capstone (kernel).** The negative-control battery for FQ-type properties:
(1) DH's dual exists, is signed, and is not carried by prime powers;
(2) W2's factor is Lee-Yang iff `|a| ≤ 1` and an Euler factor iff `a² = 1`;
(3) at finite rank, real zeros ⟺ tempered dual weights, and the golden fake's weights are unbounded;
(4) the shift control `E_θ` keeps every dual-side positivity / support / decay property of `ζ`,
    has off-line zeros above every height, and its correct "RH" is RH for `ζ`;
(5) the Fourier-Laplace dual of a finite positive configuration is tempered iff it is real.
`conjecture1_proved = False`: no item bears on where the zeros of `ζ` lie. -/
theorem negative_control_capstone :
    (∃ g : ℕ → ℂ, IsLogDerivCoeff (LSeries dhCoeff) g ∧ g 6 ≠ 0 ∧ ¬ IsPrimePow 6 ∧
      (g 3).re < 0) ∧
    (∀ a : ℝ, (IsLeeYang2 (LY2 a) ↔ |a| ≤ 1) ∧
      ((∃ u v : ℂ, ∀ z w : ℂ, LY2 a z w = (1 + u * z) * (1 + v * w)) ↔ a ^ 2 = 1)) ∧
    (∀ p c : ℝ, 1 < p →
      ((∀ s : ℂ, Qc p c s = 0 → s.re = 1 / 2) ↔ (∃ M : ℝ, ∀ k : ℕ, |qw c k| ≤ M))) ∧
    (∀ M : ℝ, ∃ k : ℕ, M < |qw (Real.sqrt 5) k|) ∧
    (∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
      (∀ n, 0 ≤ LambdaTheta θ n) ∧
      IsLogDerivCoeff (Etheta θ) (fun n => ((LambdaTheta θ n : ℝ) : ℂ)) ∧
      Tendsto (fun n : ℕ => LambdaTheta θ n / Real.sqrt n) atTop (𝓝 0) ∧
      (∀ T : ℝ, ∃ s : ℂ, XiTheta θ s = 0 ∧ s.re ≠ 1 / 2 ∧ T < s.im) ∧
      (RiemannHypothesis ↔ ∀ s : ℂ, XiTheta θ s = 0 → s.re = 1 / 2 - θ ∨ s.re = 1 / 2 + θ)) ∧
    (∀ (n : ℕ) (m : Fin n → ℝ), (∀ j, 0 < m j) → ∀ γ : Fin n → ℂ,
      ((∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, ‖dualSum m γ x‖ ≤ C * (1 + |x|) ^ k) ↔
        ∀ j, (γ j).im = 0)) := by
  refine ⟨?_, fun a => ⟨LY2_leeYang_iff a, LY2_factor_iff a⟩,
    fun p c hp => (finite_rank_realZeros_iff_tempered_iff_leeYang hp c).1,
    golden_weights_unbounded, fun θ h0 h1 => ?_, fun n m hm γ => dualSum_polyBounded_iff_real hm γ⟩
  · obtain ⟨g, hg, -, h6, hpp, -, h3⟩ := dh_dual_exists
    exact ⟨g, hg, h6, hpp, h3⟩
  · obtain ⟨-, -, hnn, -, hdec, hlog, hoff, -, hRH, -, -⟩ := Etheta_shift_control h0 h1
    exact ⟨hnn, hlog, hdec, fun T => by
      obtain ⟨s, hs, -, hre, hT⟩ := hoff T
      exact ⟨s, hs, hre, hT⟩, hRH⟩

end CruxFQNegControl

#print axioms CruxFQNegControl.exists_isLogDerivCoeff_of_bounded
#print axioms CruxFQNegControl.LogConv.mul_primes
#print axioms CruxFQNegControl.LogConv.mul_primes_eq_zero_iff
#print axioms CruxFQNegControl.not_isPrimePow_mul_primes
#print axioms CruxFQNegControl.dh_dual_values
#print axioms CruxFQNegControl.dh_dual_negative_atom
#print axioms CruxFQNegControl.dh_dual_off_prime_powers
#print axioms CruxFQNegControl.dh_dual_exists
#print axioms CruxFQNegControl.LY2_leeYang_iff
#print axioms CruxFQNegControl.LY2_factor_iff
#print axioms CruxFQNegControl.Ea_zero_re_of_leeYang
#print axioms CruxFQNegControl.W2_LSeries_eq
#print axioms CruxFQNegControl.W2_dual_defect
#print axioms CruxFQNegControl.W2_dual_defect_eq_zero_iff
#print axioms CruxFQNegControl.W2_fooling_instance
#print axioms CruxFQNegControl.W2_dual_exists
#print axioms CruxFQNegControl.qw_bounded_iff
#print axioms CruxFQNegControl.quad_roots_unimodular_iff
#print axioms CruxFQNegControl.Qc_zeros_on_line_iff
#print axioms CruxFQNegControl.finite_rank_realZeros_iff_tempered_iff_leeYang
#print axioms CruxFQNegControl.golden_weights
#print axioms CruxFQNegControl.golden_weights_unbounded
#print axioms CruxFQNegControl.golden_zero_re
#print axioms CruxFQNegControl.golden_factor
#print axioms CruxFQNegControl.golden_count_pos
#print axioms CruxFQNegControl.W1_fails_finite_rank
#print axioms CruxFQNegControl.exists_nontrivial_zero_above
#print axioms CruxFQNegControl.XiTheta_one_sub
#print axioms CruxFQNegControl.XiTheta_eq_completion
#print axioms CruxFQNegControl.XiTheta_zero_re_bounds
#print axioms CruxFQNegControl.Etheta_offline_zeros
#print axioms CruxFQNegControl.eisShift_violates_RH_analogue_unconditional
#print axioms CruxFQNegControl.XiTheta_no_zero_on_line_of_RH
#print axioms CruxFQNegControl.RH_iff_XiTheta_two_lines
#print axioms CruxFQNegControl.LambdaTheta_eq_cosh
#print axioms CruxFQNegControl.LambdaTheta_ne_zero_iff
#print axioms CruxFQNegControl.Etheta_logDeriv_hasSum
#print axioms CruxFQNegControl.Etheta_isLogDerivCoeff
#print axioms CruxFQNegControl.LambdaTheta_weight_tendsto_zero
#print axioms CruxFQNegControl.Etheta_pole
#print axioms CruxFQNegControl.Etheta_shift_control
#print axioms CruxFQNegControl.im_nonneg_of_polyBounded_nat
#print axioms CruxFQNegControl.dualSum_polyBounded_iff_real
#print axioms CruxFQNegControl.negative_control_capstone
