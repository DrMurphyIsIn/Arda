/-
  FamilyWeilDigamma -- the digamma weight of a general gamma shift, psiShift mu r =
  Re psi((1 + 2 mu)/4 + i r/2), and in particular the SECOND digamma psiShift 1 = Re psi(3/4 + i r/2)
  of the factor Gamma_R(s + 1) carried by the imaginary quadratic members (Stage 1a of the
  quadratic-family programme, 2026-09-25).

  Every bound the island provides for psiR = psiShift 0 (E6Bridge11: the constant floor and the
  Stirling floor 2 at |r| >= 41; E6Bridge30: evenness, monotonicity in |r|, the vertical-line series
  with the integral tail and the RATIONAL lower bound psiR_ge_rational; E6Bridge32: the finite
  Lorentzian minorant psiR_ge_finite and the pairing of hsq against it; ZhuEnvelope / ZhuTail: the
  sharp Stirling envelopes) is reproved here for an ADMISSIBLE shift mu, i.e. one whose abscissa
  a = (1 + 2 mu)/4 lies in (0, 1) (ShiftOK: -1/2 < mu < 3/2, covering mu = 0 and mu = 1), from the
  same Zeta23 inputs (MuFields.re_digamma_vertical, re_digamma_mono, summable_re_terms,
  StirlingVert.digamma_stirling, re_digamma_stirling'):
    * psiShift_eq_series      the vertical-line series at abscissa a (serFa a, the a = 1/4 case is
                              E6Bridge30's serF);
    * psiShift_ge_series / psiShift_ge_rational   the lower truncation with the integral tail
                              G(N) - G(N + M) and its rational form (N terms, tail M);
    * psiShift_le_series / psiShift_le_rational   the UPPER truncation (N + 1 terms, tail <= G(N));
                              mirrors CF_Arch.re_digamma_le (origin/cl/counterfeit-ladder, read only,
                              NOT imported), reproved with the integral tail instead of the
                              1/n^2 + 1/n^3 majorants;
    * psiShift_ge_finite      the finite Lorentzian minorant (E6Bridge32 shape, abscissae bShift);
    * psiShift_ge_const, psiShift_neg, psiShift_abs, psiShift_mono, continuous_psiShift;
    * psiShift_stirling / psiShift_ge_log / psiShift_le_log    |psiShift - log(|r|/2)| <= 20/r^2
                              for |r| >= 1;
    * psiShift_ge_stirling / psiShift_le_stirling   the sharp envelopes log(t/2) -+ (12 + 2a)/t^2
                              and log(t/2) + (12 + 2a^2)/t^2 for t >= 1 (ZhuEnvelope / ZhuTail
                              shape);
    * psiShift_le_psiR_add    psiShift mu <= psiR + 10 everywhere, hence
      integrable_mul_psiShift / integrable_hsq_mul_psiShift   the second digamma is integrable
                              against |ĝ|^2 (what the symbol representation needs);
    * phiShift, integrable_hsq_mul_phiShift, integral_hsq_mul_phiShift,
      integral_hsq_mul_psiShift_ge   the finite minorant paired with hsq through E6Bridge32's
                              exponential-kernel pairings.
  Instances at mu = 1 (psiD_*): the series, the floors -2 and 2 (|r| >= 41), the rational two-sided
  enclosures, and kernel-checkable (norm_num) floors / ceilings at r = 0, 1, 2, 4, 8, 16 (N = 40
  series terms, tail M = 10^6, gamma in [0.5733, 0.58112]).

  Nothing about positivity is proved.  conjecture1_proved = False.
-/
import FamilyWeilQuad
import E6Bridge32
import ZhuEnvelope

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace FamilyWeil
open WeilExplicit RvMBridge11 RvMBridge30 RvMBridge31 RvMBridge32

/-! ## A. Admissible shifts and the abscissa. -/

/-- A shift `mu` is admissible when its abscissa `a = (1 + 2 mu)/4` lies in `(0, 1)`. -/
def ShiftOK (μ : ℝ) : Prop := -1 / 2 < μ ∧ μ < 3 / 2

/-- The abscissa `a = (1 + 2 mu)/4` of the factor `Gamma_R(s + mu)` on the critical line. -/
def absc (μ : ℝ) : ℝ := (1 + 2 * μ) / 4

lemma absc_pos {μ : ℝ} (h : ShiftOK μ) : 0 < absc μ := by unfold absc; linarith [h.1]
lemma absc_lt_one {μ : ℝ} (h : ShiftOK μ) : absc μ < 1 := by unfold absc; linarith [h.2]
lemma shiftOK_zero : ShiftOK 0 := ⟨by norm_num, by norm_num⟩
lemma shiftOK_one : ShiftOK 1 := ⟨by norm_num, by norm_num⟩
lemma shiftOK_muOf (neg : Bool) : ShiftOK (muOf neg) := by
  cases neg <;> simp [muOf, shiftOK_zero, shiftOK_one]
lemma absc_zero : absc 0 = 1 / 4 := by unfold absc; norm_num
lemma absc_one : absc 1 = 3 / 4 := by unfold absc; norm_num

/-- `psiShift` in Zeta23's vertical-line spelling `Re psi(a + i t)`, `t = r/2`. -/
lemma psiShift_eq (μ r : ℝ) :
    psiShift μ r = (Complex.digamma ((absc μ : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re := by
  unfold psiShift absc
  congr 2
  push_cast
  ring

/-! ## B. The vertical-line series at a general abscissa. -/

/-- `f_a(t, x) = 1/(x+1) - (x+1+a)/((x+1+a)^2 + t^2)` (E6Bridge30's `serF` is `a = 1/4`). -/
def serFa (a t x : ℝ) : ℝ := 1 / (x + 1) - (x + 1 + a) / ((x + 1 + a) ^ 2 + t ^ 2)

/-- Minus an antiderivative of `f_a`: `G_a(t, x) = (1/2) log((x+1+a)^2 + t^2) - log(x+1)`. -/
def serGa (a t x : ℝ) : ℝ := (1 / 2) * Real.log ((x + 1 + a) ^ 2 + t ^ 2) - Real.log (x + 1)

lemma serFa_quarter (t x : ℝ) : serFa (1 / 4) t x = serF t x := rfl

/-- The vertical-line series (Zeta23 `re_digamma_vertical`) at the abscissa of the shift. -/
theorem psiShift_eq_series {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) :
    psiShift μ r = -Real.eulerMascheroniConstant - absc μ / (absc μ ^ 2 + (r / 2) ^ 2)
      + ∑' n : ℕ, serFa (absc μ) (r / 2) n := by
  rw [psiShift_eq, Zeta23.MuFields.re_digamma_vertical (absc_pos hμ) (absc_lt_one hμ)]
  rfl

lemma summable_serFa {μ : ℝ} (hμ : ShiftOK μ) (t : ℝ) :
    Summable (fun n : ℕ => serFa (absc μ) t n) :=
  Zeta23.MuFields.summable_re_terms (absc_pos hμ) (absc_lt_one hμ) t

lemma serFa_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ serFa a t x := by
  unfold serFa
  have hn : (0 : ℝ) < x + 1 + a := by linarith
  have h1 : (x + 1 + a) / ((x + 1 + a) ^ 2 + t ^ 2) ≤ 1 / (x + 1 + a) := by
    rw [div_le_div_iff₀ (by positivity) hn]
    nlinarith [sq_nonneg t]
  have h2 : 1 / (x + 1 + a) ≤ 1 / (x + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

/-- `f_a(t, ·)` is decreasing on `[0, ∞)`. -/
lemma serFa_antitoneOn {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : AntitoneOn (serFa a t) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  set p := x + 1 + a with hp
  set q := y + 1 + a with hq
  have hp0 : 0 < p := by rw [hp]; linarith
  have hq0 : 0 < q := by rw [hq]; linarith
  have hP : 0 < p ^ 2 + t ^ 2 := by positivity
  have hQ : 0 < q ^ 2 + t ^ 2 := by positivity
  have hnum : 0 ≤ (p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2) - (x + 1) * (y + 1) * (p * q - t ^ 2) := by
    rcases le_or_gt (p * q) (t ^ 2) with h | h
    · nlinarith [mul_pos hx1 hy1, mul_pos hP hQ]
    · have h1 : (x + 1) * (y + 1) ≤ p * q := by
        rw [hp, hq]
        nlinarith [mul_nonneg ha hx1.le, mul_nonneg ha hy1.le, sq_nonneg a]
      have h2 : (x + 1) * (y + 1) * (p * q - t ^ 2) ≤ p * q * (p * q - t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg p), mul_nonneg (sq_nonneg t) (sq_nonneg q),
        mul_nonneg (sq_nonneg t) (mul_pos hp0 hq0).le, sq_nonneg (t ^ 2)]
  have hid : serFa a t x - serFa a t y
      = (y - x) * ((p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2) - (x + 1) * (y + 1) * (p * q - t ^ 2))
        / ((x + 1) * (y + 1) * ((p ^ 2 + t ^ 2) * (q ^ 2 + t ^ 2))) := by
    unfold serFa
    rw [← hp, ← hq]
    field_simp
    ring
  have : 0 ≤ serFa a t x - serFa a t y := by
    rw [hid]
    apply div_nonneg (mul_nonneg (by linarith) hnum)
    positivity
  linarith

lemma hasDerivAt_neg_serGa {a : ℝ} (ha : 0 ≤ a) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x => -serGa a t x) (serFa a t x) x := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hq : (x + 1 + a) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x + 1 + a) 1 x :=
    ((hasDerivAt_id x).add_const 1).add_const a
  have h2 : HasDerivAt (fun x : ℝ => (x + 1 + a) ^ 2 + t ^ 2) (2 * (x + 1 + a)) x := by
    have h := (h1.pow 2).add_const (t ^ 2)
    refine h.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun x : ℝ => Real.log ((x + 1 + a) ^ 2 + t ^ 2))
      (2 * (x + 1 + a) / ((x + 1 + a) ^ 2 + t ^ 2)) x := h2.log hq
  have h4 : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (x + 1)) x := by
    have := ((hasDerivAt_id x).add_const 1).log hx1
    simpa using this
  have h5 := ((h3.const_mul (1 / 2)).sub h4).neg
  have h6 : HasDerivAt (fun x => -serGa a t x)
      (-((1 / 2) * (2 * (x + 1 + a) / ((x + 1 + a) ^ 2 + t ^ 2)) - 1 / (x + 1))) x := by
    unfold serGa
    exact h5
  refine h6.congr_deriv ?_
  unfold serFa
  field_simp
  ring

lemma integral_serFa_eq {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (N M : ℕ) :
    ∫ x in (N : ℝ)..((N + M : ℕ) : ℝ), serFa a t x = serGa a t N - serGa a t (N + M) := by
  have hNM : (N : ℝ) ≤ ((N + M : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hanti : AntitoneOn (serFa a t) (Set.Icc (N : ℝ) ((N + M : ℕ) : ℝ)) :=
    (serFa_antitoneOn ha t).mono fun x hx => by
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -serGa a t x)
    (f' := serFa a t) (a := (N : ℝ)) (b := ((N + M : ℕ) : ℝ))
    (fun x hx => by
      rw [Set.uIcc_of_le hNM, Set.mem_Icc] at hx
      exact hasDerivAt_neg_serGa ha t (by linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
    (by
      rw [← Set.uIcc_of_le hNM] at hanti
      exact hanti.intervalIntegrable)
  rw [h]
  push_cast
  ring

/-- The tail comparison from below: `G(N) - G(N + M) <= Σ_{n ∈ [N, N+M)} f(n)`. -/
lemma sum_serFa_ge {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (N M : ℕ) :
    serGa a t N - serGa a t (N + M) ≤ ∑ n ∈ Finset.Ico N (N + M), serFa a t n := by
  have hanti : AntitoneOn (serFa a t) (Set.Icc (N : ℝ) ((N + M : ℕ) : ℝ)) :=
    (serFa_antitoneOn ha t).mono fun x hx => by
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h1 := AntitoneOn.integral_le_sum_Ico (f := serFa a t) (a := N) (b := N + M) (by omega) hanti
  rw [integral_serFa_eq ha t N M] at h1
  exact h1

/-- The tail comparison from above: `Σ_{m < M} f(N + m + 1) <= G(N) - G(N + M)`. -/
lemma sum_serFa_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (N M : ℕ) :
    ∑ m ∈ Finset.range M, serFa a t ((N + m + 1 : ℕ) : ℝ) ≤ serGa a t N - serGa a t (N + M) := by
  have hanti : AntitoneOn (serFa a t) (Set.Icc (N : ℝ) ((N + M : ℕ) : ℝ)) :=
    (serFa_antitoneOn ha t).mono fun x hx => by
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      linarith [hx.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h1 := AntitoneOn.sum_le_integral_Ico (f := serFa a t) (a := N) (b := N + M) (by omega) hanti
  rw [integral_serFa_eq ha t N M, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h1
  exact h1

/-- The two log bounds on `G`:
`(1/2)(1 - (x+1)^2/((x+1+a)^2+t^2)) <= G(x) <= (1/2)(((x+1+a)^2+t^2)/(x+1)^2 - 1)`. -/
lemma serGa_bounds {a : ℝ} (ha : 0 ≤ a) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2) * (1 - (x + 1) ^ 2 / ((x + 1 + a) ^ 2 + t ^ 2)) ≤ serGa a t x
      ∧ serGa a t x ≤ (1 / 2) * (((x + 1 + a) ^ 2 + t ^ 2) / (x + 1) ^ 2 - 1) := by
  unfold serGa
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1 + a) ^ 2 + t ^ 2 := by positivity
  have e : (1 / 2) * Real.log ((x + 1 + a) ^ 2 + t ^ 2) - Real.log (x + 1)
      = (1 / 2) * Real.log (((x + 1 + a) ^ 2 + t ^ 2) / (x + 1) ^ 2) := by
    rw [Real.log_div hq.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  have hpos : 0 < ((x + 1 + a) ^ 2 + t ^ 2) / (x + 1) ^ 2 := by positivity
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hpos
    rw [inv_div] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    linarith

lemma serGa_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ serGa a t x := by
  have h := (serGa_bounds ha t hx).1
  have hle : (x + 1) ^ 2 / ((x + 1 + a) ^ 2 + t ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg t, mul_nonneg ha (by linarith : (0 : ℝ) ≤ x + 1), sq_nonneg a]
  linarith

/-- THE SERIES LOWER BOUND at a general admissible shift (E6Bridge30 `psiR_ge_series` shape). -/
theorem psiShift_ge_series {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) (N M : ℕ) :
    -Real.eulerMascheroniConstant - absc μ / (absc μ ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serFa (absc μ) (r / 2) n
      + (serGa (absc μ) (r / 2) N - serGa (absc μ) (r / 2) (N + M)) ≤ psiShift μ r := by
  rw [psiShift_eq_series hμ]
  have ha := (absc_pos hμ).le
  have hsum := summable_serFa hμ (r / 2)
  have hnn : ∀ n : ℕ, 0 ≤ serFa (absc μ) (r / 2) n :=
    fun n => serFa_nonneg ha _ (Nat.cast_nonneg n)
  have h1 : ∑ n ∈ Finset.range (N + M), serFa (absc μ) (r / 2) n
      ≤ ∑' n : ℕ, serFa (absc μ) (r / 2) n :=
    hsum.sum_le_tsum _ (fun n _ => hnn n)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N M),
    ← Finset.range_eq_Ico] at h1
  have h2 := sum_serFa_ge ha (r / 2) N M
  linarith

/-- THE SERIES UPPER BOUND: `N + 1` terms, the tail bounded by `G(N)` (mirrors CF_Arch's
`re_digamma_le`, with the integral tail in place of the `a/N + t^2/(2N^2)` majorant). -/
theorem psiShift_le_series {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) (N : ℕ) :
    psiShift μ r ≤ -Real.eulerMascheroniConstant - absc μ / (absc μ ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range (N + 1), serFa (absc μ) (r / 2) n + serGa (absc μ) (r / 2) N := by
  rw [psiShift_eq_series hμ]
  have ha := (absc_pos hμ).le
  have hsum := summable_serFa hμ (r / 2)
  rw [← hsum.sum_add_tsum_nat_add (N + 1)]
  have htail : ∑' m : ℕ, serFa (absc μ) (r / 2) ((m + (N + 1) : ℕ) : ℝ)
      ≤ serGa (absc μ) (r / 2) N := by
    apply Real.tsum_le_of_sum_range_le (fun m => serFa_nonneg ha _ (Nat.cast_nonneg _))
    intro M
    have h := sum_serFa_le ha (r / 2) N M
    have hG := serGa_nonneg ha (r / 2) (x := ((N : ℝ) + M)) (by positivity)
    have e : ∑ m ∈ Finset.range M, serFa (absc μ) (r / 2) ((m + (N + 1) : ℕ) : ℝ)
        = ∑ m ∈ Finset.range M, serFa (absc μ) (r / 2) ((N + m + 1 : ℕ) : ℝ) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      push_cast
      ring
    rw [e]
    linarith
  linarith

/-- THE RATIONAL LOWER BOUND: every quantity on the left is rational once `r`, `N`, `M`, `gamma_up`
and the abscissa are (E6Bridge30 `psiR_ge_rational` shape). -/
theorem psiShift_ge_rational {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) (N M : ℕ) {γ : ℝ}
    (hγ : Real.eulerMascheroniConstant ≤ γ) :
    -γ - absc μ / (absc μ ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serFa (absc μ) (r / 2) n
      + (1 / 2) * (1 - ((N : ℝ) + 1) ^ 2 / (((N : ℝ) + 1 + absc μ) ^ 2 + (r / 2) ^ 2))
      - (1 / 2) * (((((N : ℝ) + M) + 1 + absc μ) ^ 2 + (r / 2) ^ 2) / (((N : ℝ) + M + 1) ^ 2) - 1)
      ≤ psiShift μ r := by
  have h := psiShift_ge_series hμ r N M
  have ha := (absc_pos hμ).le
  have hN := (serGa_bounds ha (r / 2) (x := (N : ℝ)) (Nat.cast_nonneg N)).1
  have hNM := (serGa_bounds ha (r / 2) (x := ((N : ℝ) + M)) (by positivity)).2
  linarith

/-- THE RATIONAL UPPER BOUND (`N + 1` terms, `gamma_lo <= gamma`). -/
theorem psiShift_le_rational {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) (N : ℕ) {γ : ℝ}
    (hγ : γ ≤ Real.eulerMascheroniConstant) :
    psiShift μ r ≤ -γ - absc μ / (absc μ ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range (N + 1), serFa (absc μ) (r / 2) n
      + (1 / 2) * ((((N : ℝ) + 1 + absc μ) ^ 2 + (r / 2) ^ 2) / ((N : ℝ) + 1) ^ 2 - 1) := by
  have h := psiShift_le_series hμ r N
  have ha := (absc_pos hμ).le
  have hN := (serGa_bounds ha (r / 2) (x := (N : ℝ)) (Nat.cast_nonneg N)).2
  linarith

/-! ## C. The finite Lorentzian minorant (E6Bridge32 shape). -/

/-- The `a`-term of the series is the Lorentzian of abscissa `2a`. -/
lemma absc_term_eq_lor {a : ℝ} (ha : 0 < a) (r : ℝ) :
    a / (a ^ 2 + (r / 2) ^ 2) = lor (2 * a) r := by
  unfold lor
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `f_a(r/2, n) = 1/(n+1) - lor(2(n+1+a)) r`. -/
lemma serFa_eq_lor {a : ℝ} (ha : 0 ≤ a) (r : ℝ) (n : ℕ) :
    serFa a (r / 2) n = 1 / ((n : ℝ) + 1) - lor (2 * ((n : ℝ) + 1 + a)) r := by
  unfold serFa lor
  have h1 : ((n : ℝ) + 1 + a) ^ 2 + (r / 2) ^ 2 ≠ 0 := by positivity
  have h2 : (2 * ((n : ℝ) + 1 + a)) ^ 2 + r ^ 2 ≠ 0 := by positivity
  rw [sub_eq_sub_iff_sub_eq_sub, sub_self, eq_comm, sub_eq_zero, div_eq_div_iff h1 h2]
  ring

/-- The `n`-th Lorentzian abscissa of the series at shift `mu`: `2(n + 1 + a)`
(`2n + 5/2` at `mu = 0`, E6Bridge32's `bN`; `2n + 7/2` at `mu = 1`). -/
def bShift (μ : ℝ) (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1 + absc μ)

lemma bShift_pos {μ : ℝ} (hμ : ShiftOK μ) (n : ℕ) : 0 < bShift μ n := by
  unfold bShift; have := absc_pos hμ; positivity

lemma bShift_zero (n : ℕ) : bShift 0 n = bN n := by
  unfold bShift bN; rw [absc_zero]; ring

lemma bShift_one (n : ℕ) : bShift 1 n = 2 * n + 7 / 2 := by
  unfold bShift; rw [absc_one]; ring

/-- The finite Lorentzian minorant (E6Bridge32 `psiR_ge_finite` shape). -/
theorem psiShift_ge_finite {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant - lor (2 * absc μ) r
      + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - lor (bShift μ n) r) ≤ psiShift μ r := by
  have h := psiShift_ge_series hμ r N 0
  simp only [Nat.cast_zero, add_zero, sub_self] at h
  rw [absc_term_eq_lor (absc_pos hμ)] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  exact Finset.sum_congr rfl fun n _ => (serFa_eq_lor (absc_pos hμ).le r n).symm

/-! ## D. Constant floor, parity, monotonicity, continuity, Stirling. -/

/-- The constant floor `-gamma - 1/a` (the `a = 1/4` case is E6Bridge11's `-5`). -/
theorem psiShift_ge_const {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) :
    -Real.eulerMascheroniConstant - 1 / absc μ ≤ psiShift μ r := by
  rw [psiShift_eq_series hμ]
  have ha := absc_pos hμ
  have hsum : 0 ≤ ∑' n : ℕ, serFa (absc μ) (r / 2) n :=
    tsum_nonneg fun n => serFa_nonneg ha.le _ (Nat.cast_nonneg n)
  have hfrac : absc μ / (absc μ ^ 2 + (r / 2) ^ 2) ≤ 1 / absc μ := by
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith [sq_nonneg (r / 2)]
  linarith

theorem psiShift_neg {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) : psiShift μ (-r) = psiShift μ r := by
  rw [psiShift_eq_series hμ, psiShift_eq_series hμ]
  simp only [serFa, neg_div, neg_sq]

theorem psiShift_abs {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) : psiShift μ |r| = psiShift μ r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiShift_neg hμ]

/-- Monotone in `|r|` (E6Bridge30 `psiR_mono` shape). -/
theorem psiShift_mono {μ : ℝ} (hμ : ShiftOK μ) {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ |r|) :
    psiShift μ s ≤ psiShift μ r := by
  rw [← psiShift_abs hμ r, psiShift_eq, psiShift_eq]
  exact Zeta23.MuFields.re_digamma_mono (absc_pos hμ) (absc_lt_one hμ)
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ s / 2))
    (Set.mem_Ici.mpr (by positivity : (0 : ℝ) ≤ |r| / 2)) (by linarith)

lemma continuous_psiShift {μ : ℝ} (hμ : ShiftOK μ) : Continuous (psiShift μ) := by
  unfold psiShift
  apply Complex.continuous_re.comp
  refine continuous_iff_continuousAt.mpr fun r => ?_
  have hz : ((((1 + 2 * μ) / 4 : ℝ) : ℂ) + ((r : ℂ) / 2) * I) ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have hre : ((k : ℂ)).re = ((((1 + 2 * μ) / 4 : ℝ) : ℂ) + ((r : ℂ) / 2) * I).re :=
      congrArg Complex.re hk
    simp at hre
    have h1 := hμ.1
    have h2 := hμ.2
    have hk0 : (0 : ℤ) < k := by exact_mod_cast (by linarith : (0 : ℝ) < k)
    have hk1 : k < (1 : ℤ) := by exact_mod_cast (by linarith : (k : ℝ) < 1)
    omega
  have hf : Continuous (fun r : ℝ => ((((1 + 2 * μ) / 4 : ℝ) : ℂ) + ((r : ℂ) / 2) * I)) := by
    fun_prop
  exact ContinuousAt.comp (g := Complex.digamma)
    (f := fun r : ℝ => ((((1 + 2 * μ) / 4 : ℝ) : ℂ) + ((r : ℂ) / 2) * I))
    (Zeta23.Stirling.differentiableAt_digamma hz).continuousAt hf.continuousAt

/-- Stirling on the vertical line: `|psiShift mu r - log(|r|/2)| <= 20/r^2` for `|r| >= 1`. -/
theorem psiShift_stirling {μ : ℝ} (hμ : ShiftOK μ) {r : ℝ} (hr : 1 ≤ |r|) :
    |psiShift μ r - Real.log (|r| / 2)| ≤ 20 / r ^ 2 := by
  rw [psiShift_eq]
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have ht : 1 / 2 ≤ |r / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' (absc_pos hμ) (absc_lt_one hμ).le ht
  rw [abs_div, abs_two] at h
  have e : 5 / (r / 2) ^ 2 = 20 / r ^ 2 := by field_simp; ring
  rw [e] at h
  exact h

theorem psiShift_ge_log {μ : ℝ} (hμ : ShiftOK μ) {r : ℝ} (hr : 1 ≤ |r|) :
    Real.log (|r| / 2) - 20 / r ^ 2 ≤ psiShift μ r := by
  have := (abs_le.mp (psiShift_stirling hμ hr)).1
  linarith

theorem psiShift_le_log {μ : ℝ} (hμ : ShiftOK μ) {r : ℝ} (hr : 1 ≤ |r|) :
    psiShift μ r ≤ Real.log (|r| / 2) + 20 / r ^ 2 := by
  have := (abs_le.mp (psiShift_stirling hμ hr)).2
  linarith

/-- The second digamma is controlled by the first: `psiShift mu <= psiR + 10` everywhere. -/
theorem psiShift_le_psiR_add {μ : ℝ} (hμ : ShiftOK μ) (r : ℝ) : psiShift μ r ≤ psiR r + 10 := by
  rcases le_or_gt 2 |r| with h | h
  · have h1 := psiShift_le_log hμ (by linarith : 1 ≤ |r|)
    have h2 := psiR_ge_log h
    have hr2 : (4 : ℝ) ≤ r ^ 2 := by
      have := sq_abs r
      nlinarith
    have h3 : 20 / r ^ 2 ≤ 5 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · have h1 : psiShift μ r ≤ psiShift μ 2 := by
      rw [← psiShift_abs hμ r]
      exact psiShift_mono hμ (abs_nonneg r) (by rw [abs_two]; exact h.le)
    have h2 := psiShift_le_log hμ (r := 2) (by rw [abs_two]; norm_num)
    have h3 := psiR_ge r
    rw [abs_two] at h2
    norm_num at h2
    linarith

/-- Integrability of the second digamma against any nonnegative integrable weight `F` against which
`psiR` is integrable (the weight of the symbol representation: `F = |ĝ|^2`). -/
theorem integrable_mul_psiShift {F : ℝ → ℝ} (hF : Integrable F) (hF0 : ∀ r, 0 ≤ F r)
    (hFpsi : Integrable (fun r => F r * psiR r)) {μ : ℝ} (hμ : ShiftOK μ) :
    Integrable (fun r => F r * psiShift μ r) := by
  have hc : Continuous (psiShift μ) := continuous_psiShift hμ
  set C : ℝ := Real.eulerMascheroniConstant + 1 / absc μ + 10 with hC
  have h1 : Integrable (fun r => F r * |psiR r|) := by
    refine hFpsi.abs.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [abs_mul, abs_of_nonneg (hF0 r)]
  have hdom := h1.add (hF.const_mul C)
  refine hdom.mono' (hF.aestronglyMeasurable.mul hc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF0 r)]
  have hlo := psiShift_ge_const hμ r
  have hhi := psiShift_le_psiR_add hμ r
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hinv : 0 < 1 / absc μ := one_div_pos.mpr (absc_pos hμ)
  have habs0 := abs_nonneg (psiR r)
  have hab : |psiShift μ r| ≤ |psiR r| + C := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (psiR r)
      rw [hC]
      linarith
    · have := le_abs_self (psiR r)
      rw [hC]
      linarith
  calc F r * |psiShift μ r| ≤ F r * (|psiR r| + C) := mul_le_mul_of_nonneg_left hab (hF0 r)
    _ = F r * |psiR r| + C * F r := by ring

/-- `|ĝ|^2 psiShift mu` is integrable for every Weil test `g`. -/
theorem integrable_hsq_mul_psiShift {g : ℝ → ℂ} (hg : IsWeilTest g) {μ : ℝ} (hμ : ShiftOK μ) :
    Integrable (fun r => hsq g r * psiShift μ r) :=
  integrable_mul_psiShift (integrable_hsq hg) (fun r => by unfold hsq; positivity)
    (integrable_hsq_mul_psiR hg) hμ

/-- The sharp Stirling floor: `log(t/2) - (12 + 2a)/t^2 <= psiShift mu t` for `t >= 1`
(ZhuEnvelope `psiR_ge_stirling` shape). -/
theorem psiShift_ge_stirling {μ : ℝ} (hμ : ShiftOK μ) {t : ℝ} (ht : 1 ≤ t) :
    Real.log (t / 2) - (12 + 2 * absc μ) / t ^ 2 ≤ psiShift μ t := by
  have ht0 : 0 < t := by linarith
  have ha := absc_pos hμ
  rw [psiShift_eq]
  set w : ℂ := (absc μ : ℂ) + I * ((t / 2 : ℝ) : ℂ) with hw
  have hwre : w.re = absc μ := by simp [hw]
  have hwim : w.im = t / 2 := by simp [hw]
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w) (by rw [hwre]; exact ha)
    (by rw [hwim, abs_of_pos (by linarith)]; linarith)
  rw [hwim] at hst
  have hrem : -(3 / (t / 2) ^ 2) ≤ (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
    have h2 := (abs_le.mp (h1.trans hst)).1
    linarith
  have hlog : Real.log (t / 2) ≤ (Complex.log w).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by positivity)
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos (by positivity)] at this
    exact this
  have hinv : ((1 / 2 : ℂ) / w).re = (absc μ / 2) / (absc μ ^ 2 + (t / 2) ^ 2) := by
    rw [Complex.div_re, Complex.normSq_apply, hwre, hwim]
    simp
    ring
  have hinv_le : (absc μ / 2) / (absc μ ^ 2 + (t / 2) ^ 2) ≤ 2 * absc μ / t ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (absc μ), sq_nonneg t, mul_pos ha ht0]
  have e3 : 3 / (t / 2) ^ 2 = 12 / t ^ 2 := by field_simp; ring
  have hsplit : (Complex.digamma w).re
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re
        + (Complex.log w).re - ((1 / 2 : ℂ) / w).re := by
    simp only [Complex.add_re, Complex.sub_re]
    ring
  have e4 : (12 + 2 * absc μ) / t ^ 2 = 12 / t ^ 2 + 2 * absc μ / t ^ 2 := by ring
  rw [hsplit, hinv]
  linarith

/-- The sharp Stirling ceiling: `psiShift mu t <= log(t/2) + (12 + 2a^2)/t^2` for `t >= 1`
(ZhuTail `psiR_le_stirling` shape). -/
theorem psiShift_le_stirling {μ : ℝ} (hμ : ShiftOK μ) {t : ℝ} (ht : 1 ≤ t) :
    psiShift μ t ≤ Real.log (t / 2) + (12 + 2 * absc μ ^ 2) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ha := absc_pos hμ
  rw [psiShift_eq]
  set w : ℂ := (absc μ : ℂ) + I * ((t / 2 : ℝ) : ℂ) with hw
  have hwre : w.re = absc μ := by simp [hw]
  have hwim : w.im = t / 2 := by simp [hw]
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w) (by rw [hwre]; exact ha)
    (by rw [hwim, abs_of_pos (by linarith)]; linarith)
  rw [hwim] at hst
  have hrem : (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re ≤ 3 / (t / 2) ^ 2 := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
    exact (le_abs_self _).trans (h1.trans hst)
  have hlog : (Complex.log w).re ≤ Real.log (t / 2) + 2 * absc μ ^ 2 / t ^ 2 := by
    rw [Complex.log_re]
    have hn : ‖w‖ ^ 2 = absc μ ^ 2 + t ^ 2 / 4 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by rw [h] at hwre; simp at hwre; linarith)
    have e : Real.log ‖w‖ = (1 / 2) * Real.log (‖w‖ ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [e, hn, show absc μ ^ 2 + t ^ 2 / 4 = (t / 2) ^ 2 * (1 + 4 * absc μ ^ 2 / t ^ 2) by
        field_simp; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl : Real.log (1 + 4 * absc μ ^ 2 / t ^ 2) ≤ 4 * absc μ ^ 2 / t ^ 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 4 * absc μ ^ 2 / t ^ 2)
      linarith
    have h8 : 2 * absc μ ^ 2 / t ^ 2 = (1 / 2) * (4 * absc μ ^ 2 / t ^ 2) := by ring
    push_cast
    linarith
  have hinv : 0 ≤ ((1 / 2 : ℂ) / w).re := by
    rw [Complex.div_re, Complex.normSq_apply, hwre, hwim]
    simp
    positivity
  have hsplit : (Complex.digamma w).re
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re
        + (Complex.log w).re - ((1 / 2 : ℂ) / w).re := by
    simp only [Complex.add_re, Complex.sub_re]; ring
  have e3 : 3 / (t / 2) ^ 2 = 12 / t ^ 2 := by field_simp; ring
  have e4 : (12 + 2 * absc μ ^ 2) / t ^ 2 = 12 / t ^ 2 + 2 * absc μ ^ 2 / t ^ 2 := by ring
  rw [hsplit]
  linarith

/-! ## E. The finite minorant paired with `|ĝ|^2` (E6Bridge32 `phiN` shape). -/

/-- The truncated weight `φ_{mu,N}(r)`. -/
def phiShift (μ : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant - lor (2 * absc μ) r
    + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - lor (bShift μ n) r)

lemma phiShift_le_psiShift {μ : ℝ} (hμ : ShiftOK μ) (N : ℕ) (r : ℝ) :
    phiShift μ N r ≤ psiShift μ r :=
  psiShift_ge_finite hμ r N

lemma hsq_mul_phiShift_eq (g : ℝ → ℂ) (μ : ℝ) (N : ℕ) :
    (fun r : ℝ => hsq g r * phiShift μ N r)
      = fun r => (-Real.eulerMascheroniConstant) * hsq g r - hsq g r * lor (2 * absc μ) r
        + ∑ n ∈ Finset.range N, ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r) := by
  funext r
  unfold phiShift
  rw [mul_add, Finset.mul_sum]
  have hin : ∀ n ∈ Finset.range N, hsq g r * (1 / ((n : ℝ) + 1) - lor (bShift μ n) r)
      = (1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r := fun n _ => by ring
  rw [Finset.sum_congr rfl hin]
  ring

lemma integrable_hsq_mul_phiShift {g : ℝ → ℂ} (hg : IsWeilTest g) {μ : ℝ} (hμ : ShiftOK μ)
    (N : ℕ) : Integrable (fun r : ℝ => hsq g r * phiShift μ N r) := by
  have hh := integrable_hsq hg
  have ha := absc_pos hμ
  rw [hsq_mul_phiShift_eq]
  have hA : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r
      - hsq g r * lor (2 * absc μ) r) :=
    (hh.const_mul _).sub (integrable_hsq_mul_lor hg (by positivity))
  have hB : Integrable (fun r : ℝ => ∑ n ∈ Finset.range N,
      ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r)) :=
    integrable_finsetSum _ fun n _ => (hh.const_mul _).sub (integrable_hsq_mul_lor hg (bShift_pos hμ n))
  exact hA.add hB

/-- `∫ |ĝ|^2 φ_{mu,N}` in closed form through E6Bridge32's exponential-kernel pairings. -/
theorem integral_hsq_mul_phiShift {g : ℝ → ℂ} (hg : IsWeilTest g) {μ : ℝ} (hμ : ShiftOK μ)
    (N : ℕ) :
    ∫ r : ℝ, hsq g r * phiShift μ N r
      = 2 * Real.pi * ((-Real.eulerMascheroniConstant
          + ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) * mass g
        - (∫ u : ℝ, autocorr g u * (expK (2 * absc μ) u : ℂ)).re
        - ∑ n ∈ Finset.range N, (∫ u : ℝ, autocorr g u * (expK (bShift μ n) u : ℂ)).re) := by
  have hh := integrable_hsq hg
  have ha : (0 : ℝ) < 2 * absc μ := by have := absc_pos hμ; positivity
  rw [hsq_mul_phiShift_eq]
  have hA : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r
      - hsq g r * lor (2 * absc μ) r) :=
    (hh.const_mul _).sub (integrable_hsq_mul_lor hg ha)
  have hA1 : Integrable (fun r : ℝ => (-Real.eulerMascheroniConstant) * hsq g r) := hh.const_mul _
  have hA2 : Integrable (fun r : ℝ => hsq g r * lor (2 * absc μ) r) := integrable_hsq_mul_lor hg ha
  have hBn : ∀ n ∈ Finset.range N, Integrable (fun r : ℝ =>
      (1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r) :=
    fun n _ => (hh.const_mul _).sub (integrable_hsq_mul_lor hg (bShift_pos hμ n))
  have hB : Integrable (fun r : ℝ => ∑ n ∈ Finset.range N,
      ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r)) :=
    integrable_finsetSum _ hBn
  rw [integral_add hA hB, integral_sub hA1 hA2, integral_finsetSum _ hBn, integral_const_mul,
    integral_hsq hg, integral_hsq_mul_lor hg ha]
  have hsum : ∀ n ∈ Finset.range N,
      ∫ r : ℝ, ((1 / ((n : ℝ) + 1)) * hsq g r - hsq g r * lor (bShift μ n) r)
        = (1 / ((n : ℝ) + 1)) * (2 * Real.pi * mass g)
          - 2 * Real.pi * (∫ u : ℝ, autocorr g u * (expK (bShift μ n) u : ℂ)).re := by
    intro n _
    have h1 : Integrable (fun r : ℝ => (1 / ((n : ℝ) + 1)) * hsq g r) := hh.const_mul _
    have h2 : Integrable (fun r : ℝ => hsq g r * lor (bShift μ n) r) :=
      integrable_hsq_mul_lor hg (bShift_pos hμ n)
    rw [integral_sub h1 h2, integral_const_mul, integral_hsq hg, integral_hsq_mul_lor hg (bShift_pos hμ n)]
  rw [Finset.sum_congr rfl hsum, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The archimedean integral of the shift dominates its finite minorant. -/
theorem integral_hsq_mul_psiShift_ge {g : ℝ → ℂ} (hg : IsWeilTest g) {μ : ℝ} (hμ : ShiftOK μ)
    (N : ℕ) :
    ∫ r : ℝ, hsq g r * phiShift μ N r ≤ ∫ r : ℝ, hsq g r * psiShift μ r := by
  refine integral_mono (integrable_hsq_mul_phiShift hg hμ N) (integrable_hsq_mul_psiShift hg hμ)
    fun r => ?_
  exact mul_le_mul_of_nonneg_left (phiShift_le_psiShift hμ N r) (by unfold hsq; positivity)

/-! ## F. The instance `mu = 1`: the second digamma `Re psi(3/4 + i r/2)`. -/

/-- Twin of E6Bridge30's series (`psiR_eq` + `re_digamma_vertical`): the vertical-line series of
the second digamma (`a = 3/4`). -/
theorem psiD_eq_series (r : ℝ) :
    psiShift 1 r = -Real.eulerMascheroniConstant - (3 / 4) / ((3 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑' n : ℕ, serFa (3 / 4) (r / 2) n := by
  rw [psiShift_eq_series shiftOK_one, absc_one]

/-- Twin of E6Bridge11 `psiR_ge` (`-5 <= psiR`): the constant floor `-2` (`-gamma - 4/3`,
`gamma < 2/3`). -/
theorem psiD_ge_const (r : ℝ) : -2 ≤ psiShift 1 r := by
  have h := psiShift_ge_const shiftOK_one r
  rw [absc_one] at h
  have := Real.eulerMascheroniConstant_lt_two_thirds
  norm_num at h
  linarith

/-- Twin of E6Bridge11 `psiR_ge_two`: the Stirling floor `2` at `|r| >= R₀ = 41`. -/
theorem psiD_ge_two {r : ℝ} (hr : R₀ ≤ |r|) : 2 ≤ psiShift 1 r := by
  unfold R₀ at hr
  have h := psiShift_ge_log shiftOK_one (r := r) (by linarith)
  have hlog : 3 ≤ Real.log (|r| / 2) := by
    have he : Real.exp 3 ≤ |r| / 2 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3
      rw [h1]
      nlinarith
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (|r| / 2) := Real.log_le_log (Real.exp_pos 3) he
  have hr2 : 20 / r ^ 2 ≤ 1 := by
    have : (41 : ℝ) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs r]
      exact pow_le_pow_left₀ (by norm_num) hr 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

/-- Twin of E6Bridge30 `psiR_neg`. -/
theorem psiD_neg (r : ℝ) : psiShift 1 (-r) = psiShift 1 r := psiShift_neg shiftOK_one r
/-- Twin of E6Bridge30 `psiR_abs`. -/
theorem psiD_abs (r : ℝ) : psiShift 1 |r| = psiShift 1 r := psiShift_abs shiftOK_one r
/-- Twin of E6Bridge30 `psiR_mono`: monotone in `|r|`. -/
theorem psiD_mono {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ |r|) : psiShift 1 s ≤ psiShift 1 r :=
  psiShift_mono shiftOK_one hs hsr
/-- Twin of E6Bridge11 `continuous_psiR`. -/
theorem continuous_psiD : Continuous (psiShift 1) := continuous_psiShift shiftOK_one

/-- Twin of E6Bridge30 `psiR_ge_series`: `psiShift 1 r >= -gamma - a/(a^2+t^2) + Σ_{n<N} f(n)
+ (G(N) - G(N+M))`, `a = 3/4`, `t = r/2`. -/
theorem psiD_ge_series (r : ℝ) (N M : ℕ) :
    -Real.eulerMascheroniConstant - (3 / 4) / ((3 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serFa (3 / 4) (r / 2) n
      + (serGa (3 / 4) (r / 2) N - serGa (3 / 4) (r / 2) (N + M)) ≤ psiShift 1 r := by
  have h := psiShift_ge_series shiftOK_one r N M
  rw [absc_one] at h
  exact h

/-- Twin of ZhuEnvelope `psiR_ge_stirling` (`t >= 25/2`): `log(t/2) - 1/t <= psiShift 1 t` for
`t >= 27/2` (`(12 + 3/2)/t^2 <= 1/t`). -/
theorem psiD_ge_stirling {t : ℝ} (ht : 27 / 2 ≤ t) : Real.log (t / 2) - 1 / t ≤ psiShift 1 t := by
  have h := psiShift_ge_stirling shiftOK_one (t := t) (by linarith)
  rw [absc_one] at h
  have ht0 : 0 < t := by linarith
  have : (12 + 2 * (3 / 4 : ℝ)) / t ^ 2 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  linarith

/-- Twin of ZhuTail `psiR_le_stirling` (`log(t/2) + 13/t^2`): `psiShift 1 t <= log(t/2) + 14/t^2`
for `t >= 1`. -/
theorem psiD_le_stirling {t : ℝ} (ht : 1 ≤ t) : psiShift 1 t ≤ Real.log (t / 2) + 14 / t ^ 2 := by
  have h := psiShift_le_stirling shiftOK_one (t := t) ht
  rw [absc_one] at h
  have ht0 : 0 < t := by linarith
  have : (12 + 2 * (3 / 4 : ℝ) ^ 2) / t ^ 2 ≤ 14 / t ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num
  linarith

/-- Twin of E6Bridge30 `psiR_ge_rational`: the rational lower bound of the second digamma (`N`
terms, tail `M`, `gamma <= gamma_up`). -/
theorem psiD_ge_rational (r : ℝ) (N M : ℕ) {γ : ℝ} (hγ : Real.eulerMascheroniConstant ≤ γ) :
    -γ - (3 / 4) / ((3 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range N, serFa (3 / 4) (r / 2) n
      + (1 / 2) * (1 - ((N : ℝ) + 1) ^ 2 / (((N : ℝ) + 1 + 3 / 4) ^ 2 + (r / 2) ^ 2))
      - (1 / 2) * (((((N : ℝ) + M) + 1 + 3 / 4) ^ 2 + (r / 2) ^ 2) / (((N : ℝ) + M + 1) ^ 2) - 1)
      ≤ psiShift 1 r := by
  have h := psiShift_ge_rational shiftOK_one r N M hγ
  rw [absc_one] at h
  exact h

/-- The rational upper bound of the second digamma (`N + 1` terms, `gamma_lo <= gamma`). -/
theorem psiD_le_rational (r : ℝ) (N : ℕ) {γ : ℝ} (hγ : γ ≤ Real.eulerMascheroniConstant) :
    psiShift 1 r ≤ -γ - (3 / 4) / ((3 / 4) ^ 2 + (r / 2) ^ 2)
      + ∑ n ∈ Finset.range (N + 1), serFa (3 / 4) (r / 2) n
      + (1 / 2) * ((((N : ℝ) + 1 + 3 / 4) ^ 2 + (r / 2) ^ 2) / ((N : ℝ) + 1) ^ 2 - 1) := by
  have h := psiShift_le_rational shiftOK_one r N hγ
  rw [absc_one] at h
  exact h

/-- Twin of E6Bridge32 `psiR_ge_finite` (abscissae `1/2`, `2n + 5/2`): the finite Lorentzian
minorant of the second digamma, abscissae `3/2` and `2n + 7/2`. -/
theorem psiD_ge_finite (r : ℝ) (N : ℕ) :
    -Real.eulerMascheroniConstant - lor (3 / 2) r
      + ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - lor (2 * n + 7 / 2) r) ≤ psiShift 1 r := by
  have h := psiShift_ge_finite shiftOK_one r N
  rw [absc_one] at h
  simp only [bShift_one] at h
  norm_num at h ⊢
  exact h

/-- `gamma >= 0.5733` (Mathlib: `H_128 - log 129 < gamma`, `log 129 <= 7 log 2 + 1/128`). -/
lemma eulerMascheroni_ge : (5733 / 10000 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 128
  rw [Real.eulerMascheroniSeq] at h
  have h3 : Real.log (((128 : ℕ) : ℝ) + 1) ≤ 7 * Real.log 2 + 1 / 128 := by
    have e : (((128 : ℕ) : ℝ) + 1) = 2 ^ 7 * (1 + 1 / 128) := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 128)
    push_cast
    linarith
  have h4 : (54331470 / 10000000 : ℝ) ≤ ((harmonic 128 : ℚ) : ℝ) := by
    have hq : (54331470 / 10000000 : ℚ) ≤ harmonic 128 := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have hr : ((54331470 / 10000000 : ℚ) : ℝ) ≤ ((harmonic 128 : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at hr
    exact hr
  have h5 := Real.log_two_lt_d9
  have h6 : 7 * Real.log 2 < 7 * 0.6931471808 := by linarith
  set H : ℝ := ((harmonic 128 : ℚ) : ℝ) with hH
  set Lg : ℝ := Real.log (((128 : ℕ) : ℝ) + 1) with hLg
  norm_num at h6 h4 ⊢
  linarith

/-! ### Kernel-checkable floors and ceilings of the second digamma (N = 40 terms, tail M = 10^6). -/

/-- Twin of E6Bridge30 `psiR_floor_0` (`psiR 0 >= -4.2315`): `psi(3/4) = -1.08586...`, floor
`-1.091`. -/
lemma psiD_floor_0 : (-1091 / 1000 : ℝ) ≤ psiShift 1 0 := by
  refine le_trans ?_ (psiD_ge_rational 0 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- ceiling `-1.0813` (`gamma >= 0.5733`). -/
lemma psiD_ceil_0 : psiShift 1 0 ≤ (-10813 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 0 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_floor_1 : (-614 / 1000 : ℝ) ≤ psiShift 1 1 := by
  refine le_trans ?_ (psiD_ge_rational 1 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_ceil_1 : psiShift 1 1 ≤ (-6049 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 1 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_floor_2 : (-96 / 10000 : ℝ) ≤ psiShift 1 2 := by
  refine le_trans ?_ (psiD_ge_rational 2 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_ceil_2 : psiShift 1 2 ≤ (-6 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 2 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_floor_4 : (6860 / 10000 : ℝ) ≤ psiShift 1 4 := by
  refine le_trans ?_ (psiD_ge_rational 4 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_ceil_4 : psiShift 1 4 ≤ (6951 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 4 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_floor_8 : (13808 / 10000 : ℝ) ≤ psiShift 1 8 := by
  refine le_trans ?_ (psiD_ge_rational 8 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_ceil_8 : psiShift 1 8 ≤ (13905 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 8 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_floor_16 : (20734 / 10000 : ℝ) ≤ psiShift 1 16 := by
  refine le_trans ?_ (psiD_ge_rational 16 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_ceil_16 : psiShift 1 16 ≤ (20852 / 10000 : ℝ) := by
  refine le_trans (psiD_le_rational 16 40 eulerMascheroni_ge) ?_
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ### The envelope of the second digamma (twin of ZhuEnvelope `psiR_ge_envelope`, Zhu Lemma 3.1):
thirteen bands `[15/4, 27/2]` with rational left-endpoint floors (N = 40, M = 10^6) beating the
increasing right-hand side at the right endpoint, then Stirling from `27/2`. -/

/-- Twin of ZhuEnvelope `band_step` for the second digamma. -/
lemma psiD_band_step {a b φ : ℝ} (ha : 0 < a) (hφ : φ ≤ psiShift 1 a)
    (hb : Real.log (b / 2) - 1 / b ≤ φ) {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    Real.log (t / 2) - 1 / t ≤ psiShift 1 t := by
  have h1 : psiShift 1 a ≤ psiShift 1 t :=
    psiD_mono ha.le (by rw [abs_of_pos (by linarith)]; exact hat)
  have h2 : Real.log (t / 2) ≤ Real.log (b / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have h3 : 1 / b ≤ 1 / t := one_div_le_one_div_of_le (by linarith) htb
  linarith

lemma psiD_bfloor_0 : (6211 / 10000 : ℝ) ≤ psiShift 1 (15 / 4) := by
  refine le_trans ?_ (psiD_ge_rational (15 / 4) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_1 : (8263 / 10000 : ℝ) ≤ psiShift 1 (23 / 5) := by
  refine le_trans ?_ (psiD_ge_rational (23 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_2 : (2491 / 2500 : ℝ) ≤ psiShift 1 (109 / 20) := by
  refine le_trans ?_ (psiD_ge_rational (109 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_3 : (11417 / 10000 : ℝ) ≤ psiShift 1 (63 / 10) := by
  refine le_trans ?_ (psiD_ge_rational (63 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_4 : (3171 / 2500 : ℝ) ≤ psiShift 1 (143 / 20) := by
  refine le_trans ?_ (psiD_ge_rational (143 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_5 : (863 / 625 : ℝ) ≤ psiShift 1 (8) := by
  refine le_trans ?_ (psiD_ge_rational (8) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_6 : (14819 / 10000 : ℝ) ≤ psiShift 1 (177 / 20) := by
  refine le_trans ?_ (psiD_ge_rational (177 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_7 : (1967 / 1250 : ℝ) ≤ psiShift 1 (97 / 10) := by
  refine le_trans ?_ (psiD_ge_rational (97 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_8 : (1036 / 625 : ℝ) ≤ psiShift 1 (211 / 20) := by
  refine le_trans ?_ (psiD_ge_rational (211 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_9 : (347 / 200 : ℝ) ≤ psiShift 1 (57 / 5) := by
  refine le_trans ?_ (psiD_ge_rational (57 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_10 : (18069 / 10000 : ℝ) ≤ psiShift 1 (49 / 4) := by
  refine le_trans ?_ (psiD_ge_rational (49 / 4) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_11 : (1827 / 1000 : ℝ) ≤ psiShift 1 (25 / 2) := by
  refine le_trans ?_ (psiD_ge_rational (25 / 2) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_bfloor_12 : (9331 / 5000 : ℝ) ≤ psiShift 1 (13) := by
  refine le_trans ?_ (psiD_ge_rational (13) 40 1000000 eulerMascheroni_le)
  simp only [serFa, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma psiD_brhs_0 : Real.log ((23 / 5) / 2) - 1 / (23 / 5) ≤ (6211 / 10000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_1 : Real.log ((109 / 20) / 2) - 1 / (109 / 20) ≤ (8263 / 10000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_2 : Real.log ((63 / 10) / 2) - 1 / (63 / 10) ≤ (2491 / 2500 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_3 : Real.log ((143 / 20) / 2) - 1 / (143 / 20) ≤ (11417 / 10000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_4 : Real.log ((8) / 2) - 1 / (8) ≤ (3171 / 2500 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_5 : Real.log ((177 / 20) / 2) - 1 / (177 / 20) ≤ (863 / 625 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_6 : Real.log ((97 / 10) / 2) - 1 / (97 / 10) ≤ (14819 / 10000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_7 : Real.log ((211 / 20) / 2) - 1 / (211 / 20) ≤ (1967 / 1250 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_8 : Real.log ((57 / 5) / 2) - 1 / (57 / 5) ≤ (1036 / 625 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_9 : Real.log ((49 / 4) / 2) - 1 / (49 / 4) ≤ (347 / 200 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_10 : Real.log ((25 / 2) / 2) - 1 / (25 / 2) ≤ (18069 / 10000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_11 : Real.log ((13) / 2) - 1 / (13) ≤ (1827 / 1000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma psiD_brhs_12 : Real.log ((27 / 2) / 2) - 1 / (27 / 2) ≤ (9331 / 5000 : ℝ) := by
  refine RvMBridgeZhu.rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- Twin of ZhuEnvelope `psiR_ge_envelope` (Zhu Lemma 3.1 for the second digamma):
`log(t/2) - 1/t <= Re psi(3/4 + it/2)` for `t >= 15/4`. -/
theorem psiD_ge_envelope {t : ℝ} (ht : 15 / 4 ≤ t) : Real.log (t / 2) - 1 / t ≤ psiShift 1 t := by
  rcases le_or_gt t (23 / 5) with h0 | h0
  · exact psiD_band_step (by norm_num) psiD_bfloor_0 psiD_brhs_0 ht h0
  rcases le_or_gt t (109 / 20) with h1 | h1
  · exact psiD_band_step (by norm_num) psiD_bfloor_1 psiD_brhs_1 h0.le h1
  rcases le_or_gt t (63 / 10) with h2 | h2
  · exact psiD_band_step (by norm_num) psiD_bfloor_2 psiD_brhs_2 h1.le h2
  rcases le_or_gt t (143 / 20) with h3 | h3
  · exact psiD_band_step (by norm_num) psiD_bfloor_3 psiD_brhs_3 h2.le h3
  rcases le_or_gt t (8) with h4 | h4
  · exact psiD_band_step (by norm_num) psiD_bfloor_4 psiD_brhs_4 h3.le h4
  rcases le_or_gt t (177 / 20) with h5 | h5
  · exact psiD_band_step (by norm_num) psiD_bfloor_5 psiD_brhs_5 h4.le h5
  rcases le_or_gt t (97 / 10) with h6 | h6
  · exact psiD_band_step (by norm_num) psiD_bfloor_6 psiD_brhs_6 h5.le h6
  rcases le_or_gt t (211 / 20) with h7 | h7
  · exact psiD_band_step (by norm_num) psiD_bfloor_7 psiD_brhs_7 h6.le h7
  rcases le_or_gt t (57 / 5) with h8 | h8
  · exact psiD_band_step (by norm_num) psiD_bfloor_8 psiD_brhs_8 h7.le h8
  rcases le_or_gt t (49 / 4) with h9 | h9
  · exact psiD_band_step (by norm_num) psiD_bfloor_9 psiD_brhs_9 h8.le h9
  rcases le_or_gt t (25 / 2) with h10 | h10
  · exact psiD_band_step (by norm_num) psiD_bfloor_10 psiD_brhs_10 h9.le h10
  rcases le_or_gt t (13) with h11 | h11
  · exact psiD_band_step (by norm_num) psiD_bfloor_11 psiD_brhs_11 h10.le h11
  rcases le_or_gt t (27 / 2) with h12 | h12
  · exact psiD_band_step (by norm_num) psiD_bfloor_12 psiD_brhs_12 h11.le h12
  exact psiD_ge_stirling h12.le

/-- The two-digamma envelope of the quadratic archimedean symbol `psiR + psiShift mu_d`:
`2 (log(t/2) - 1/t) <= psiR t + psiShift (muOf neg) t` for `t >= 15/4`, both signs. -/
theorem symbolArch_quad_ge_envelope (neg : Bool) {t : ℝ} (ht : 15 / 4 ≤ t) :
    2 * (Real.log (t / 2) - 1 / t) ≤ psiR t + psiShift (muOf neg) t := by
  have h1 := RvMBridgeZhu.psiR_ge_envelope ht
  cases neg
  · simp only [muOf, Bool.false_eq_true, if_false, psiShift_zero]
    linarith
  · simp only [muOf, if_true]
    have h2 := psiD_ge_envelope ht
    linarith

end FamilyWeil

end
