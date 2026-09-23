/-  H1000Phase.lean -- the Riemann-Siegel phase at a rational height, as kernel-checkable integer
    bounds (lane h1000-prep; consumed by `H1000Line`).

    For `t = tn / 2^tq` and the branch limit `Λ = lim imLnVal (1/4) (t/2)` (the one
    `KernelGammaEnvelope.gLine_decomp_explicit` exposes), `phase_sound` gives

        phaseLo tn tq k nl ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi tn tq k nl,

    where `phaseLo`, `phaseHi` are plain `Int`/`Nat` computations (the kernel evaluates them) of the
    height-uniform bracket `RSTheta.theta_bracket`:
        thetaS t - 1/(2t) ≤ Λ - (t/2) log π ≤ thetaS t,
        thetaS t = (t/4) log (1/16 + t²/4) - (1/4) arctan (2t) - t/2 - (t/2) log π.
    Ingredients: `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`, `A = 4^tq + 4 tn²`
    (`log_inner_eq`); the fixed-point series of `-log (1 - x)` with Mathlib's geometric remainder
    `Real.abs_log_sub_add_sum_range_le` (`lnBox_sound`); `log 2`, `log π` from `RSTheta.log2_box`,
    `logpi_box`; `π` from `Real.pi_gt_d20`, `pi_lt_d20`; `arctan (2t) = π/2 - arctan w` with
    `w - w³/3 ≤ arctan w ≤ w` (`ArctanTaylor`).  Every rounding is outward (`fdiv`, `cdiv`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Elementary enclosures of one special-function value; nothing here
    bears on the Riemann Hypothesis.
-/
import EMZetaHighCheck
import RSTheta
import KernelGammaEnvelope
import SignChain
import ArctanTaylor

open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section

/-! ## A. Floor and ceiling division of an integer by a positive natural. -/

/-- `⌊a / b⌋` for `b > 0` (`Int.ediv`). -/
def fdiv (a : ℤ) (b : ℕ) : ℤ := a / (b : ℤ)

/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))

theorem fdiv_le (a : ℤ) {b : ℕ} (hb : 0 < b) : ((fdiv a b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hb)
  have h := Int.ediv_mul_le a hb'
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  have h' : (((a / (b : ℤ)) * (b : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  rw [Int.cast_mul, Int.cast_natCast] at h'
  exact h'

theorem le_cdiv (a : ℤ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ ((cdiv a b : ℤ) : ℝ) := by
  have h := fdiv_le (-a) hb
  unfold fdiv at h
  unfold cdiv
  rw [Int.cast_neg]
  rw [Int.cast_neg, neg_div] at h
  linarith

/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/

/-- The fixed-point scale of the phase, `2^64` (the evaluator's `one`). -/
def ONE : ℕ := 18446744073709551616

theorem ONE_eq : ((ONE : ℕ) : ℝ) = 2 ^ 64 := by norm_num [ONE]

/-- `lser one a b n i pa pb acc`: `n` more floored series terms from index `i` (with `pa = a^(i+1)`,
    `pb = b^(i+1)`); returns `(acc', a^(i+n+1), b^(i+n+1))`.  The scale `one` is a parameter (it is
    `ONE = 2^64` in `lnBox`), so the generic lemmas never unfold a large literal. -/
def lser (one a b : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (fun _ pa pb acc => (acc, pa, pb))
    (fun _ ih i pa pb acc => ih (i + 1) (pa * a) (pb * b) (acc + pa * one / (pb * (i + 1))))

/-- The `j`-th floored term `⌊a^(j+1) one / (b^(j+1) (j+1))⌋`. -/
def lterm (one a b j : ℕ) : ℕ := a ^ (j + 1) * one / (b ^ (j + 1) * (j + 1))

theorem lser_zero (one a b i pa pb acc : ℕ) : lser one a b 0 i pa pb acc = (acc, pa, pb) := rfl

theorem lser_succ (one a b n i pa pb acc : ℕ) :
    lser one a b (n + 1) i pa pb acc
      = lser one a b n (i + 1) (pa * a) (pb * b) (acc + pa * one / (pb * (i + 1))) := rfl

theorem lser_spec (one a b : ℕ) : ∀ (n i acc : ℕ),
    lser one a b n i (a ^ (i + 1)) (b ^ (i + 1)) acc
      = (acc + ∑ j ∈ Finset.range n, lterm one a b (i + j), a ^ (i + n + 1), b ^ (i + n + 1)) := by
  intro n
  induction n with
  | zero => intro i acc; simp [lser_zero]
  | succ n ih =>
    intro i acc
    rw [lser_succ, ← pow_succ, ← pow_succ, ih (i + 1)]
    have hs : ∑ j ∈ Finset.range (n + 1), lterm one a b (i + j)
        = lterm one a b i + ∑ j ∈ Finset.range n, lterm one a b (i + 1 + j) := by
      rw [Finset.sum_range_succ', add_comm, add_zero]
      refine congrArg (lterm one a b i + ·) (Finset.sum_congr rfl fun j _ => ?_)
      rw [show i + (j + 1) = i + 1 + j by ring]
    rw [hs]
    have e1 : i + 1 + n + 1 = i + (n + 1) + 1 := by ring
    rw [e1]
    simp only [lterm, Prod.mk.injEq, and_true]
    ring

theorem lser_spec0 (one a b n : ℕ) :
    lser one a b n 0 a b 0 = (∑ j ∈ Finset.range n, lterm one a b j, a ^ (n + 1), b ^ (n + 1)) := by
  have h := lser_spec one a b n 0 0
  simp only [zero_add, pow_one] at h
  exact h

/-- `(lo, hi)` with `lo ≤ -log (1 - a/b) · 2^64 ≤ hi` (for `0 < b`, `2a < b`): `nl` floored series
    terms plus the geometric tail `(a/b)^(nl+1) / (1 - a/b)`. -/
def lnBox (a b nl : ℕ) : ℤ × ℤ :=
  let r := lser ONE a b nl 0 a b 0
  let EU : ℕ := r.2.1 * ONE * b / (r.2.2 * (b - a)) + 1
  ((r.1 : ℤ) - (EU : ℤ), ((r.1 + nl + EU : ℕ) : ℤ))

theorem lnBox_sound (a b nl : ℕ) (hb : 0 < b) (h2 : 2 * a < b) :
    (((lnBox a b nl).1 : ℤ) : ℝ) ≤ -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ∧
    -Real.log (1 - (a : ℝ) / b) * 2 ^ 64 ≤ (((lnBox a b nl).2 : ℤ) : ℝ) := by
  have hspec := lser_spec0 ONE a b nl
  simp only [lnBox, hspec]
  set S := ∑ j ∈ Finset.range nl, lterm ONE a b j with hS
  set EU : ℕ := a ^ (nl + 1) * ONE * b / (b ^ (nl + 1) * (b - a)) + 1 with hEU
  set x : ℝ := (a : ℝ) / b with hx
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : a < b := by omega
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 / 2 := by
    rw [hx, div_lt_iff₀ hbR]
    have : ((2 * a : ℕ) : ℝ) < b := by exact_mod_cast h2
    push_cast at this; linarith
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  -- each floored term against the exact term
  have hterm : ∀ j : ℕ, (lterm ONE a b j : ℝ) ≤ x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64 ∧
      x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64 < (lterm ONE a b j : ℝ) + 1 := by
    intro j
    have e : x ^ (j + 1) / ((j : ℝ) + 1) * 2 ^ 64
        = ((a ^ (j + 1) * ONE : ℕ) : ℝ) / ((b ^ (j + 1) * (j + 1) : ℕ) : ℝ) := by
      rw [hx, div_pow]; push_cast; rw [ONE_eq]; field_simp
    rw [e]
    have hpos : 0 < b ^ (j + 1) * (j + 1) := by positivity
    exact ⟨natdiv_le _ _, lt_natdiv_add_one _ _ hpos⟩
  have hsum_lo : (S : ℝ) ≤ (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64 := by
    rw [hS, Finset.sum_mul]; push_cast
    exact Finset.sum_le_sum (fun j _ => (hterm j).1)
  have hsum_hi : (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64 ≤ (S : ℝ) + nl := by
    rw [hS, Finset.sum_mul]; push_cast
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range nl) => (hterm j).2.le)
    rw [Finset.sum_add_distrib] at h
    simpa using h
  -- the Mathlib remainder bound
  have habs := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) nl
  rw [abs_of_nonneg hx0] at habs
  have hbaR : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have htail : x ^ (nl + 1) / (1 - x) * 2 ^ 64 ≤ (EU : ℝ) := by
    have h1 : (1 : ℝ) - (a : ℝ) / b = ((b : ℝ) - a) / b := by field_simp
    have e : x ^ (nl + 1) / (1 - x) * 2 ^ 64
        = ((a ^ (nl + 1) * ONE * b : ℕ) : ℝ) / ((b ^ (nl + 1) * (b - a) : ℕ) : ℝ) := by
      rw [hx, h1, div_pow]
      push_cast [Nat.cast_sub hab.le]
      rw [ONE_eq]
      field_simp
    rw [e, hEU]
    have hpos : 0 < b ^ (nl + 1) * (b - a) := by
      have : 0 < b - a := by omega
      positivity
    have := lt_natdiv_add_one (a ^ (nl + 1) * ONE * b) (b ^ (nl + 1) * (b - a)) hpos
    push_cast at this ⊢
    linarith
  have hsplit : -Real.log (1 - x) * 2 ^ 64
      = (∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) * 2 ^ 64
        - ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64 := by
    ring
  have hmid := abs_le.mp habs
  have hm1 : -(x ^ (nl + 1) / (1 - x)) * 2 ^ 64
      ≤ ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64 :=
    mul_le_mul_of_nonneg_right hmid.1 hP.le
  have hm2 : ((∑ j ∈ Finset.range nl, x ^ (j + 1) / ((j : ℝ) + 1)) + Real.log (1 - x)) * 2 ^ 64
      ≤ x ^ (nl + 1) / (1 - x) * 2 ^ 64 :=
    mul_le_mul_of_nonneg_right hmid.2 hP.le
  push_cast
  constructor
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/

def L2LO : ℕ := 12786308645202588812
def L2HI : ℕ := 12786308645202719885
def LPLO : ℕ := 21116539237789363774
def LPHI : ℕ := 21116539237791978907
def P8LO : ℕ := 7244019458077122842
def P8HI : ℕ := 7244019458077122843
def TPLO : ℕ := 115904311329233965478
def TPHI : ℕ := 115904311329233965479

theorem log2_scaled : (L2LO : ℝ) ≤ Real.log 2 * 2 ^ 64 ∧ Real.log 2 * 2 ^ 64 ≤ L2HI := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.log2_box
  have hP : (0 : ℝ) ≤ 2 ^ 64 := by positivity
  have a1 := mul_le_mul_of_nonneg_right h1 hP
  have a2 := mul_le_mul_of_nonneg_right h2 hP
  constructor
  · have e : (L2LO : ℝ) ≤ 3465735902799708427977 / 5000000000000000000000 * 2 ^ 64 := by
      norm_num [L2LO]
    linarith
  · have e : 6931471805599487910229 / 10000000000000000000000 * 2 ^ 64 ≤ (L2HI : ℝ) := by
      norm_num [L2HI]
    linarith

theorem logpi_scaled : (LPLO : ℝ) ≤ Real.log π * 2 ^ 64 ∧ Real.log π * 2 ^ 64 ≤ LPHI := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.logpi_box
  have hP : (0 : ℝ) ≤ 2 ^ 64 := by positivity
  have a1 := mul_le_mul_of_nonneg_right h1 hP
  have a2 := mul_le_mul_of_nonneg_right h2 hP
  constructor
  · have e : (LPLO : ℝ) ≤ 11447298858493313056567 / 10000000000000000000000 * 2 ^ 64 := by
      norm_num [LPLO]
    linarith
  · have e : 5723649429247365361409 / 5000000000000000000000 * 2 ^ 64 ≤ (LPHI : ℝ) := by
      norm_num [LPHI]
    linarith

theorem pi8_scaled : (P8LO : ℝ) ≤ π / 8 * 2 ^ 64 ∧ π / 8 * 2 ^ 64 ≤ P8HI := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · have e : (P8LO : ℝ) ≤ 3.14159265358979323846 / 8 * 2 ^ 64 := by norm_num [P8LO]
    nlinarith
  · have e : 3.14159265358979323847 / 8 * 2 ^ 64 ≤ (P8HI : ℝ) := by norm_num [P8HI]
    nlinarith

theorem twopi_scaled : (TPLO : ℝ) ≤ 2 * π * 2 ^ 64 ∧ 2 * π * 2 ^ 64 ≤ TPHI := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · have e : (TPLO : ℝ) ≤ 2 * 3.14159265358979323846 * 2 ^ 64 := by norm_num [TPLO]
    nlinarith
  · have e : 2 * 3.14159265358979323847 * 2 ^ 64 ≤ (TPHI : ℝ) := by norm_num [TPHI]
    nlinarith

/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/

/-- `A = 4^tq + 4 tn²`, so that `1/16 + t²/4 = A / 2^(2 tq + 4)` at `t = tn / 2^tq`. -/
def AA (tn tq : ℕ) : ℕ := 2 ^ tq * 2 ^ tq + 4 * tn * tn

/-- Side conditions of the phase evaluation: `2^k ≤ A < 2^(k+1)`, `2 tq + 4 ≤ k`, `1 ≤ tn`,
    `2^tq ≤ 2 tn` (so `t ≥ 1/2`). -/
def phaseOk (tn tq k : ℕ) : Bool :=
  decide (2 ^ k ≤ AA tn tq) && decide (AA tn tq < 2 * 2 ^ k) && decide (2 * tq + 4 ≤ k) &&
    decide (1 ≤ tn) && decide (2 ^ tq ≤ 2 * tn)

/-- Bounds for `log (1/16 + t²/4) · 2^64`: `(k - 2 tq - 4) log 2 - log (1 - (A - 2^k)/A)`. -/
def innerBox (tn tq k nl : ℕ) : ℤ × ℤ :=
  let j : ℤ := ((k - (2 * tq + 4) : ℕ) : ℤ)
  let lb := lnBox (AA tn tq - 2 ^ k) (AA tn tq) nl
  (j * (L2LO : ℤ) + lb.1, j * (L2HI : ℤ) + lb.2)

/-- Lower bound of `φ · 2^64` (theta bracket lower edge `thetaS t - 1/(2t)`). -/
def phaseLo (tn tq k nl : ℕ) : ℤ :=
  fdiv ((innerBox tn tq k nl).1 * (tn : ℤ)) (4 * 2 ^ tq)
    + (fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn)
        - cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) - (P8HI : ℤ))
    + fdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq)
    + fdiv (-((tn * LPHI : ℕ) : ℤ)) (2 * 2 ^ tq)
    - cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (2 * tn)

/-- Upper bound of `φ · 2^64` (theta bracket upper edge `thetaS t`). -/
def phaseHi (tn tq k nl : ℕ) : ℤ :=
  cdiv ((innerBox tn tq k nl).2 * (tn : ℤ)) (4 * 2 ^ tq)
    + (cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) - (P8LO : ℤ))
    + cdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq)
    + cdiv (-((tn * LPLO : ℕ) : ℤ)) (2 * 2 ^ tq)

theorem phaseOk_spec {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    2 ^ k ≤ AA tn tq ∧ AA tn tq < 2 * 2 ^ k ∧ 2 * tq + 4 ≤ k ∧ 1 ≤ tn ∧ 2 ^ tq ≤ 2 * tn := by
  simp only [phaseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`. -/
theorem log_inner_eq {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4)
      = ((k - (2 * tq + 4) : ℕ) : ℝ) * Real.log 2
        + -Real.log (1 - ((AA tn tq - 2 ^ k : ℕ) : ℝ) / (AA tn tq : ℕ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec h
  have hA : (0 : ℝ) < (AA tn tq : ℕ) := by
    have : 0 < AA tn tq := lt_of_lt_of_le (Nat.two_pow_pos k) h1
    exact_mod_cast this
  have hAeq : ((AA tn tq : ℕ) : ℝ) = (2 : ℝ) ^ tq * 2 ^ tq + 4 * tn * tn := by
    simp [AA]
  have e1 : (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) = ((AA tn tq : ℕ) : ℝ) / 2 ^ (2 * tq + 4) := by
    rw [hAeq]
    have hq : (0 : ℝ) < 2 ^ tq := by positivity
    rw [show (2 : ℝ) ^ (2 * tq + 4) = (2 ^ tq) ^ 2 * 16 by rw [pow_add, pow_mul']; norm_num]
    field_simp
    ring
  have e2 : (1 : ℝ) - ((AA tn tq - 2 ^ k : ℕ) : ℝ) / (AA tn tq : ℕ) = (2 : ℝ) ^ k / (AA tn tq : ℕ) := by
    rw [Nat.cast_sub h1]
    push_cast
    field_simp
    ring
  have e3 : ((k - (2 * tq + 4) : ℕ) : ℝ) = (k : ℝ) - (2 * tq + 4) := by
    rw [Nat.cast_sub h3]; push_cast; ring
  rw [e1, e2, e3, Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hA),
    Real.log_div (ne_of_gt hA) (ne_of_gt (by positivity)), Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem innerBox_sound {tn tq k : ℕ} (nl : ℕ) (h : phaseOk tn tq k = true) :
    (((innerBox tn tq k nl).1 : ℤ) : ℝ) ≤ Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) * 2 ^ 64 ∧
    Real.log (1 / 16 + ((tn : ℝ) / 2 ^ tq) ^ 2 / 4) * 2 ^ 64 ≤ (((innerBox tn tq k nl).2 : ℤ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec h
  have hA : 0 < AA tn tq := lt_of_lt_of_le (Nat.two_pow_pos k) h1
  have h2a : 2 * (AA tn tq - 2 ^ k) < AA tn tq := by omega
  obtain ⟨lb1, lb2⟩ := lnBox_sound (AA tn tq - 2 ^ k) (AA tn tq) nl hA h2a
  obtain ⟨l1, l2⟩ := log2_scaled
  rw [log_inner_eq h]
  simp only [innerBox]
  set j : ℕ := k - (2 * tq + 4)
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have m1 := mul_le_mul_of_nonneg_left l1 hj
  have m2 := mul_le_mul_of_nonneg_left l2 hj
  push_cast
  constructor <;> nlinarith [m1, m2, lb1, lb2]

/-- The arctan part: `-(1/4) arctan (2t) · 2^64` with `t = tn / 2^tq > 0`, bounded through
    `arctan (2t) = π/2 - arctan w`, `w = 1/(2t)`, and `w - w³/3 ≤ arctan w ≤ w`. -/
theorem arctan_part {tn tq : ℕ} (htn : 1 ≤ tn) :
    ((fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
        - ((cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) : ℤ) : ℝ)
        - (P8HI : ℝ)
      ≤ -(1 / 4) * Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) * 2 ^ 64 ∧
    -(1 / 4) * Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) * 2 ^ 64
      ≤ ((cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ) - (P8LO : ℝ) := by
  have htnR : (0 : ℝ) < tn := by exact_mod_cast htn
  have hq : (0 : ℝ) < 2 ^ tq := by positivity
  set w : ℝ := (2 : ℝ) ^ tq / (2 * tn) with hw
  have hw0 : 0 ≤ w := by positivity
  have harc : Real.arctan (2 * ((tn : ℝ) / 2 ^ tq)) = π / 2 - Real.arctan w := by
    have h := Real.arctan_inv_of_pos (x := 2 * ((tn : ℝ) / 2 ^ tq)) (by positivity)
    have hinv : (2 * ((tn : ℝ) / 2 ^ tq))⁻¹ = w := by rw [hw]; field_simp
    rw [hinv] at h
    linarith
  have a1 := ArctanTaylor.arctan_le_self hw0
  have a2 := ArctanTaylor.self_sub_cube_le_arctan hw0
  obtain ⟨p1, p2⟩ := pi8_scaled
  have hpos1 : 0 < 8 * tn := by omega
  have hpos2 : 0 < 96 * tn * tn * tn := by positivity
  have f1 := fdiv_le ((2 ^ tq * ONE : ℕ) : ℤ) hpos1
  have c1 := le_cdiv ((2 ^ tq * ONE : ℕ) : ℤ) hpos1
  have c2 := le_cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) hpos2
  have e1 : (((2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((8 * tn : ℕ) : ℝ) = w / 4 * 2 ^ 64 := by
    rw [hw]; push_cast; rw [ONE_eq]; field_simp; ring
  have e2 : (((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((96 * tn * tn * tn : ℕ) : ℝ)
      = w ^ 3 / 12 * 2 ^ 64 := by
    rw [hw]; push_cast; rw [ONE_eq]; field_simp; ring
  rw [e1] at f1 c1
  rw [e2] at c2
  set F := ((fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
  set C1 := ((cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) : ℤ) : ℝ)
  set C2 := ((cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) : ℤ) : ℝ)
  rw [harc]
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  have b1 := mul_le_mul_of_nonneg_right a1 hP.le
  have b2 := mul_le_mul_of_nonneg_right a2 hP.le
  constructor
  · have : -(1 / 4) * (π / 2 - Real.arctan w) * 2 ^ 64
        = -(π / 8 * 2 ^ 64) + Real.arctan w * 2 ^ 64 / 4 := by ring
    rw [this]
    have : (w - w ^ 3 / 3) * 2 ^ 64 / 4 = w / 4 * 2 ^ 64 - w ^ 3 / 12 * 2 ^ 64 := by ring
    linarith
  · have : -(1 / 4) * (π / 2 - Real.arctan w) * 2 ^ 64
        = -(π / 8 * 2 ^ 64) + Real.arctan w * 2 ^ 64 / 4 := by ring
    rw [this]
    have : w * 2 ^ 64 / 4 = w / 4 * 2 ^ 64 := by ring
    linarith

/-- **The phase bracket at `t = tn / 2^tq`.**  For the branch limit `Λ` of
    `imLnVal (1/4) (t/2)`: `phaseLo ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi`. -/
theorem phase_sound (tn tq k nl : ℕ) (hok : phaseOk tn tq k = true) (Λ : ℝ)
    (hΛ : Tendsto (ThetaGap.imLnVal (1 / 4) (((tn : ℝ) / 2 ^ tq) / 2)) atTop (𝓝 Λ)) :
    ((phaseLo tn tq k nl : ℤ) : ℝ) ≤ (Λ - ((tn : ℝ) / 2 ^ tq) / 2 * Real.log π) * 2 ^ 64 ∧
    (Λ - ((tn : ℝ) / 2 ^ tq) / 2 * Real.log π) * 2 ^ 64 ≤ ((phaseHi tn tq k nl : ℤ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phaseOk_spec hok
  have htnR : (0 : ℝ) < tn := by exact_mod_cast h4
  have hq : (0 : ℝ) < 2 ^ tq := by positivity
  have hP : (0 : ℝ) < 2 ^ 64 := by positivity
  have hpos4 : 0 < 4 * 2 ^ tq := by positivity
  have hpos2 : 0 < 2 * 2 ^ tq := by positivity
  have hpos2t : 0 < 2 * tn := by omega
  -- the integer pieces, abstracted before any cast normalisation
  obtain ⟨i1, i2⟩ := innerBox_sound nl hok
  obtain ⟨a1, a2⟩ := arctan_part (tq := tq) h4
  have t1lo := fdiv_le ((innerBox tn tq k nl).1 * (tn : ℤ)) hpos4
  have t1hi := le_cdiv ((innerBox tn tq k nl).2 * (tn : ℤ)) hpos4
  have t3lo := fdiv_le (-((tn * ONE : ℕ) : ℤ)) hpos2
  have t3hi := le_cdiv (-((tn * ONE : ℕ) : ℤ)) hpos2
  have t4lo := fdiv_le (-((tn * LPHI : ℕ) : ℤ)) hpos2
  have t4hi := le_cdiv (-((tn * LPLO : ℕ) : ℤ)) hpos2
  have t5 := le_cdiv ((2 ^ tq * ONE : ℕ) : ℤ) hpos2t
  simp only [phaseLo, phaseHi, Int.cast_add, Int.cast_sub, Int.cast_natCast]
  set I1 := (innerBox tn tq k nl).1 with hI1
  set I2 := (innerBox tn tq k nl).2 with hI2
  set F1 := fdiv (I1 * (tn : ℤ)) (4 * 2 ^ tq) with hF1
  set G1 := cdiv (I2 * (tn : ℤ)) (4 * 2 ^ tq) with hG1
  set F2 := fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) with hF2
  set G2 := cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) with hG2
  set C2 := cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) with hC2
  set F3 := fdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq) with hF3
  set G3 := cdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq) with hG3
  set F4 := fdiv (-((tn * LPHI : ℕ) : ℤ)) (2 * 2 ^ tq) with hF4
  set G4 := cdiv (-((tn * LPLO : ℕ) : ℤ)) (2 * 2 ^ tq) with hG4
  set G5 := cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (2 * tn) with hG5
  set t : ℝ := (tn : ℝ) / 2 ^ tq with ht
  have htpos : 0 < t := by rw [ht]; positivity
  obtain ⟨tb1, tb2⟩ := RSDesignTheta.theta_bracket t htpos Λ hΛ
  unfold RSDesignTheta.thetaS at tb1 tb2
  set L := Real.log (1 / 16 + t ^ 2 / 4) with hL
  -- rewrite each piece's real bound
  have ef : ∀ z : ℤ, ((z * (tn : ℤ) : ℤ) : ℝ) / ((4 * 2 ^ tq : ℕ) : ℝ) = (z : ℝ) * (t / 4) := by
    intro z; rw [ht]; push_cast; field_simp
  rw [ef] at t1lo t1hi
  have e3 : ((-((tn * ONE : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 2 ^ tq : ℕ) : ℝ) = -t / 2 * 2 ^ 64 := by
    rw [ht]; push_cast; rw [ONE_eq]; field_simp
  rw [e3] at t3lo t3hi
  have e4 : ∀ c : ℕ, ((-((tn * c : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 2 ^ tq : ℕ) : ℝ) = -(t / 2) * (c : ℝ) := by
    intro c; rw [ht]; push_cast; field_simp
  rw [e4] at t4lo t4hi
  have e5 : (((2 ^ tq * ONE : ℕ) : ℤ) : ℝ) / ((2 * tn : ℕ) : ℝ) = 1 / (2 * t) * 2 ^ 64 := by
    rw [ht]; push_cast; rw [ONE_eq]; field_simp
  rw [e5] at t5
  have m1 : (I1 : ℝ) * (t / 4) ≤ t / 4 * L * 2 ^ 64 := by
    have := mul_le_mul_of_nonneg_right i1 (by positivity : (0 : ℝ) ≤ t / 4)
    linarith
  have m2 : t / 4 * L * 2 ^ 64 ≤ (I2 : ℝ) * (t / 4) := by
    have := mul_le_mul_of_nonneg_right i2 (by positivity : (0 : ℝ) ≤ t / 4)
    linarith
  obtain ⟨lp1, lp2⟩ := logpi_scaled
  have m4lo : -(t / 2) * (LPHI : ℝ) ≤ -(t / 2 * Real.log π) * 2 ^ 64 := by
    have := mul_le_mul_of_nonneg_left lp2 (by positivity : (0 : ℝ) ≤ t / 2)
    linarith
  have m4hi : -(t / 2 * Real.log π) * 2 ^ 64 ≤ -(t / 2) * (LPLO : ℝ) := by
    have := mul_le_mul_of_nonneg_left lp1 (by positivity : (0 : ℝ) ≤ t / 2)
    linarith
  have htarc : 2 * ((tn : ℝ) / 2 ^ tq) = 2 * t := by rw [ht]
  rw [htarc] at a1 a2
  constructor
  · have hφ := mul_le_mul_of_nonneg_right tb1 hP.le
    have : (t / 4 * L - 1 / 4 * Real.arctan (2 * t) - t / 2 - t / 2 * Real.log π - 1 / (2 * t))
        * 2 ^ 64 = t / 4 * L * 2 ^ 64 + -(1 / 4) * Real.arctan (2 * t) * 2 ^ 64 + -t / 2 * 2 ^ 64
          + -(t / 2 * Real.log π) * 2 ^ 64 - 1 / (2 * t) * 2 ^ 64 := by ring
    linarith
  · have hφ := mul_le_mul_of_nonneg_right tb2 hP.le
    have : (t / 4 * L - 1 / 4 * Real.arctan (2 * t) - t / 2 - t / 2 * Real.log π) * 2 ^ 64
        = t / 4 * L * 2 ^ 64 + -(1 / 4) * Real.arctan (2 * t) * 2 ^ 64 + -t / 2 * 2 ^ 64
          + -(t / 2 * Real.log π) * 2 ^ 64 := by ring
    linarith

end

end H1000Line
