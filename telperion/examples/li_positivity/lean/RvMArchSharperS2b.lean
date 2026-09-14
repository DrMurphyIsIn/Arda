/-
RvMArchSharperS2b — Arc B (sharper archimedean Li constant), step S2b (scaffolding + crux hypothesis).

`Dseries m = ∑'_j (1 − r_j^m)/(2j+3)`, `r_j = (2j+2)/(2j+3) = 1 − ε_j`, `ε_j = 1/(2j+3)`, is the
`D`-series of the S1a difference identity.  The crux limit is
  `Dseries m − (1/2)·log m → γ − 1 + (log 2)/2`   (numerically `−0.0762107448185`).

This file lands the **exact one-dimensional reformulation** that reduces the 2-D limit to a clean
1-D sum, plus the summability/positivity infrastructure:

  * `Dterm_eq_geom` — the per-term geometric expansion `Dterm m j = ∑_{i<m} ε_j²·(1−ε_j)^i`
    (from S2a's singularity-free `one_sub_pow_div_eq_geom`).
  * `aCoeff i = ∑'_j ε_j²·(1−ε_j)^i` and `summable_aTerm` — each inner series is summable
    (dominated by `ε_j² ≤ 1/(2j+3)²`).
  * `Dseries_eq_sum_aCoeff` — **THE FUBINI REFORMULATION** `Dseries m = ∑_{i<m} aCoeff i`
    (finite outer sum commutes with the tsum via `Summable.tsum_finsetSum`).  Numerically verified:
    `aCoeff i · 2i → 1`, so `aCoeff i ~ 1/(2i)` and `∑_{i<m} aCoeff i − (1/2)log m` converges.

The final limit `Dseries m − (1/2)log m → γ − 1 + (log 2)/2` (equivalently
`∑_{i<m} aCoeff i − (1/2)Hsum m → γ − 1 + (log 2)/2 − γ/2 = C` for the fixed constant
`C = ∑_i (aCoeff i − 1/(2(i+1)))`) is packaged as the named predicate `DseriesAsymptotic` and left as
the single remaining analytic obligation (a Riemann-sum/integral comparison bridging
`aCoeff i` to `1/(2(i+1))`).  S3 proves the capstone conditionally on it; no `sorry` is committed.

conjecture1_proved = False: elementary real analysis; nothing here approaches RH.
-/
import Mathlib
import RvMArchSharperS1
import RvMArchSharperS2a

open Finset Filter Topology

namespace RvMWeierstrass

/-! ### The per-term geometric expansion -/

/-- `Dterm m j = ∑_{i<m} ε_j²·(1−ε_j)^i`, with `ε_j = 1/(2j+3)`.  From the singularity-free geometric
    identity `(1−(1−ε)^m)/ε = ∑_{i<m}(1−ε)^i` applied with `ε = ε_j` (`r_j = 1 − ε_j`). -/
theorem Dterm_eq_geom (m j : ℕ) :
    Dterm m j = ∑ i ∈ Finset.range m,
      (1 / (2 * (j : ℝ) + 3)) ^ 2 * (1 - 1 / (2 * (j : ℝ) + 3)) ^ i := by
  have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  set ε : ℝ := 1 / (2 * (j : ℝ) + 3) with hε
  have hε0 : ε ≠ 0 := by rw [hε]; positivity
  -- r_j = 1 − ε
  have hr : ratioR j = 1 - ε := by
    rw [ratioR, hε]; field_simp; ring
  -- Dterm m j = (1 − (1−ε)^m)·ε  and geometric expansion of (1−(1−ε)^m)/ε
  have hgeom := one_sub_pow_div_eq_geom ε hε0 m
  -- Dterm m j = (1 − r_j^m)/(2j+3) = ε·(1 − (1−ε)^m) = ε²·∑_{i<m}(1−ε)^i
  rw [Dterm, hr]
  have hEq : (1 - (1 - ε) ^ m) / (2 * (j : ℝ) + 3) = ε ^ 2 * ((1 - (1 - ε) ^ m) / ε) := by
    rw [hε]
    field_simp
  rw [hEq, hgeom, Finset.mul_sum]

/-! ### The 1-D coefficients `aCoeff` -/

/-- The inner-series summand `ε_j²·(1−ε_j)^i`. -/
noncomputable def aTerm (i j : ℕ) : ℝ :=
  (1 / (2 * (j : ℝ) + 3)) ^ 2 * (1 - 1 / (2 * (j : ℝ) + 3)) ^ i

theorem aTerm_nonneg (i j : ℕ) : 0 ≤ aTerm i j := by
  unfold aTerm
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  have hb : (0 : ℝ) ≤ 1 - 1 / (2 * (j : ℝ) + 3) := by
    have : (1 : ℝ) / (2 * (j : ℝ) + 3) ≤ 1 := by rw [div_le_one h3]; linarith
    linarith
  positivity

/-- Each inner series `∑'_j aTerm i j` is summable (dominated by `1/(2j+3)²`, base `≤ 1`). -/
theorem summable_aTerm (i : ℕ) : Summable (fun j : ℕ => aTerm i j) := by
  have hb : Summable (fun j : ℕ => (1 / (2 * (j : ℝ) + 3)) ^ 2) := by
    have h2 := summable_one_div_sq_succ
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) h2
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith [Nat.cast_nonneg j (α := ℝ)]
  refine Summable.of_nonneg_of_le (fun j => aTerm_nonneg i j) (fun j => ?_) hb
  unfold aTerm
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  have hble : (1 - 1 / (2 * (j : ℝ) + 3)) ^ i ≤ 1 := by
    apply pow_le_one₀
    · have : (1 : ℝ) / (2 * (j : ℝ) + 3) ≤ 1 := by rw [div_le_one h3]; linarith
      linarith
    · have : (0 : ℝ) < 1 / (2 * (j : ℝ) + 3) := by positivity
      linarith
  nlinarith [sq_nonneg (1 / (2 * (j : ℝ) + 3)), hble,
    sq_nonneg ((1 - 1 / (2 * (j : ℝ) + 3)) ^ i)]

/-- The 1-D coefficient `aCoeff i = ∑'_j ε_j²·(1−ε_j)^i`.  Numerically `aCoeff i · 2i → 1`. -/
noncomputable def aCoeff (i : ℕ) : ℝ := ∑' j : ℕ, aTerm i j

theorem aCoeff_nonneg (i : ℕ) : 0 ≤ aCoeff i :=
  tsum_nonneg (fun j => aTerm_nonneg i j)

/-! ### The Fubini reformulation -/

/-- **THE FUBINI REFORMULATION.**  `Dseries m = ∑_{i<m} aCoeff i`.  The finite outer sum commutes
    with the inner tsum (`Summable.tsum_finsetSum`), after the per-term geometric expansion. -/
theorem Dseries_eq_sum_aCoeff (m : ℕ) :
    Dseries m = ∑ i ∈ Finset.range m, aCoeff i := by
  unfold Dseries aCoeff
  -- rewrite each Dterm via the geometric expansion
  have hcongr : (∑' j : ℕ, Dterm m j)
      = ∑' j : ℕ, ∑ i ∈ Finset.range m, aTerm i j := by
    refine tsum_congr (fun j => ?_)
    rw [Dterm_eq_geom m j]
    rfl
  rw [hcongr]
  -- swap tsum with the finite sum
  exact Summable.tsum_finsetSum (fun i _ => summable_aTerm i)

/-! ### The crux limit, as a named obligation -/

/-- **The crux limit predicate (S2b).**  `Dseries m − (1/2)·log m → γ − 1 + (log 2)/2`.

    Numerically `−0.0762107448185`, verified to 12 digits.  Equivalent (via
    `Dseries_eq_sum_aCoeff` and `(1/2)(Hsum m − log m) → γ/2`) to
    `∑_{i<m}(aCoeff i − 1/(2(i+1))) → γ − 1 + (log 2)/2 − γ/2`, i.e. summability of
    `aCoeff i − 1/(2(i+1))` with the stated sum — a Riemann-sum/integral comparison between the
    point-mass sum `aCoeff i = ∑_j ε_j²(1−ε_j)^i` and `(1/2)∫_0^{1/3}(1−t)^i dt`.  This is the single
    remaining analytic obligation; S3 consumes it to prove the capstone. -/
def DseriesAsymptotic : Prop :=
  Tendsto (fun m : ℕ => Dseries m - (1 / 2) * Real.log m) atTop
    (nhds (Real.eulerMascheroniConstant - 1 + Real.log 2 / 2))

end RvMWeierstrass
