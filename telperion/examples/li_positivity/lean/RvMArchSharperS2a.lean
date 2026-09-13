/-
RvMArchSharperS2a — Arc B (sharper archimedean Li constant), step S2a.

Two elementary lemmas feeding the S2b crux limit:

  * `one_sub_pow_div_eq_geom` — the singularity-free geometric identity
      `(1 − (1−t)^m)/t = ∑_{i<m} (1−t)^i`   (for `t ≠ 0`),
    from `1 − u^m = (1−u)·∑_{i<m} u^i` with `u = 1−t`.  This is the design's "cleanest" route to
    `H_m = ∫_0^1 (1−(1−t)^m)/t dt = ∑_{i<m} 1/(i+1)` with NO removable singularity.
  * `oddSum_partial_sum` / `oddSum_sub_half_log_tendsto` — the **odd-harmonic asymptotic**
      `∑_{j<J} 1/(2j+3) − (1/2)·log J → γ/2 + log 2 − 1`,
    via `∑_{j<J} 1/(2j+3) = H_{2J+1} − (1/2)H_J − 1` (induction) and `Real.tendsto_harmonic_sub_log`.
    This is the constant `oddH = γ/2 + log 2 − 1 ≈ −0.0182449869893` used to assemble `C` in S2b.

conjecture1_proved = False: elementary real analysis; nothing here approaches RH.
-/
import Mathlib
import RvMArchGrowth

open Finset Filter Topology

namespace RvMWeierstrass

/-! ### The singularity-free geometric identity (S2a) -/

/-- **Geometric identity, singularity-free.**  For `t ≠ 0`,
    `(1 − (1−t)^m)/t = ∑_{i<m} (1−t)^i`.  (`1 − u^m = (1−u)∑ u^i`, `u = 1−t`, `1−u = t`.) -/
theorem one_sub_pow_div_eq_geom (t : ℝ) (ht : t ≠ 0) (m : ℕ) :
    (1 - (1 - t) ^ m) / t = ∑ i ∈ Finset.range m, (1 - t) ^ i := by
  have hgeom : 1 - (1 - t) ^ m = t * ∑ i ∈ Finset.range m, (1 - t) ^ i := by
    have := geom_sum_mul (1 - t) m
    -- `(∑ i<m, x^i) * (x − 1) = x^m − 1`, with `x = 1−t`, `x − 1 = −t`
    have hx : ((1 - t) - 1) = -t := by ring
    rw [hx] at this
    -- this : (∑ i<m, (1−t)^i) * (−t) = (1−t)^m − 1
    have : (∑ i ∈ Finset.range m, (1 - t) ^ i) * t = 1 - (1 - t) ^ m := by linarith [this]
    linarith [this, mul_comm (∑ i ∈ Finset.range m, (1 - t) ^ i) t]
  rw [hgeom, mul_comm, mul_div_assoc, div_self ht, mul_one]

/-- The finite sum `∑_{i<m} 1/(i+1)` is `Hsum m` — the polynomial-integral identity
    `H_m = ∫_0^1 ∑_{i<m}(1−t)^i dt = ∑_{i<m} 1/(i+1)` at the level of the *integrand's* term-by-term
    antiderivative (`∫_0^1 (1−t)^i dt = 1/(i+1)`).  Recorded as the definitional `Hsum`. -/
theorem Hsum_eq_sum_inv (m : ℕ) : Hsum m = ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) := rfl

/-! ### The odd-harmonic asymptotic (S2a) -/

/-- The finite odd-reciprocal sum `∑_{j<J} 1/(2j+3)`. -/
noncomputable def oddSum (J : ℕ) : ℝ := ∑ j ∈ Finset.range J, 1 / (2 * (j : ℝ) + 3)

/-- **Partial-sum identity.**  `∑_{j<J} 1/(2j+3) = H_{2J+1} − (1/2)H_J − 1`, by induction. -/
theorem oddSum_partial_sum (J : ℕ) :
    oddSum J = Hsum (2 * J + 1) - (1 / 2) * Hsum J - 1 := by
  induction J with
  | zero => simp [oddSum, Hsum]
  | succ J ih =>
    unfold oddSum at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have hHJ : Hsum (J + 1) = Hsum J + 1 / ((J : ℝ) + 1) := by
      unfold Hsum; rw [Finset.sum_range_succ]
    have h2J : Hsum (2 * (J + 1) + 1) = Hsum (2 * J + 1)
        + 1 / (2 * (J : ℝ) + 2) + 1 / (2 * (J : ℝ) + 3) := by
      unfold Hsum
      rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast; ring
    rw [hHJ, h2J]
    have hJ1 : ((J : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (J : ℝ) + 2) ≠ 0 := by positivity
    have h3 : (2 * (J : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- **THE ODD-HARMONIC ASYMPTOTIC (S2a).**
    `∑_{j<J} 1/(2j+3) − (1/2)·log J → γ/2 + log 2 − 1`. -/
theorem oddSum_sub_half_log_tendsto :
    Tendsto (fun J : ℕ => oddSum J - (1 / 2) * Real.log J) atTop
      (nhds (Real.eulerMascheroniConstant / 2 + Real.log 2 - 1)) := by
  -- rewrite via the partial-sum identity
  have hpe : (fun J : ℕ => oddSum J - (1 / 2) * Real.log J)
      = fun J : ℕ => (Hsum (2 * J + 1) - Real.log (2 * J + 1))
          - (1 / 2) * (Hsum J - Real.log J)
          + (Real.log (2 * J + 1) - Real.log J) - 1 := by
    funext J; rw [oddSum_partial_sum]; ring
  rw [hpe]
  -- piece 1: Hsum(2J+1) − log(2J+1) → γ
  have hbase : Tendsto (fun m : ℕ => Hsum m - Real.log m) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have := Real.tendsto_harmonic_sub_log
    refine this.congr (fun m => ?_); rw [Hsum_eq_harmonic]
  have hγ1 : Tendsto (fun J : ℕ => Hsum (2 * J + 1) - Real.log (2 * J + 1)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have hcomp : Tendsto (fun J : ℕ => 2 * J + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (f := fun J : ℕ => J) (g := fun J : ℕ => 2 * J + 1)
        (fun J => by omega) Filter.tendsto_id
    have hsub := hbase.comp hcomp
    refine hsub.congr (fun J => ?_)
    simp only [Function.comp_apply]; push_cast; ring_nf
  -- piece 2: Hsum J − log J → γ
  have hγ2 : Tendsto (fun J : ℕ => Hsum J - Real.log J) atTop
      (nhds Real.eulerMascheroniConstant) := hbase
  -- piece 3: log(2J+1) − log J → log 2
  have hlog : Tendsto (fun J : ℕ => Real.log (2 * J + 1) - Real.log J) atTop
      (nhds (Real.log 2)) := by
    have hbr : Tendsto (fun J : ℕ => Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) atTop
        (nhds 0) := by
      have hbase' := Real.tendsto_log_comp_add_sub_log (1 : ℝ)
      have hcomp : Tendsto (fun J : ℕ => (2 * J : ℝ)) atTop atTop := by
        apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        exact tendsto_natCast_atTop_atTop
      exact (hbase'.comp hcomp)
    have hrw : ∀ᶠ J : ℕ in atTop, Real.log (2 * (J : ℝ) + 1) - Real.log (J : ℝ)
        = (Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) + Real.log 2 := by
      filter_upwards [eventually_gt_atTop 0] with J hJ
      have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
      have h2J : Real.log (2 * (J : ℝ)) = Real.log 2 + Real.log (J : ℝ) :=
        Real.log_mul (by norm_num) (ne_of_gt hJpos)
      rw [h2J]; ring
    have hlim : Tendsto (fun J : ℕ =>
        (Real.log ((2 * J : ℝ) + 1) - Real.log (2 * J : ℝ)) + Real.log 2) atTop
        (nhds (Real.log 2)) := by
      have := hbr.add_const (Real.log 2); simpa using this
    exact hlim.congr' (hrw.mono (fun J h => h.symm))
  -- assemble: γ − (1/2)γ + log 2 − 1 = γ/2 + log 2 − 1
  have hfinal := (((hγ1.sub (hγ2.const_mul (1 / 2))).add hlog).sub_const 1)
  have hcst : Real.eulerMascheroniConstant - (1 / 2) * Real.eulerMascheroniConstant
      + Real.log 2 - 1 = Real.eulerMascheroniConstant / 2 + Real.log 2 - 1 := by ring
  rw [hcst] at hfinal
  convert hfinal using 2

end RvMWeierstrass
