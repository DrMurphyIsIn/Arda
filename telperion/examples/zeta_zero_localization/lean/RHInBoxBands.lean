/-  BAND-ADDITIVITY + WIDTH-FOLD REDUCTION for the RH-in-a-box certificate.

    Two composition lemmas that sit ON TOP of `RHInBox.rh_in_box_of_certificate` (which itself
    consumes `RHInBoxAnalytic.zeta_count_eq_winding_generic`).  Both operate at the CONCLUSION
    level — "every zeta zero in box `B` lies on `Re = 1/2`" — so they glue the OUTPUTS of one or
    more `rh_in_box_of_certificate` calls without touching the argument-principle internals.

    ------------------------------------------------------------------------------------------------
    1. HEIGHT-TILING (`rh_box_two_bands`, `rh_box_of_bands`) -- the compute lever for HIGH boxes.

       A zero's `Im` lies in exactly one sub-band, so an RH-certificate on each of `n` consecutive
       height-bands `[b i, b (i+1)]` covering `[b 0, b n]` glues to an RH-certificate on the whole
       box.  This is what makes tall boxes tractable: each band carries its OWN (small) winding
       count and SHORT vertical edges, so the `n` per-band Arb certificates are cheap and
       independent (parallelizable), where a single full-height certificate would need the whole
       `N ~ (T/2π)·log T` winding and a length-`T` vertical contour at once.  Each band's premise
       is discharged by `RHInBox.rh_in_box_of_certificate` on that band (off-line vertical edges —
       no boundary obstruction), so the consumption of `zeta_count_eq_winding_generic` is genuine.

    2. WIDTH-FOLD (`rh_full_box_of_left_half`) -- halves the REGION to be certified, via #320's
       reflection family (`ZeroFreeBridge.riemannZeta_reflect_line_eq_zero`, `ρ ↦ 1 - conj ρ`,
       which preserves `Im`).  If every zeta zero in the CLOSED left half `[a, 1/2] × [T0,T1]` lies
       on `Re = 1/2`, so does every zeta zero in the full symmetric box `[a, 1-a] × [T0,T1]`:
       right-half zeros reflect into the left half at the same height.

       HONEST OBSTRUCTION (documented, not hidden).  Discharging the left-half premise `hleft` via
       the argument principle is NOT currently possible: a half-box `[a, 1/2] × [T0,T1]` has its
       RIGHT vertical edge ON the critical line `Re = 1/2`, exactly where the zeros are, so the
       `hArb` boundary-non-vanishing hypothesis of `zeta_count_eq_winding_generic`
       (`∀ y, riemannZeta (1/2 + i y) ≠ 0`) is FALSE — the contour passes through zeros.  So this
       lemma is a SOUND structural reduction (the symmetry really does halve the region), but its
       premise awaits an indented-contour ("keyhole") half-box certificate, which is a separate
       piece of complex analysis, not a re-instantiation of the existing box driver.  The
       DISCHARGEABLE compute win for high boxes is height-tiling (item 1), not this.

    conjecture1_proved = False.  These are kernel-verified glue/reduction lemmas, NOT a proof of RH.
-/
import Mathlib
import DlvpZetaSymmetry

open Complex

namespace RHInBoxBands

/-! ## Height-tiling (band-additivity). -/

/-- **Two-band glue.**  Split `[T0,T1]` at `Tm`.  If every zeta zero in the lower band
    `[σ0,σ1] × [T0,Tm]` lies on `Re = 1/2`, and likewise for the upper band `[σ0,σ1] × [Tm,T1]`,
    then every zeta zero in `[σ0,σ1] × [T0,T1]` lies on `Re = 1/2`.  (No ordering hypothesis on the
    corners is needed: a zero's `Im` is either `≤ Tm` or `> Tm`.) -/
theorem rh_box_two_bands (σ0 σ1 T0 Tm T1 : ℝ)
    (hlow : ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (T0 ≤ ρ.im ∧ ρ.im ≤ Tm) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2)
    (hhigh : ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (Tm ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) :
    ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  intro ρ hre him hz
  obtain ⟨hlo, hhi⟩ := him
  rcases le_or_lt ρ.im Tm with h | h
  · exact hlow ρ hre ⟨hlo, h⟩ hz
  · exact hhigh ρ hre ⟨le_of_lt h, hhi⟩ hz

/-- **General height-tiling.**  Given monotone band boundaries `b : ℕ → ℝ` and, for each of the `n`
    consecutive bands `[b i, b (i+1)]` (`i < n`), a certificate that every zeta zero in
    `[σ0,σ1] × [b i, b (i+1)]` lies on `Re = 1/2`, every zeta zero in the full box
    `[σ0,σ1] × [b 0, b n]` lies on `Re = 1/2`.  Proof: induction on `n`, peeling the top band and
    gluing with `rh_box_two_bands` at `b n`.  This is the composition that lets `n` cheap per-band
    `rh_in_box_of_certificate` results certify one tall box. -/
theorem rh_box_of_bands (σ0 σ1 : ℝ) (b : ℕ → ℝ) (hmono : Monotone b) (n : ℕ) (hn : 1 ≤ n)
    (hbands : ∀ i, i < n → ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) →
      (b i ≤ ρ.im ∧ ρ.im ≤ b (i + 1)) → riemannZeta ρ = 0 → ρ.re = 1 / 2) :
    ∀ ρ : ℂ, (σ0 ≤ ρ.re ∧ ρ.re ≤ σ1) → (b 0 ≤ ρ.im ∧ ρ.im ≤ b n) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  revert hn hbands
  induction n with
  | zero => intro hn _; exact absurd hn (by omega)
  | succ m ih =>
    intro _ hbands
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- n = 1 : the single band `i = 0`.
      subst hm0
      intro ρ hre him hz
      exact hbands 0 (by omega) ρ hre him hz
    · -- n = m+1, m ≥ 1 : peel the top band `[b m, b (m+1)]`, recurse on `[b 0, b m]`.
      intro ρ hre him hz
      obtain ⟨hlo, hhi⟩ := him
      rcases le_or_lt ρ.im (b m) with h | h
      · exact ih hmpos (fun i hi => hbands i (Nat.lt_succ_of_lt hi)) ρ hre ⟨hlo, h⟩ hz
      · exact hbands m (Nat.lt_succ_self m) ρ hre ⟨le_of_lt h, hhi⟩ hz

/-! ## Width-fold (region halving via the critical-line reflection). -/

/-- **Width-fold reduction to the left half-box.**  If every zeta zero in the CLOSED left half
    `[a, 1/2] × [T0,T1]` lies on `Re = 1/2`, then every zeta zero in the full symmetric box
    `[a, 1-a] × [T0,T1]` lies on `Re = 1/2`.  A right-half zero `ρ` (`ρ.re > 1/2`) is reflected to
    `1 - conj ρ` (real part `1 - ρ.re < 1/2`, imaginary part `ρ.im` unchanged) by
    `ZeroFreeBridge.riemannZeta_reflect_line_eq_zero`, landing it in the left half where the premise
    applies; the reflected point is on the line iff `1 - ρ.re = 1/2`, i.e. `ρ.re = 1/2`.

    Requires `0 < a` (so `0 < ρ.re < 1` for the reflection) and `a ≤ 1/2` (so the "full box" really
    contains the left half).  See the module header for why `hleft` is not currently dischargeable
    by the argument principle (right edge on the zero locus). -/
theorem rh_full_box_of_left_half (a T0 T1 : ℝ) (ha0 : 0 < a) (ha_half : a ≤ 1 / 2)
    (hleft : ∀ ρ : ℂ, (a ≤ ρ.re ∧ ρ.re ≤ 1 / 2) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2) :
    ∀ ρ : ℂ, (a ≤ ρ.re ∧ ρ.re ≤ 1 - a) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  intro ρ hre him hz
  obtain ⟨hre_lo, hre_hi⟩ := hre
  obtain ⟨him_lo, him_hi⟩ := him
  rcases le_or_lt ρ.re (1 / 2) with hle | hgt
  · -- Left half already: apply the premise directly.
    exact hleft ρ ⟨hre_lo, hle⟩ ⟨him_lo, him_hi⟩ hz
  · -- Right half: reflect `ρ ↦ 1 - conj ρ` into the left half.
    have h0 : 0 < ρ.re := lt_of_lt_of_le ha0 hre_lo
    have h1 : ρ.re < 1 := by linarith
    have hz' : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 :=
      ZeroFreeBridge.riemannZeta_reflect_line_eq_zero h0 h1 hz
    have hre' : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
      rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
      rw [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    have key : (1 - (starRingEnd ℂ) ρ).re = 1 / 2 :=
      hleft (1 - (starRingEnd ℂ) ρ)
        ⟨by rw [hre']; linarith, by rw [hre']; linarith⟩
        ⟨by rw [him']; exact him_lo, by rw [him']; exact him_hi⟩ hz'
    rw [hre'] at key
    linarith

end RHInBoxBands
