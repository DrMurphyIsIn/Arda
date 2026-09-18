/-  ForgeTailTerms.lean -- ANDÚRIL cert-forge: the three EM tail-correction terms as w·B.

    `emZetaFinite3_eq_dirichlet` leaves three non-summand terms:
        T = N^{1-s}/(s-1) + N^{-s}/2 + b₂·s·N^{-s-1}/2.
    All three share the factor `w = N^{-s}`; factoring gives `T = w · B` with
        B = N/(s-1) + 1/2 + b₂·s/(2N)  (a fixed ℂ, exactly rational for s = 1/2 + it, t ∈ ℤ).
    Then, writing `w = P + iQ` (`P = Re(N^{-s}) = N^{-1/2}cos(t log N)`, `Q = Im`), the real/imag parts
    are `T.re = P·B.re − Q·B.im`, `T.im = P·B.im + Q·B.re` — LINEAR in the same `P, Q` the forge already
    boxes via a ζ-term box at n = N.  This file proves the factoring identity `tail_eq_wB` once,
    parametric in `s, N`; the forge instantiates `B` and boxes T.re/T.im from the n = N term box.

    conjecture1_proved = False.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Bernoulli

open Complex

namespace ForgeTailTerms

/-- **The tail-term factoring.**  For `N ≥ 1` (so `(N:ℂ) ≠ 0`) and `s ≠ 1`:
        N^{1-s}/(s-1) + N^{-s}/2 + b₂·s·N^{-s-1}/2 = N^{-s} · (N/(s-1) + 1/2 + b₂·s/(2N)).
    Proof: `N^{1-s} = N·N^{-s}` and `N^{-s-1} = N^{-s}·N⁻¹` (cpow_add / cpow identities), then field algebra. -/
theorem tail_eq_wB (s : ℂ) (N : ℕ) (hN : 1 ≤ N) (hs1 : s ≠ 1) :
    (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2
      = (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
          + (bernoulli 2 : ℂ) * s / (2 * (N : ℂ))) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  have hNr : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; ring
  -- N^{1-s} = N^1 · N^{-s} = N · N^{-s}
  have h1 : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + (-s) by ring, Complex.cpow_add _ _ hNc, Complex.cpow_one]
  -- N^{-s-1} = N^{-s} · N^{-1} = N^{-s} / N
  have h2 : ((N : ℝ) : ℂ) ^ (-s - 1) = (N : ℂ) ^ (-s) / (N : ℂ) := by
    rw [hNr, show (-s - 1 : ℂ) = (-s) + (-1) by ring, Complex.cpow_add _ _ hNc,
      Complex.cpow_neg_one, div_eq_mul_inv]
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h1, h2]
  field_simp

/-- **Tail-term real/imag parts as linear combos of `P = Re(N^{-s})`, `Q = Im(N^{-s})`.**  Given the
    factoring `tail_eq_wB` and that `B = (Bre:ℂ) + (Bim:ℂ)·I` (a per-instance `norm_num` check on the
    rational `B`), the real/imag parts of the tail-term sum are
        T.re = P·Bre − Q·Bim,   T.im = P·Bim + Q·Bre. -/
theorem tail_re_im (s : ℂ) (N : ℕ) (hN : 1 ≤ N) (hs1 : s ≠ 1) (Bre Bim : ℝ)
    (hB : (N : ℂ) / (s - 1) + 1 / 2 + (bernoulli 2 : ℂ) * s / (2 * (N : ℂ))
        = (Bre : ℂ) + (Bim : ℂ) * I) :
    ((N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2).re
      = ((N : ℂ) ^ (-s)).re * Bre - ((N : ℂ) ^ (-s)).im * Bim
    ∧ ((N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (bernoulli 2 : ℂ) * (s * (N : ℝ) ^ (-s - 1)) / 2).im
      = ((N : ℂ) ^ (-s)).re * Bim + ((N : ℂ) ^ (-s)).im * Bre := by
  rw [tail_eq_wB s N hN hs1, hB]
  constructor
  · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring

end ForgeTailTerms
