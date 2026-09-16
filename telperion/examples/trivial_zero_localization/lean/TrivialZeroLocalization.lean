/-
TrivialZeroLocalization — the trivial zeros of ζ are an ARCHIMEDEAN artifact.

The "trivial" zeros of the Riemann zeta function at s = −2, −4, −6, … are not a
separate arithmetic phenomenon: they are exactly the locations where the
archimedean (Gamma) factor `Gammaℝ s = π^(−s/2)·Γ(s/2)` has a pole (Mathlib encodes
that pole as the junk value `Gammaℝ = 0`).  Since `ζ s = Λ s / Gammaℝ s` (the
completed function divided by the archimedean factor), ζ vanishes there BECAUSE the
archimedean denominator vanishes — `ζ = Λ / 0` — NOT because the completed,
arithmetic-carrying function `Λ = completedRiemannZeta` vanishes.  This is the
precise sense in which the trivial zeros carry no arithmetic information and
disappear in the completed picture: RH is a statement about Λ's zeros alone.

conjecture1_proved = False.  These are unconditional facts localizing the trivial
zeros to the archimedean place; they neither prove nor approach RH.  The DEEP form
of this localization — the Li-coefficient split λₙ = 1 + companion + Γℝ, with the
Γℝ (archimedean/trivial) part bounded (n/2)log n — already lives in the corpus as
`taylorCoeff_riemannXi_split` / `taylorCoeff_Gammaℝ_re_growth`.
-/
import Mathlib

namespace TrivialZeroLocalization

open Complex

private lemma trivial_arg_ne_zero (n : ℕ) : (-2 * ((n : ℂ) + 1)) ≠ 0 :=
  mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero n)

/-- **The archimedean (Gamma) factor vanishes at the trivial-zero locations.**
`Gammaℝ` takes Mathlib's junk value `0` at the negative even integers — the formal
encoding of the pole of `Γ(s/2)` there. -/
theorem gammaℝ_zero_at_trivial (n : ℕ) : Gammaℝ (-2 * ((n : ℂ) + 1)) = 0 :=
  Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by push_cast; ring⟩

/-- **The trivial zeros of ζ** (Mathlib): `ζ(−2), ζ(−4), ζ(−6), … = 0`. -/
theorem zeta_trivial_zero (n : ℕ) : riemannZeta (-2 * ((n : ℂ) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- **LOCALIZATION — the trivial zero is archimedean in origin.**
At every trivial-zero location `s = −2(n+1)`, `ζ s = (completed Λ) / Gammaℝ` with
`Gammaℝ = 0`: the vanishing of ζ is caused entirely by the archimedean factor's pole
(`ζ = Λ / 0`), and places no constraint on the completed function `Λ`.  The trivial
zeros are thus an artifact of the archimedean place, carrying no arithmetic content —
RH, a statement about Λ's zeros, is untouched by them. -/
theorem trivial_zero_is_archimedean (n : ℕ) :
    riemannZeta (-2 * ((n : ℂ) + 1))
        = completedRiemannZeta (-2 * ((n : ℂ) + 1)) / Gammaℝ (-2 * ((n : ℂ) + 1))
      ∧ Gammaℝ (-2 * ((n : ℂ) + 1)) = 0 :=
  ⟨riemannZeta_def_of_ne_zero (trivial_arg_ne_zero n), gammaℝ_zero_at_trivial n⟩

/-- **NEGATIVE CONTROL — the trivial zeros are off the critical line.**
`Re(−2(n+1)) = −2(n+1) ≠ 1/2`.  These are *known off-line zeros of ζ*, so any
reality-forcing / positivity argument on the closure map must be consistent with
them lying off `Re = 1/2` — a built-in refutation test (forge-the-witness
discipline): a method that would push these onto the line is thereby wrong. -/
theorem trivial_zero_off_critical_line (n : ℕ) :
    (-2 * ((n : ℂ) + 1)).re ≠ 1 / 2 := by
  have h : (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_re]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  intro he
  nlinarith [he, hn]

end TrivialZeroLocalization

#print axioms TrivialZeroLocalization.trivial_zero_is_archimedean
#print axioms TrivialZeroLocalization.gammaℝ_zero_at_trivial
#print axioms TrivialZeroLocalization.trivial_zero_off_critical_line
