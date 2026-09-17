# Trivial Zeros and the Archimedean Localization of RH — a formalized theory

*2026-09-16. `conjecture1_proved = False`. Unconditional facts localizing the
trivial zeros to the archimedean place; they neither prove nor approach RH — they
localize precisely what RH is *not* about.*

## Thesis
The "trivial" zeros of ζ (at −2, −4, −6, …) carry **no arithmetic information**:
they are the poles of the archimedean factor `Γℝ(s) = π^(−s/2)Γ(s/2)`, and they
vanish in the completed picture. RH is a statement about the completed function's
zeros alone; the trivial zeros localize the difficulty entirely to the
**arithmetic / companion** part.

## Verified core (kernel-checked, 3-axiom clean)
`telperion/examples/trivial_zero_localization/lean/TrivialZeroLocalization.lean`,
compiled against Mathlib v4.32; `#print axioms = [propext, Classical.choice,
Quot.sound]`, 0 sorryAx:

- **`gammaℝ_zero_at_trivial`**: `Γℝ(−2(n+1)) = 0` — the archimedean factor vanishes
  at the trivial-zero locations (Mathlib's junk-value encoding of the Γ pole).
- **`zeta_trivial_zero`**: `ζ(−2(n+1)) = 0` (Mathlib).
- **`trivial_zero_is_archimedean`** (the localization): `ζ(−2(n+1)) =
  completedRiemannZeta(−2(n+1)) / Γℝ(−2(n+1))` **and** `Γℝ(−2(n+1)) = 0`. So ζ
  vanishes there because the archimedean denominator vanishes (`ζ = Λ/0`); the
  completed function `Λ` is unconstrained. The zero is an archimedean artifact.

## The deep form is already in the corpus
The trivial-zero localization at the level of the RH-equivalent Li coefficients is
`taylorCoeff_riemannXi_split` (#463): `λₙ = 1 + taylorCoeff(companion)ₙ +
taylorCoeff(Γℝ)ₙ`, with the **archimedean (Γℝ / trivial) part bounded** by
`taylorCoeff_Gammaℝ_re_growth` (#519): `|Re taylorCoeff(Γℝ)ₙ − (n/2)log n| ≤ 8n`.
That is the localization made quantitative: the archimedean part is split off and
controlled; RH lives entirely in the **companion** remainder.

## The three roles of the trivial zeros (honest assistance, not a proof)
1. **Archimedean shadow** — complete the function (ξ/Λ); the trivial zeros disappear.
2. **Localization** — the archimedean place is fully known, so RH's content is
   entirely at the finite/arithmetic places (the companion). Verified above and
   quantified by the Li split.
3. **Negative control** — the trivial zeros are *known off-line zeros*. Any
   reality-forcing / positivity argument must apply to Λ (which has none) and must
   NOT push ζ's trivial zeros onto Re = ½ — a built-in refutation test for wrong
   methods, in the program's negative-control discipline.

They calibrate, localize, and control; they do not supply the missing structural
theorem — because, being archimedean, they carry no arithmetic. `conjecture1_proved
= False`.
