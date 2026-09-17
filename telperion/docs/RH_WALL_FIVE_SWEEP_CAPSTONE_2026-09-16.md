# The RH wall — a five-sweep no-go map, audited and corrected (campaign capstone)

*Five honest adversarial multi-agent sweeps (`wylptmzxv` weight, `wryhnwohw` ordinate,
`w0fy2g125` horizontal, `wu0aecd5x` joint, `wcrkqbzrj` non-self-dual GL(n)), then a sixth
**adversarial self-audit** (`w7m91imr9`, 19 agents, 6 attack axes × 2 skeptics + synthesis)
that tried to BREACH the map. Result: the substantive no-go claim **survived**, and the
audit **corrected three genuine overclaims in the prose**. `conjecture1_proved = False.`
This is a research no-go map with a kernel-verified core — not a kernel theorem that RH
resists every approach, and not a proof of RH.*

## Honest status header (read first)
- The **kernel-verified** part is small, exact, and true: the reflection/aggregate/razor
  theorems below, all `[propext, Classical.choice, Quot.sound]`, 0 sorry.
- "**Irreducible from every direction**" is a **research narrative**, not a kernel theorem:
  it is a survey of *existing* techniques (some source fetches rate-limited), and by
  construction it cannot foreclose a *future* occupant of the escape. `conjecture1_proved
  = False` concedes exactly this.
- The audit refuted the **letter** of the original FORCED-half prose (corrected below); the
  **substance** stands and is sharpened.

## The five directions (as surveyed)
| Direction | Sweep | Verdict (corrected) |
|---|---|---|
| Weight (multiplicative) | `wylptmzxv` | FREE — does no work |
| Ordinate (zero statistics) | `wryhnwohw` | ORTHOGONAL — reflection-blind |
| Horizontal (real-part) | `w0fy2g125` | FREE-OR-RH — one static landmark, no lever |
| Joint (real-part × ordinate) | `wu0aecd5x` | **CAPPED-AT-RH-EQUIVALENT** — Li/Weil positivity re-symmetrizes ρ with 1−conj ρ; the finite face is the Li ladder (λ₁..λ₂₀ ≥ 0, PR #411), the uniform ∀n is RH itself |
| Non-self-dual GL(n) | `wcrkqbzrj` | LANE CLOSES — trichotomy (per-zero→GRH, even-kernel→self-dual, odd-kernel→family-average); the even→self-dual step is temperedness-in-disguise (fails into the named temperedness wall) |

## The unifying theorem — corrected (kernel-verified core)
The original prose overclaimed: it slid from "the zero *set* is Klein-four-closed" to "every
Ξ-symmetric *functional* is invariant under ρ↦1−conj ρ." **That is a non-sequitur**, and the
audit built the counterexample (then `LiRazor` compiled it clean): the Bombieri–Lagarias/Li
term `F(ρ) = ‖1 − 1/ρ‖` is **conjugation-even, reality-diagnostic** (on/off the line ⇔ on/off
the unit circle), yet **functional-equation-odd** — the reflected partner `1−conj ρ` has
*reciprocal* modulus. So a reality-diagnostic functional CAN be conjugation-symmetric while
breaking the s↦1−s reflection.

The **kernel-true** statement is therefore restricted to functionals invariant under **BOTH**
reflections:

> `ReflectionForced.functional_constant_on_reflection_pair` — a real `F` invariant under
> **both** `z↦1−z` **and** `z↦conj z` is constant on `{ρ, 1−conj ρ}`, so cannot separate an
> off-line zero from an on-line one.

with the **aggregate** companion

> `FamilyReflectionBlind.symmetric_stat_reflection_blind` — any real functional of the zero
> *multiset* is identical on a reflection-closed family and its mirror,

and the razor that explains *why the criterion is exact*, not approximable:

> `LiRazor.critical_line_iff_unit_normSq` — a zero is on the line ⇔ its Li-summand base
> `1−1/ρ` sits exactly on the unit circle; `offline_left_geometric_blowup` — an off-line-left
> zero puts it outside, giving `rⁿ` blow-up (r>1) that no finite prefix of rungs sees but the
> `∀ n` does.

All `[propext, Classical.choice, Quot.sound]`, 0 sorry. Together these say: a reflection-**even**
functional cannot separate the pair; a reflection-**odd** one (the Li term) separates it but,
summed over the reflection-closed multiset, **re-symmetrizes** (`symmetric_stat_reflection_blind`)
and forces reality only in the all-n aggregate `λ_n = Σ_ρ[1−(1−1/ρ)ⁿ] ≥ 0 ∀n`, which is
**RH-equivalent** (Li 1997). Neither route forces a **named** zero.

## What "force reality" must mean (corrected)
Replace "cannot force `Re ρ = ½`" with the accurate per-zero/named/all form:

> no reflection-symmetric **or** reflection-odd functional entering **robustly** can force a
> **NAMED** zero (or **ALL** zeros) onto the line; reflection-odd functionals force reality
> only in the RH-equivalent aggregate, reflection-even ones not at all.

Positive-proportion (Levinson–Conrey, ≥ 0.4128 on the line unconditionally) is the paradigm
case of the excluded class: it forces reality for a **counted density**, never a **named**
zero, and literally re-imports `ξ(s)=ξ(1−s)`.

## The escape — sharpened by the audit
The missing idea must be simultaneously:
1. **UNCONDITIONAL** — not a conditional positivity ⇔ RH equivalence (Li/Weil), not assuming GRH;
2. **PER-ZERO / NAMED** — force a single named zero's *real part*, not a proportion, count,
   ordinate, magnitude, or family average;
3. **REFLECTION-BREAKING WITHOUT RE-IMPORT** — break the functional-equation reflection per-zero
   via non-symmetric arithmetic entering non-robustly, **without** routing through the Weil
   explicit formula / Li coefficients / Weil positivity (all RH-equivalent and re-symmetrizing).

The audit found this escape **currently unpopulated** by any surveyed technique — every
candidate fails ≥1 clause (Connes/F_q intersection positivity, Miller highest-lowest zero,
the Li term, self-adjointness). The one place a reality-forcing positivity provably lives
*outside* reflection invariance is **Weil's Castelnuovo–Severi / Hodge-index intersection
positivity on `C × C` over `F_q`** — which needs a *second geometric dimension* (a surface,
Frobenius-as-correspondence) with **no known analogue over `Spec ℤ`**. That geometric object
is the concrete portrait of what the escape must supply, and its absence over ℚ is the
sharpest available statement of why the wall holds.

## What this is, and is not
- **Is:** a survey-grade no-go map with a small exact kernel core (reflection-even blindness,
  aggregate blindness, the unit-circle razor), sharpened by adversarial self-audit into a
  three-clause characterization of the missing idea and its geometric portrait (F_q intersection
  positivity absent over Spec ℤ).
- **Is not:** a proof of RH, and not a *kernel theorem* that RH is unreachable. `conjecture1_proved
  = False`. It cannot foreclose a future occupant of the escape; it states precisely what such an
  occupant must do and shows no current technique does it.
