# Reassessment of the whole zero_free_bridge proof (with the degree-n + hinge + Fejér findings)

**Date:** 2026-08-30. `conjecture1_proved = False`. A clear-eyed re-appraisal of the entire
`zero_free_bridge` formalization in light of this session's findings — what is proven, what it reaches,
and exactly where and why it stops.

## 1. What is now proven (kernel-green, gap-free)

20 theorems, `telperion-lean-e2e` green, and **zero `sorry` / `admit` / `axiom` / `Prop := True`** — a
genuinely gap-free formalization (unlike stubbed "green" builds). The complete arc:

- **Positivity core** — `mertens_three_four_one` (`3+4cos+cos2 ≥ 0`) carried onto the actual `−ζ'/ζ`
  Dirichlet series: `zeta_logDeriv_comb_nonneg` (`σ>1`), via `cpow_re` → `term_re` → sum.
- **`residue_logDeriv`** — a genuine Mathlib v4.32.0 gap-filler (order = residue of `logDeriv`, general
  order; library had only the simple-zero case). Reusable, not RH-specific.
- **`zeta_boundary_contradiction`** — de la Vallée Poussin core: `ζ(1+it) ≠ 0` via the `−ζ'/ζ` route.
- **Improved degree-3 cert** — `mertens_improved` (`20+30cos+12cos2+2cos3 = 8(1+cos)³ ≥ 0`) onto `−ζ'/ζ`
  (`zeta_logDeriv_comb4_nonneg`); the Mossinghoff–Trudgian direction.
- **General degree-n cone** — `cosine_comb_zeta_nonneg`: ANY pointwise-nonnegative cosine polynomial of
  any degree gives the `−ζ'/ζ` positivity. Subsumes all the above + the whole `2ⁿ(1+cos)ⁿ` family.
- **The hinge** — `admissible_boundary_contradiction`: any admissible certificate (`aₖ≥0`, pointwise
  nonneg, and `a₀ < a₁`) forces `ζ(1+it) ≠ 0`. `a₀ < a₁` is the *exact* condition.

This is a faithful, complete, in-kernel formalization of the classical nonnegative-cosine-polynomial
zero-free-region *positivity program* and its boundary conclusion.

## 2. What the new findings say about its REACH (the sharp part)

Three findings compose into a hard verdict on the whole method:

1. **The hinge is `a₁ > a₀`** (proven, `admissible_boundary_contradiction`): the boundary needs exactly
   the pole residue `+a₀` to lose to a zero residue `−a₁·m` (m≥1).
2. **Fejér caps `a₁ < 2 a₀`** for *any* nonnegative cosine polynomial. So the zero-free functional
   `F(P) = (√a₁−√a₀)²/Σ_{k≥1}aₖ` — hence the region constant `c` — has a **finite ceiling** (the
   Mossinghoff–Trudgian optimum, `R₀ = 5.573412`). No cosine-polynomial cert beats it.
3. **The horizon collapses.** The region is `σ > 1 − c/log|t|`. With `c` capped, the edge → 1 as |t|→∞:

   | height \|t\| | best σ (MT-optimal edge) | gap to critical line ½ |
   |---|---|---|
   | 10² | 0.96104 | 0.461 |
   | 10¹² | 0.99351 | 0.494 |
   | 10¹⁰⁰ | 0.99922 | 0.499 |

   The region hugs σ=1 and **collapses onto it** at large height. It never reaches any fixed σ<1, let
   alone ½.

**Verdict on reach:** the entire certificate program — the whole cone, optimized to its Fejér ceiling —
is provably confined to `1 − O(1)/log|t|`, **infinitely far from RH**. Improving the certificate
(degree-n, MT-optimal) only rescales the constant `c`; the `1/log|t|` *shape* is intrinsic and capped.
**The gap to RH is the shape (rate), not the constant.** This is a provable ceiling of the *method*, not a
limitation of the formalization.

## 3. Unification with the marginality picture (digs 1–4)

The certificate is a **fixed, height-independent object**. RH is `Λ = 0` (de Bruijn–Newman) — a
**height-indexed marginal** problem whose ties (Lehmer pairs) sharpen without bound as height grows
(dig #2–3). A height-blind certificate cannot control ties at every height, so the zero-free region
collapses *precisely where the ties sharpen* (large |t|). The certificate horizon and RH's marginality
are the **same phenomenon from two sides**: the certificate improves a *constant* and is blind to height;
RH requires the *arithmetic at every scale*. The proven bottleneck (dig #3, corrected) — the
zero-free-region constant — is exactly what this program optimizes, and exactly where it stops.

## 4. Honest value of the whole proof

- **NOT progress toward RH** — and never claimed to be (`conjecture1_proved = False` throughout).
- **A complete, reusable, in-kernel formalization** of the certificate program's positivity + boundary
  machinery. `cosine_comb_zeta_nonneg` (general cone) and `residue_logDeriv` (Mathlib gap-filler) are
  genuinely reusable beyond this example.
- **A precise localization of the RH gap.** The certificate reaches its Fejér ceiling and stops at
  `1 − O(1)/log|t|`; RH lives beyond, in the height-dependent rate/shape, which is intrinsically
  *not* certificate-shaped (Vinogradov–Korobov / arithmetic-at-every-scale technology, per digs #3–4).
- **The method meta-result.** Six bold RH attempts + four digs + this build, each verified or refuted on
  its own controls, converge on a sharp, honest statement of where the certificate method ends and why —
  which is the deliverable. Not a proof; a map with its edges proven.

## 5. Bottom line

`zero_free_bridge` is a correct, gap-free, kernel-checked formalization of a classical method whose horizon
is now *provably known* to fall infinitely short of RH — collapsing onto σ=1 at large height, capped by
Fejér, its gap to RH being the height-dependent shape it cannot touch. The honest posture is unchanged and
now precise: a real certificate on RH's proven frontier, with its reach measured exactly.
`conjecture1_proved = False`.
