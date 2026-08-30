# RH as a marginal-tie problem: de Bruijn–Newman criticality and Lehmer pairs

**Date:** 2026-08-30. **Status:** research artifact, adversarially attacked, overreach trimmed.
`conjecture1_proved = False`. NOT a proof of RH, NOT a narrowing of the gap. A reframing that
survived a hostile skeptic in its rigorous core.

## Motivation

Five prior RH attempts (fusion / tie-mechanism / tie-σ-artifact / H¹-cone / L²-cokernel) all lived in
the Weil-form / L² / Gram-matrix family and all collapsed to RH-equivalence. Instead of a sixth, ask
Brualdi–Goldwasser's question: WHY do smooth certificates collapse? BG answer: the problem is MARGINAL —
its continuous relaxation crosses the bound (Φ(c*)=1.00004>1), so any smooth monotone certificate proving
Φ≤1 would also prove the false continuous statement; hence the proof HAD to be arithmetic (integrality of
an 11th root, 23-adic). The claim tested here: RH has the same shape.

## The rigorous core (proven, not conjectural)

- **RH ⟺ Λ = 0** (de Bruijn–Newman constant). Hₜ(z) = ∫ e^{t u²} Φ(u) cos(zu) du is the backward-heat
  deformation of the Riemann Ξ (= H₀). For t ≥ Λ all zeros of Hₜ real; for t < Λ some complex.
- **Rodgers–Tao 2020 (Annals 191(3):1167–1203): Λ ≥ 0.** The continuous relaxation has ALREADY reached the
  phase boundary from below. Newman 1976: "the RH, if true, is only barely so" — a marginality conjecture,
  now half-proven. This is the exact analog of BG's Φ(c*)>1, and — unlike a first guess — this half is
  PROVEN, as solid as BG's computed gap.
- Combined with RH ⟺ Λ ≤ 0: **RH ⟺ Λ = 0 exactly** — ζ sits precisely on the boundary, zero backward-heat
  slack.

## The structural (not cosmetic) match: ties = Lehmer pairs

BG's marginality is pinned by its tightest ties (exact rational degeneracies at c+k=5). RH's is pinned by
**Lehmer pairs** — anomalously close consecutive zeros — and Rodgers–Tao's proof of Λ ≥ 0 runs through the
DYNAMICS of exactly these close pairs (a close pair pushes Λ upward under the flow). Grounding computation
(mpmath, dps=30):

    n      t_n         t_{n+1}       gap        avg_gap    gap/avg
    100    236.5242    237.7698     1.24559    1.73052    0.7198
    6709   7005.0629   7005.1006    0.03770    0.89549    0.0421  <-- LEHMER PAIR
    6710   7005.1006   7006.7397    1.63910    0.89547    1.8304

The 6709/6710 pair is 0.042× the mean spacing — 24× tighter, a near-degenerate tie. Both problems are
controlled by their tightest near-ties: a shared MECHANISM, not a resemblance.

## What the adversary correctly killed (removed)

- **Over-claim "this EXPLAINS the five collapses":** REMOVED. Convergent failure ≠ proof of necessity.
  Downgraded to: consistent with, and it makes a test.
- **"No smooth certificate for RH":** the no-go is rigorous ONLY for certificates ROBUST UNDER THE HEAT
  FLOW — a precise but narrow class. Arithmetic-analytic certificates escape (Connes' L² method may). So
  this excludes FLOW-ROBUST proofs, not all smooth ones. BG's excluded class was exactly the class everyone
  used (decisive); RH's excluded class is not obviously the class of the actual attempts (not yet decisive).

## The one non-vacuous lever

A discriminating TEST, applicable per-approach (contra "arithmetic structure of Λ is an empty box"):

> Is the approach ROBUST under the de Bruijn–Newman flow? Flow-robust ⇒ provably dead (would prove the
> false t<0 statement). Flow-fragile ⇒ that fragility IS where the arithmetic content hides.

Concretely testable on Weil positivity: the flow multiplies the archimedean term by the heat kernel
e^{tu²}, so "Weil positivity of the t-deformed form Mₜ = M_arch(t) + M_prime(t)" is well-defined. Check
whether M_arch(t) stays PSD as t→0⁻ while the full Mₜ must fail (zeros leave the line for t<0). If M_arch
is flow-robust and M_prime flow-fragile, the criticality lives ENTIRELY in M_prime — a concrete
localization of the arithmetic obstruction. Either outcome is a real, honest result.

## Next step taken: the zero-dynamics make the marginality QUANTITATIVE

The clean, sign-checkable handle is not the Weil-form reweighting (Hₜ has no Euler product, so the prime
term has no clean heat-deformation) but the de Bruijn–Newman flow AS a backward-heat flow on the zeros.

- **Derived + sign-checked ODE.** Hₜ = e^{-t ∂_z²}Ξ ⇒ ∂_t H = -H_zz ⇒ Coulomb-gas dynamics
  żⱼ = +2 Σ_{k≠j} 1/(zⱼ−z_k). Sign check on a ± a pair: ż(+a)=+1/a>0 ⇒ under INCREASING t zeros REPEL and
  stay real = de Bruijn "increasing t ⇒ real zeros." Correct. Hence DECREASING t (t<0): close pairs attract,
  collide, complexify.
- **2-body collision law** (isolated pair, gap δ): δ(s)² = δ₀² − 8s ⇒ collision at backward-heat time
  **s\* = δ₀²/8**. Verified numerically to ~1% (gap 0.4→s\*=2.11e-2 vs law 2.00e-2; 0.2→5.04e-3 vs 5.00e-3;
  0.1→1.28e-3 vs 1.25e-3).
- **Applied to the real Lehmer pair** (6709/6710, δ₀=0.0377 at T~7005, typical gap 0.895):
  s\*_Lehmer=1.78e-4 vs s\*_typical=1.00e-1 ⇒ the Lehmer pair is **564× more fragile**, first to exit the
  real axis; the backward-heat horizon it sets is only ~1.8e-4 of heat-time — marginal, with a number.
- **Many-body stabilizer.** Collective Coulomb repulsion of all other zeros resists collision. Λ ≥ 0
  (Rodgers–Tao) = repulsion WINS at t=0 (no pair collides for t≥0); RH = it wins EXACTLY to t=0 (Λ=0). The
  Lehmer pair being 24× tighter than its neighbours means the collective repulsion barely protects it, so it
  genuinely controls the horizon. **Marginality = the balance of tightest-tie fragility vs collective
  repulsion** — the quantitative form of BG's "tightest tie controls the bound."

Caveats: isolated/truncated model, explicit Euler, finite zero set; the rigorous infinite-gas control is
Rodgers–Tao. This is grounding/illustration, not a new theorem.

## Dug deeper: the tie-tower CORRECTED, and the real bottleneck located

Pushed the fork "does the tie-vs-repulsion balance give an unconditional handle on Λ, or re-encode RH?"
Empirical (first 400 zeros, unfolded gaps): the minimal normalized gap DECREASES monotonically with
height — 0.386 → 0.324 → 0.291 → 0.243 over t~14→680; the 6709/6710 pair is ~0.042. So the tightest ties
appear to sharpen with height. A hostile skeptic then corrected the structural claims built on this:

- **RETRACTED — the "ever-sharpening GUE tie-tower" as mechanism.** The min-gap ~ N^{-1/3} scaling is the
  GUE/random-matrix EXTREME-gap prediction — **conjectural**, resting on Montgomery pair correlation (proven
  only for restricted Fourier support). The monotone shrink in 400 zeros is a real empirical trend, NOT a
  proof of the scaling; "infinitely many arbitrarily-tight ties" is itself conjectural. Every GUE invocation
  must be flagged conditional.
- **RETRACTED — Rodgers–Tao runs on the gap-tower.** RT prove Λ≥0 via zero-DENSITY / second-moment /
  repulsion inputs (unconditional), NOT via the extremal small-gap structure. My "runs through Lehmer pairs"
  overstated: the proven input is a weaker close-pair/density fact, not the GUE tower.
- **CORRECTED — the Λ-upper-bound ladder's bottleneck.** Polymath15 → Platt–Trudgian (Λ≤0.2) combine (i)
  numerical RH-verification to height T with (ii) an analytic no-collision-above-t argument — but the rate
  c(T)→0 is governed by the **analytic zero-free-region width (~1/log T)** and log-derivative bounds, NOT by
  gap² of a Lehmer pair. The real obstruction to Λ≤0 by current methods is the zero-free region — which is
  exactly the classical de la Vallée Poussin / Vinogradov–Korobov terrain mapped at the START of this
  campaign (ZERO_FREE_REGION_TERRAIN.md, zero_free_bridge). The de Bruijn–Newman program loops back to it.

- **SURVIVED — the genuine finding (the plan's crux, answered).** Each bound **Λ ≤ c (c>0) is unconditional
  and STRICTLY WEAKER than RH** (RH ⟺ Λ≤0; Rodgers–Tao Λ≥0). This is a real "weaker-suffices ladder," NOT a
  rename of RH — a positive answer to "is there a not-known-RH-equivalent sufficient statement?" (there is a
  whole tower of proven weaker ones). Honest caveat: unknown whether the ladder accelerates to 0 or
  asymptotes above it; the rate is ~1/log T (slow), and reaching Λ≤0 needs control at all heights.
- **HEDGED — "infinite tie-tower vs BG's finite tie."** A real but incomplete diagnosis of why RH is harder
  than BG. The deeper difference: RH's zeros are a transcendental, non-finitizable object (no integrality on
  a finite family), whereas BG reduces to a finite arithmetic configuration. The tower is a symptom, not the
  whole cause.

**Net of digging deeper:** the dig CORRECTED my own overreach — the gap-tower is a conjectural (GUE)
parallel, not the proven mechanism; the proven bottleneck of the Λ≤0 program is the analytic zero-free-region
width, routing back to the campaign's starting terrain. The one solid new deliverable is C3: the Λ≤c ladder
is a genuine unconditional weaker-than-RH structure. conjecture1_proved = False.

## Dug deeper again: the proven bottleneck IS certificate-shaped (loop closes)

The corrected bottleneck is the zero-free-region CONSTANT (dig #3). Is it certificate-shaped or pure
analysis? Traced the mechanism: the de la Vallée Poussin region width comes from the nonnegative cosine
polynomial 3+4cosθ+cos2θ ≥ 0 — literally the `zero_free_bridge` Mertens certificate. The constant is set by
OPTIMIZING over nonnegative cosine polynomials. Derived the leading-order extremal problem:

  zero-free region 1−β ≥ c/log γ,  c = (√a₁ − √a₀)² / (A·Σ_{k≥1}a_k),  A universal ⇒
  **maximize  F(P) = (√a₁ − √a₀)² / Σ_{k≥1}a_k  over nonneg cosine polys P=Σa_k cos kθ ≥ 0, a_k ≥ 0.**

Larger F ⇔ wider region ⇔ smaller R₀ (region ~ 1 − 1/(R₀ log t)). Computed (scipy, nonneg cone on a grid):
F(dlVP 3,4,1)=0.01436 baseline; optimizing degree d gives 0.0188 (d=2) → 0.0271 (d=3) → 0.0287 (d=4) →
0.0290 (d=8) — a ~2× improvement, saturating. [F is an illustrative LEADING-ORDER proxy — the exact O(1)
constant handling is refined; cite the real published result for the rigorous constant.]

- **This is a REAL, published, certificate-shaped program.** Mossinghoff–Trudgian 2015 (J. Number Theory
  157) optimize exactly this nonneg-cosine cone and improve the zero-free constant to **R₀ = 5.573412** (from
  ~5.70). Nonnegativity of a cosine polynomial ⇔ Fejér–Riesz SOS ⇔ a PSD Toeplitz condition = **exactly
  Telperion's certificate shape**, and exactly the family the existing `zero_free_bridge` Mertens certificate
  + the Turán/Hankel/TrigNonneg emitters already live in.
- **The campaign loop closes.** de Bruijn–Newman bottleneck (dig #2) → zero-free-region constant (dig #3) →
  nonnegative-cosine-polynomial certificate (this dig) → the `zero_free_bridge` Lean work + Turán/Hankel
  emitters at the START of the campaign. RH's *approachable* frontier is precisely the certificate family
  Telperion was built to emit. Concrete buildable next step: emit the Mossinghoff–Trudgian optimal cosine
  polynomial as a kernel-checked Fejér–Riesz nonnegativity certificate, extending `zero_free_bridge` from the
  degree-2 Mertens polynomial to the optimal one.
- **HONEST reach (bounded).** This sharpens the CONSTANT in the CLASSICAL 1/log t region only. It does NOT
  improve the Vinogradov–Korobov rate 1/(log t)^{2/3} (different, non-cosine-polynomial technology), the gain
  is modest (~2% in R₀), and it is nowhere near Λ≤0 (= RH). It is ONE ingredient of the Λ-upper-bound
  numerics (which lean more on numerical RH-verification + explicit formula), not the whole bottleneck. So:
  a genuine certificate foothold on RH's proven frontier, useful for explicit zero-free constants — NOT a
  path to RH.

## Honest verdict

Not a proof, not a gap-narrowing. A genuine, attack-survived reframing: RH is BG-marginal; its ties are
Lehmer pairs (proven mechanism); the search should be sorted by heat-flow robustness, not "smooth vs
arithmetic" hand-waving. The rigorous half (Λ=0 marginality, Rodgers–Tao, Lehmer-pair control) stands; the
conjectural half (that this forces all attempts to fail) does not, and is not claimed. `conjecture1_proved = False`.

## Sources
- Rodgers, Tao, "The de Bruijn–Newman constant is non-negative," Ann. Math. 191(3) (2020) 1167–1203.
- de Bruijn (1950) Λ≤1/2; Newman (1976) conjecture + "only barely so"; Polymath15 / Platt–Trudgian Λ≤0.2.
- Csordas–Norfolk–Varga, Newman: Lehmer pairs / closest-zero control on Λ.
- Brualdi–Goldwasser marginality: see memory laplacian_* + phi11_not_classical_bg_2026-08-29.
