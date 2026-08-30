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
