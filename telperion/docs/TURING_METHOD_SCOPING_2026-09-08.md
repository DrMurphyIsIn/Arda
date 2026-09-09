# Turing's Method: Formalization Scoping (2026-09-08)

**Question scoped.** Can the per-band certificates of the tiled capstone
(`AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line_tiled`, PR #341) be made
*height-uniform in shape* — a fixed "band template" whose only per-band content is fresh Arb
numbers — by formalizing Turing's method (Backlund/Turing bounds on `S(T)`)? And is the result a
drop-in for the tiling architecture?

**Answers up front.**
1. Drop-in: **yes by construction** — the tiled capstone consumes only per-band *conclusions*
   (`∀ ρ ∈ band box, ζ ρ = 0 → Re ρ = 1/2`); any Turing-band lemma producing that shape replaces
   the winding route with zero changes to #341.
2. Payoff: **a trust-surface and driver-cost reduction, not new mathematical reach.** The winding
   route already gives exact per-band counts. Turing's method would (a) delete the per-band
   4-edge contour integral `hwind` and the ~17-conjunct `hArb` integrability bundle, replacing
   them with *critical-line-only real sign enclosures* (the cheapest, most robust Arb inputs we
   have), and (b) make the certificate template literally uniform in the band index.
3. Cost: **one genuinely hard new formalization rung** (effective `|S(T)|`), one medium rung
   (effective `θ(T)`), on top of atoms we already own. Multi-session, parallelizable with the
   T-milestone program; NOT on the critical path for T = 200 (winding route works today).

`conjecture1_proved = False` throughout: Turing's method certifies *finite* height prefixes; the
Markov-style "uniform transition rule for all heights" would be RH itself (see the tiling
discussion — Voronin universality is the structural no-finite-alphabet obstruction).

---

## 1. The mathematics (what would be formalized)

Write `ξ`-side counting through the completed zeta `Λ`. For `T` not the ordinate of a zero:

```
N(T) = θ(T)/π + 1 + S(T)
```

* `N(T)` = number of zeros `ρ` with `0 < Im ρ < T` (in the strip),
* `θ(T) = Im logΓ(1/4 + iT/2) − (T/2)·log π` (Riemann–Siegel theta),
* `S(T) = (1/π)·arg ζ(1/2 + iT)` (continuously tracked from 2 along the standard path).

**Turing's insight:** you never compute `S`. Sign changes of the real function
`t ↦ Λ(1/2+it)` give a LOWER bound on the band count; the identity + an effective bound
(Backlund: `|S(T)| ≤ a·log T + b`; or Turing's sharper integral form
`|∫_{t₁}^{t₂} S| ≤ 2.30 + 0.128·log(t₂/2π)`) gives an UPPER bound; when they pinch to the same
integer, the count is exact — **from line-only data**.

## 2. Inventory — what exists (verified 2026-09-08, Mathlib v4.32 + this repo)

**Already BUILT in-repo (the lower-bound half is DONE):**
| Piece | Where | Status |
|---|---|---|
| `Λ(1/2+it)` real on the line | `LambdaLineReal.completedZeta_im_eq_zero` | kernel-clean, on main |
| IVT sign-change ⟹ `∃` on-line zeros (increasing list) | `XiLineZeros.lambda_zero_*` (rational sign enclosures as only Arb input) | kernel-clean, on main |
| Rectangle argument principle atoms | `BoxArgPrinciple`, `RHInBoxAnalytic.zeta_count_eq_winding_generic` | kernel-clean |
| Explicit strip growth `‖ζ‖ ≤ 6(1+log t)`-class bounds | `zeta_strip_bound`, `zeta_log_bound` | kernel-clean |
| Jensen zero-count `O(log γ)` | `DlvpZetaDisk.zeta_zero_count_unconditional`, `DlvpZetaCountStrip` | kernel-clean |
| Borel–Carathéodory + Cauchy derivative machinery | `DlvpBCDeriv`, `DlvpEntireBound`, `BorelCaratheodory` | kernel-clean |
| Pole notch `‖s−1‖ ≤ 1/16 ⟹ ζ ≠ 0` | `ZeroFreeBridge.riemannZeta_ne_zero_near_one` (PR #333) | kernel-clean |
| Digamma `ψ` | Mathlib `Analysis/SpecialFunctions/Gamma/Digamma.lean` | available |

**ABSENT from Mathlib (grep-verified):** Riemann–Siegel `θ`, Hardy `Z`, `N(T)`/Riemann–von
Mangoldt in any form, continuous-argument tracking, and effective **complex** Stirling (only the
real-sequence `Stirling.lean` + Bohr–Mollerup exist). Everything in §3 rungs T2–T4 is new.

**Key synergy.** Backlund's proof of `|S(T)| ≤ a log T + b` is *exactly* our dVP toolbox run on a
rectangle: bound `Re log ζ` by the strip growth bound (have), count sign changes of `Re ζ` on
verticals via Jensen (have), Borel–Carathéodory transfer (have). The dVP session's machinery was
built for the zero-free region, but it is the same kit Backlund uses. This is the main reason T4
is "hard" rather than "very hard".

## 3. The ladder (rungs, difficulty, owner-lane)

| Rung | Content | Difficulty | Notes |
|---|---|---|---|
| **T1** | *Band template* (winding route): package `rh_in_box_of_certificate` per band as one lemma with the band index and Arb numbers as the only parameters; feed `hbands` of the tiled capstone | **cheap** (packaging) | Do first; makes T=200 emission mechanical today. Driver + dVP lanes jointly |
| **T2** | Effective `θ(T)`: DEFINE `θ(t) := ∫₀ᵗ ((1/2)·Re ψ(1/4+iu/2) − (1/2)log π) du` via Mathlib digamma (no arg-tracking, no branch cuts), then effective two-sided bounds `θ(t) = (t/2)log(t/2π) − t/2 − π/8 + O*(explicit/t)` via Binet-type digamma estimates | **medium** | Self-contained real analysis; the integral definition is the branch-cut dodge |
| **T3** | The identity `N(T) = θ(T)/π + 1 + S(T)` in certificate form: rectangle argument principle for `Λ` (atoms exist) + `Gammaℝ` factor split; `S` DEFINED as the ζ-remainder (no independent arg needed) | **medium-hard** | Reuses `zeta_count_eq_winding_generic` architecture on `Λ`; `LambdaLineReal` handles the line edge |
| **T4** | Effective Backlund `|S(T)| ≤ a·log T + b` (explicit `a, b`) via strip bound + Jensen + BC | **hard** (the crux) | Multi-session; the dVP kit is the right tool. Turing's integral refinement optional later |
| **T5** | *Turing band lemma*: sign-change list in band `[T_k, T_{k+1}]` (XiLineZeros shape) + T2 + T3 + T4 pinch ⟹ band count exact ⟹ the `hbands` conclusion — **line-only Arb input** | **medium** (assembly) | Drop-in for #341's `hbands`; deletes `hwind`+`hArb` per band |

Total new-kernel estimate: T2+T3+T4 ≈ the effort-scale of the effective-dVP arc (PRs #306–#318),
i.e. multi-session but of a familiar shape, with T4 the only research-grade risk.

## 4. Drop-in wiring (design freeze)

`all_nontrivial_zeros_up_to_height_on_line_tiled` takes
`hbands : ∀ i < n, ∀ ρ, (a ≤ Re ≤ 1−a) → (b i ≤ Im ≤ b (i+1)) → ζρ=0 → Re = 1/2`.
Both discharge routes produce exactly this:

* **Winding route (today):** `rh_in_box_of_certificate` per band — inputs `hwind` (4-edge contour
  value `2πi·N_k`) + `hArb` bundle + on-line list `Ton_k`.
* **Turing route (after T5):** per band, a rational grid `t₀ < … < t_m` in `[T_k, T_{k+1}]` with
  certified SIGNS of `Λ(1/2+it_j)` (plus the T2/T4 explicit constants evaluated at the band ends).
  Lower bound = sign changes (IVT); upper bound = `θ/π + 1 + |S|` bound; pinch ⟹ every band zero
  is among the on-line ones.

No change to #341 in either case. The routes can coexist per band (e.g. Turing where the pinch
closes, winding fallback where it doesn't — near close zero pairs the sign grid may need refining).

## 5. Recommendation

* **Now:** T1 (band template) — unblocks T=200 emission with today's machinery.
* **Next kernel campaign (dVP lane):** T2 → T3 → T4 → T5 in order, as the trust-surface upgrade:
  final state = every tall certificate consumes only (i) rational sign enclosures on the critical
  line, (ii) the two winding-0 low boxes, (iii) kernel theorems. The 4-edge contour integrals and
  integrability bundles disappear from the trust boundary entirely.
* **Non-goal:** any uniform-in-height induction. Turing's method uniformizes the *template*;
  the *data* stays irreducibly per-band. `conjecture1_proved = False`.
