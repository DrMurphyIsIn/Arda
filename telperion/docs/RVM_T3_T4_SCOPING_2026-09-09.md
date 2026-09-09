# Riemann–von Mangoldt (T3) → Effective Backlund (T4) → Band Template (T5): Scoping

**Goal of the chain.** T5 replaces every per-band winding+`hArb` bundle with line-only sign
enclosures — the 10× lever on the T=10⁶ campaign.  It rests on T4 (effective `|S(T)| ≤ a log T + b`),
which rests on T3 (`N(T) = θ(T)/π + 1 + S(T)`).  `conjecture1_proved = False` throughout.

## T3: `N(T) = θ(T)/π + 1 + S(T)`

**What is DONE (on main, kernel-clean):**
* `DiffractionCore.bd_logDeriv_zeta_eq_count` — **the ζ-side argument principle**: the box-boundary
  winding of `ζ′/ζ` equals `2πi·(box zero-count)`.  This IS the left side of RvM in box form.
* `ZeroFreeBridge.riemannSiegelTheta` + `thetaIntegrand_eq_re_logDeriv_gammaR` — `θ` and its
  identification as the boundary integral of `Re logDeriv Γℝ` on the critical line (the Γ-side).
* `logDeriv_zeta_add_gammaR` — the `Λ = ζ·Γℝ` log-derivative split (couples the two sides).
* `zeta_zero_iff_completed_zero_of_im_ne` — ζ-zeros ↔ Λ-zeros off the real axis (zero correspondence).
* `zeta_zero_count_strip` — Jensen count `N = O(log T)` (bounds `S`'s range indirectly).

**What REMAINS (research contour, ~days):**
1. **The rectangle geometry.** Apply the argument principle to the ENTIRE completed function on
   `[a, 1-a] × [0, T]` (or its FE-folded half), not just `ζ`.  `Λ = Γℝ·ζ` has the box zeros of `ζ`
   plus the Γℝ contribution; `Λ₀` (Mathlib `completedRiemannZeta₀`, entire) is the pole-free carrier.
2. **The boundary split.** `arg Λ` change around ∂box = `arg Γℝ` change + `arg ζ` change; the first
   → `2·θ(T)` (both vertical Γ-edges, via `riemannSiegelTheta_deriv` + the Archimedean bridge), the
   second is `2π·S` BY DEFINITION of `S` as the ζ-argument remainder.  The `+1` is the `s(s-1)/2`
   polynomial factor's winding (one zero-pair contribution at the real axis).
3. **The half-line limit.** RvM is the `σ₀ → −∞` / FE-symmetrized form; the box statement above is
   its finite-rectangle precursor.  Defining `S(T)` as a continuous argument requires a
   branch-tracking or winding-number definition on the ζ-edge (Mathlib has no continuous `arg`
   along a path yet — this is the true gap).

**Honest status: the ζ-side and Γ-side are BOTH kernel-clean; assembling them into the classical
`N = θ/π + 1 + S` needs the rectangle-geometry bookkeeping + a path-argument definition of `S`.**

## T4: effective `|S(T)| ≤ a·log T + b` (explicit `a, b`)

Backlund's proof = OUR dVP toolbox on a rectangle: bound `Re log ζ` by `zeta_strip_bound` (have),
count sign changes of `Re ζ` on verticals via Jensen (`zeta_zero_count_strip`, have), transfer via
Borel–Carathéodory (`DlvpBCDeriv`, have).  Once T3 defines `S`, T4 is an assembly of existing
kernel atoms — the crux is T3's `S`-definition, not new analysis.  Turing's sharper integral form
(`|∫ S| ≤ 2.30 + 0.128 log(t/2π)`) is an optional later refinement.

## T5: the band template

With T3+T4: a band `[T_k, T_{k+1}]` certifies from (i) rational sign enclosures of `Λ(1/2+it)` on
a grid (lower bound on count, via `XiLineZeros` IVT — HAVE), and (ii) `N(T_{k+1}) − N(T_k)` from
T3+T4 (upper bound).  Pinch ⟹ exact count ⟹ the `hbands` conclusion of the tiled capstone, with
NO contour integral and NO `hArb` bundle — line-only Arb input.  Drop-in for
`all_nontrivial_zeros_on_line_tiled`.

## Recommended order
T3 rectangle-geometry + `S`-definition (the one hard piece) → T4 assembly (mostly existing atoms) →
T5 template → re-rate the ladder → the 10⁶ run.  The corridor (Summit 1) is independent and can
proceed in parallel (C1 disk bound + C3 near-sum assemble with tonight's C2 + ψ-shift).
