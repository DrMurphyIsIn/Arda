# Scoping: Guinand–Weil in the kernel, rigorous Odlyzko–Schönhage, certified Bragg amplitudes

**Date:** 2026-09-12.  Companion to `MILLION_CAMPAIGN_2026-09-12.md`.
`conjecture1_proved = False` throughout.  These three fronts are the bridge from the
finite verification ladder to the Dyson quasicrystal picture — each scoped against
assets already on main.

---

## 1. Kernel formalization of the Guinand–Weil explicit formula

**Statement targeted** (test-function form): for suitable even g with transform h,

```
Σ_ρ h(γ_ρ) = (1/2π) ∫ h(r) (Γ-term)(r) dr + h(±i/2)-terms − 2 Σ_{p,m} (log p) p^{−m/2} g(m log p)
```

zeros ↔ primes + Archimedean.  This is THE structural identity behind the
diffraction/quasicrystal picture: the zero measure's Fourier transform is atomic
on {±m log p}.

**Assets on main** (grep-verified):
- The box argument principle on ξ + the RvM count assembly
  (`xiTele_winding_eq_RvM`, `riemannXi_winding_eq_RvM` — #427, li island) — the
  zero-side counting integral over rectangle edges.
- The Herglotz split `logDeriv ξ = Σ_ρ m(ρ)/(s−ρ) + entire` (zero-side kernel).
- `left_edge_prime_reflection` (#358): for Re s < 0 the left edge is EXPRESSED IN
  PRIMES with zero Arb inputs — the mirrored Dirichlet series + Γℝ terms.  The
  left edge of any explicit-formula box is structurally CLOSED.
- Right edge Re = 2: `−ζ′/ζ = Σ Λ(n) n^{−s}` absolutely convergent — the prime
  side proper; term-by-term integration is dominated-convergence bookkeeping.
- Γℝ edges: the branch-cut-free θ machinery (dVP T2 bricks, digamma integral).
- The Backlund kit (#484–#500): Jensen zero-counting near a point, confinement,
  partition — exactly the toolbox for the one open crux (below).

**The one hard open lemma** — the zero-avoiding-corridor bound: horizontal lines
T_j → ∞ avoiding zeros with `|ζ′/ζ(σ+iT_j)| = O(log² T_j)` uniformly on
−1 ≤ σ ≤ 2.  Classical proof shape: Herglotz/partial-fraction over zeros within
distance 1 (≤ O(log T) of them, by the Jensen brick already built) + choose T_j
between consecutive zeros.  This is Backlund-shaped: the same kit, run once more.

**Staged ladder (recommended):**
| Stage | Content | Cost |
|---|---|---|
| GW-finite | Fixed-rectangle identity: Σ_{|γ|≤T} h(γ) = right-edge prime sum + left-edge mirror + Γℝ edges + horizontal-edge remainders, remainders CARRIED EXPLICITLY as integrals (no limit taken) | 3–6 PRs, assembly of existing bricks, no new mathematics |
| Corridor | The `|ζ′/ζ| = O(log² T)` zero-avoiding lemma | 1 campaign, ~10–16 PRs (Backlund-sized) |
| GW-limit | T → ∞ along the corridor sequence; horizontal remainders → 0 against decaying h; monotone/dominated convergence of both sides | 3–5 PRs |
| GW-class | Clean statement for a concrete test class (Gaussians, or C_c^∞ in frequency) | 2–3 PRs |

Mathlib has no explicit formula in any form; GW-finite alone would be a first.
GW-finite is also all that certified Bragg amplitudes (§3) need.

---

## 2. Rigorous Odlyzko–Schönhage (the driver at large T)

**Finding (2026-09-12, verified on this machine):** the bundled libflint inside
our python-flint 0.6.0 already exports David Platt's rigorous FFT-amortized
machinery — `acb_dirichlet_platt_multieval`, `acb_dirichlet_platt_local_hardy_z_zeros`,
`acb_dirichlet_hardy_z_zeros` — the same ball-arithmetic multi-evaluation used
for the 3·10¹² numerical verification.  **This front is integration, not
research.**

**Plan:**
1. ctypes/cffi shim (python-flint 0.6.0 does not wrap these): expose
   `platt_local_hardy_z_zeros(T0, n, prec) -> [arb ball ordinates]` and the
   multieval grid `Z(t_k)` balls.  (~2–3 days incl. outward-rounding to the
   exact-dyadic rational extraction we already use.)
2. Wire into the line sweep: replace per-point `enclose_lambda` calls with one
   multieval per band; Z(t) sign boxes convert to Λ sign boxes through the
   (positive) |Γℝ| factor — or directly certify sign changes of Z.  Validation:
   byte-identical certificates on the [4000,8000] leg vs the current driver.
3. Payoff at height: per-point cost √T amortizes over ~√T grid points per call.
   At 10⁶ the projected driver cost returns to ~today's per-band seconds; at 10⁹
   it is the difference between 10⁴ core-years and feasible-on-a-cluster.
4. The off-line points (box/winding edges) stay per-point — mostly ELIMINATED
   anyway by the Turing/T5 template (edge-only certificates).

**Trust boundary unchanged**: Platt multieval is ball arithmetic inside FLINT —
the same Arb-certified non-kernel input class as `acb_zeta` today, documented
identically.

---

## 3. Certified truncated Bragg amplitudes (ADOPTED GOAL)

**Target artifact**: kernel-verified theorems of the shape

```
F_T(u) := Σ_{0<γ_k≤T} cos(γ_k u)   (T = 8000 today, 10⁶ at campaign end)
|F_T(m log p) − A_certified| ≤ ε_p    (peak: resonant growth ~ (log p / p^{m/2}) · T/2π · amplitude)
|F_T(u_off)| ≤ B ≪ peak               (off-peak control at certified sample points)
```

— the finite-volume diffraction pattern of the certified zeros, with Bragg peaks
at the log-prime frequencies and rigorous finite-size (~1/T-width) error bars.
The Dyson quasicrystal picture at finite T, machine-checked end to end.
(GW-finite from §1 supplies the *identity* connecting these peaks to primes;
Bragg certificates are meaningful even before GW lands.)

**Gap 1 — zero-ordinate width.**  Today's certificates place each zero inside a
sweep interval of width ~π/log T ≈ 0.3; at u = log 2 that is ±0.2 rad/zero —
useless in a 10⁶-zero sum.  Fix: a **refinement pass** — bisect each certified
sign-change interval to width δ (driver: ~log₂(0.3/δ) extra evals per zero;
kernel: the SAME IVT machinery emits the zero in the refined bracket).  δ = 10⁻⁶
costs ~21 evals/zero — absorbed by the Platt multieval grid (§2) at negligible
marginal cost.  Emit per-zero interval certificates `γ_k ∈ [a_k, b_k]`.

**Gap 2 — certified trig sums in Lean.**  Enclosing `cos(γ_k u)` from
`γ_k ∈ [a_k,b_k]` at rational u needs certified cos enclosures at rational
points: Taylor series with explicit Lagrange remainder (Mathlib has the
derivative bounds; a `cos_enclosure` norm_num-style lemma family is the work).
This is the main new Lean machinery — reusable far beyond Bragg.  (~1–2 weeks.)

**Gap 3 — scale.**  1.7M terms cannot be one norm_num sum.  Structure it exactly
like the height ladder: per-band partial sums (≤46 terms — one certified interval
box per band, emitted WITH the band), then a tree-fold of interval additions
across bands (cheap, associative, the height-chain trick applied to sums).  The
per-band Bragg box rides the same emitter pipeline; the fold is glue codegen.

**Ladder:** B0 refinement pass + per-zero brackets (driver, days) → B1 per-band
Bragg boxes at u ∈ {log 2, log 3, log 5, off-peak controls} (emitter + cos
machinery) → B2 cross-band fold to T = 8000 (headline #1: *first kernel-certified
diffraction snapshot of the zeta zeros*) → B3 ride the 10⁶ campaign — watch the
log-prime peaks sharpen with certified error bars at every height.

**Honesty**: finite-T diffraction only.  The pure-point property of the infinite
zero set is equivalent to RH-plus-explicit-formula and is NOT approached by any
finite T.  `conjecture1_proved = False`.

---

## Recommended sequencing across the three fronts

1. **Now**: continue the primary-route ladder (8000 → 20000) while building B0
   (refinement) + the §2 Platt shim — both driver-side, independent of Lean.
2. **Next Lean campaign**: GW-finite (assembly) + `cos_enclosure` (B1 prereq) —
   parallelizable, both bounded-risk.
3. **Then**: the corridor lemma (the one research-grade theorem on this page) —
   unlocks GW-limit, and with it the formal statement that the certified Bragg
   peaks ARE the prime side of the explicit formula.
4. **T5 Turing template** stays on the critical path for the 10⁶ run itself
   (MILLION_CAMPAIGN doc §Turing route).
