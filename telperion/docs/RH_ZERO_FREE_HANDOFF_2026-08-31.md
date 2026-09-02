# Handoff: RH zero-free-region formalization + Telperion emitter (2026-08-31)

`conjecture1_proved = False`. This is a research effort, NOT a proof of RH. Handoff for the next session.

## TL;DR

- **VERIFIED GREEN (kernel-checked, CI):** the `zero_free_bridge` positivity layer (20 theorems) **plus** the
  magnitude-layer *crude tier* (base case + reduction + input B). Commit `6333ce4` on `rh-research-artifacts`,
  `zero-free-bridge-compiles: success`.
- **VERIFIED (local):** `emit_zero_free_cosine` Telperion emitter (self-test + negative control + 4 pytest).
  PR #163 → main (auto-merge; see CI caveat below).
- **DRAFTED, UNVERIFIED (best-effort, sorry-free):** input R (`StripRepr.lean`) and Borel–Carathéodory
  (`borel_caratheodory/`, 398 lines) — the two hard analytic pieces, on `rh-research-artifacts`, NOT wired to
  CI (to protect the green build).
- **NOT DONE:** the sharp `|t|^{1-σ}` bound, the zero-free *region* (Phase 4 assembly), and RH itself.

## What's where (branch `rh-research-artifacts`, all pushed)

| File | State | Notes |
|---|---|---|
| `examples/zero_free_bridge/lean/ZeroFreeBridge.lean` | **GREEN** (24 thm) | positivity layer + magnitude crude tier |
| `examples/zero_free_bridge/lean/StripRepr.lean` | drafted, UNWIRED | input R conditional assembly `zeta_fract_repr_of` |
| `examples/borel_caratheodory/lean/BorelCaratheodory.lean` | drafted, own lakefile, UNWIRED | the crux, 12 theorems |
| `src/telperion/emit_zero_free_cosine.py` (+ test) | VERIFIED | new emitter; PR #163 → main |
| `docs/RH_*` | research artifacts | reassessment, first-principles review, feasibility, this handoff |

## The magnitude crude tier — CONFIRMED-WORKING Mathlib v4.32.0 API (from 4 CI rounds)

The base case + reduction + input B green after fixing (each a real root cause, in order):
1. `zeta_eq_tsum_one_div_nat_add_one_cpow` (NOT `riemannZeta_eq_…`) — ζ Dirichlet series, `1 < s.re`.
2. `Int.fract` is **measurable, not continuous** → `Measurable.aestronglyMeasurable` + `fun_prop` (fun_prop DOES
   handle `fract` + `cpow`).
3. **`open MeasureTheory`** — B is the first to use integrals; base uses `∑'` (root ns). Also `Complex.norm_real`
   (NOT `Complex.norm_ofReal`) + `Real.norm_of_nonneg` (NOT `abs_of_nonneg`) for the fract-nonneg step.
4. `((Int.fract x : ℝ) : ℂ)` (NOT `(Int.fract x : ℂ)`) — the latter makes Lean elaborate `Int.fract` at ℂ,
   demanding `LinearOrder ℂ`. Force real-first in the integral binder.

Other confirmed-present: `Complex.norm_cpow_eq_rpow_re_of_pos`, `integrableOn_Ioi_rpow_of_lt`,
`integral_Ioi_rpow_of_lt`, `setIntegral_mono_on`, `Integrable.mono'`, `norm_integral_le_integral_norm`,
`ae_restrict_mem`, `neg_div_neg_eq`, `analyticOn_riemannZeta : AnalyticOnNhd ℂ riemannZeta {1}ᶜ`,
`differentiableAt_riemannZeta`, `sum_mul_eq_sub_integral_mul` + `tendsto_sum_mul_atTop_nhds_one_sub_integral`
(AbelSummation), `hasDerivAt_integral_of_dominated_loc_of_lip`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

## Next steps (in order), for the next session

1. **Verify input R.** Wire `StripRepr.lean` as its OWN build target (do NOT `import` it into the green
   `ZeroFreeBridge.lean` — an R error would break the green build). Its `zeta_fract_repr_of` is a sorry-free
   *conditional* assembly (R4 `analyticOn_riemannZeta.mono` + R3 RHS-analyticity + R5 identity theorem), taking
   three hypotheses: **R1** (Abel-summation identity on `Re s>1`), **R2** (differentiation-under-integral), **R3**
   (preconnectedness of `{0<Re s}\{1}` — cover by 4 convex pieces + `IsPreconnected.union`). Discharging R1/R2/R3
   gives the fully-unconditional crude strip bound `|ζ(σ+it)| ≤ ‖s‖/‖s-1‖ + ‖s‖/σ`.
2. **Verify Borel–Carathéodory** (`borel_caratheodory/`, self-contained lakefile). Add its own CI job (mirror
   `zero-free-bridge-compiles`). It's the crux; drafted gap-free. NOTE (agent finding): Mathlib **master** now has
   BC (Radziwiłł, identical Möbius–Schwarz strategy) but v4.32.0 does NOT — our BC0 sphere→interior max-principle
   is the genuinely-novel part upstream omits. Known deviation: derivative constant is the honest
   `4(R+‖z‖)/(R−r)²` (same shape), not the sharp `2R/(R−r)²` (needs Poisson/mean-value).
3. **Phase 4 — the region.** With R and BC green: use BC to turn the `|ζ|` strip bound into a `|ζ'/ζ|` bound,
   feed the Layer-1 positivity `zeta_logDeriv_comb_nonneg`, optimize `δ∼c/log|γ|` → `σ > 1 − c/log|t|`. Mirror
   `zeta_boundary_contradiction`'s structure with the BC-derived `log|t|` background. HONEST: this region is
   already formalized externally (strongpnt, PrimeNumberTheoremAnd); the durable value here is `residue_logDeriv`
   + the cone/hinge characterization + (v4.32.0) BC.

## Honest ceiling (do not lose this)

The positivity layer is **Fejér-capped** (`a₁ < 2a₀`) and **shared** with Vinogradov–Korobov — it improves the
region *constant*, never the *rate*. RH's real frontier is the VK rate (VMVT — scale-recursive, absent from
Mathlib, NOT certificate/SOS-shaped) and ultimately Weil positivity `Δ(f⋆f*) ≥ 0`. No cosine polynomial, no
degree, no cleverer SOS reaches past `1 − O(1)/log|t|`. `conjecture1_proved = False`.

## Operational notes

- **CI is badly backlogged**; runs queue 20–40 min. The `concurrency` groups (added this session) cancel stale
  runs on new pushes — one build per commit. Do NOT tight-poll `gh run watch` (trips the API rate limit); use
  4-min-spaced single `gh run view`.
- **No local Lean builds** (SoC watchdog hazard) — CI-only verification.
- **arda_rust builds** must use `scripts/build_arda_rust.sh` (unrelated to this effort).
