# First-principles review: the zero-free-region formalization — mapped, lit-extended, crux reassessed

**Date:** 2026-08-31. `conjecture1_proved = False`. A ground-up review of every theorem in
`zero_free_bridge`, a literature dive on the gaps, and a reassessment of the crux.

## 1. The map — 24 theorems, 0 `sorry`, in 3 layers + a foundation

The effort is a self-contained formalization of the **classical zero-free region**, which has three layers.

**Foundation (4, RH-independent, reusable):**
`logDeriv_congr_punctured` → `logDeriv_zpow_smul_split` → `tendsto_sub_mul_logDeriv_zero` →
**`residue_logDeriv`** (order = residue of `logDeriv`, general order). A genuine Mathlib v4.32.0 gap-filler.

**Layer 1 — Positivity (14 theorems). COMPLETE, kernel-green, Fejér-capped.**
- Dirichlet-series real part: `cpow_re` (`Re n^{−s} = n^{−σ}cos(t log n)`, the crux) → `term_re`.
- Degree-2 Mertens: `mertens_three_four_one` → `term_comb_nonneg` → `vonMangoldt_re_comb_nonneg` →
  `zeta_logDeriv_comb_nonneg` (positivity on `−ζ'/ζ`, σ>1) → `zeta_boundary_contradiction` (`ζ(1+it)≠0`).
- Degree-3 improved (Mossinghoff–Trudgian direction): `one_add_cos_pow_nonneg`, `mertens_improved`,
  `term_comb4_nonneg` → `vonMangoldt_re_comb4_nonneg` → `zeta_logDeriv_comb4_nonneg`.
- General cone: `shift_re`, `shift_im`, `cosine_comb_zeta_nonneg` (ANY pointwise-nonneg cosine poly) →
  `admissible_boundary_contradiction` (the hinge: `a₀<a₁` ⟹ `ζ(1+it)≠0`). Fejér caps `a₁<2a₀`.

**Layer 2 — Magnitude (4 theorems, IN PROGRESS).**
- `norm_one_div_natAddOne_cpow`, `norm_riemannZeta_le_re` (σ>1 base case, `‖ζ(s)‖ ≤ ζ(σ)`).
- `zeta_strip_bound_of` (reduction: crude strip bound from inputs R + B).
- `zeta_repr_integral_bound` (input **B** discharged: `‖∫_{x>1}{x}x^{−s−1}‖ ≤ 1/Re s`). Building (`25a267a`).
- Remaining: input **R** — the representation `ζ(s) = s/(s−1) − s∫_{x>1}{x}x^{−s−1}dx` on `0<Re s<1`.

**Layer 3 — Assembly (NOT STARTED).** Borel–Carathéodory + the optimization that turns Layer-1 positivity
+ a Layer-2 magnitude bound into the actual region `σ > 1 − c/log|t|`.

**Logical flow:** Layer 1 → boundary `ζ(1+it)≠0` (DONE). Layer 1 + Layer 2 + Layer 3 → region (NOT DONE).

## 2. Extended edges — literature dive (2 agents, sourced)

**Input R is BUILDABLE from existing Mathlib tools** (grade A+; Loeffler–Stoll 2503.00959 did theta →
continuation → functional equation → Euler product, but NOT R or any strip bound):
- `sum_mul_eq_sub_integral_mul` (`Mathlib.NumberTheory.AbelSummation`) — the `Re s>1` identity.
- `hasDerivAt_integral_of_dominated_loc_of_lip` (`…Calculus.ParametricIntegral`) — analyticity of the integral in `s`.
- `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (`…Analytic.Uniqueness`) — the identity theorem to
  extend from `Re s>1` to the strip. **R is assembly of existing tools, not a from-scratch build.**

**Layer 3 needs BOREL–CARATHÉODORY, which is ABSENT from Mathlib** (confirmed: no `borel_caratheodory`
/`BorelCaratheodory`; the closest is `PhragmenLindelof.vertical_strip`, not a drop-in). The classical
argument (Titchmarsh §3.8–3.10; Montgomery–Vaughan §6.6–6.7): a magnitude bound `|ζ|` on a disk → (Borel–
Carathéodory) → a bound on `|ζ'/ζ|` → combine with the Layer-1 positivity → optimize `δ∼c/log|t|` → region.
The **crude `|ζ|≪|t|` bound (R+B) suffices** to run it (worse constant); the sharp near-σ=1 `|ζ|≪log|t|`
(≈3–4× harder, Euler–Maclaurin with `N∼|t|`) only improves the constant.

**Meta (crucial honesty):** the zero-free REGION is **already formalized externally** — `strongpnt`
(`PNT4_ZeroFreeRegion.lean`) and `PrimeNumberTheoremAnd` (`ZetaBounds.lean`) both do it, via ad-hoc growth-bound
machinery (not Borel–Carathéodory, not in base Mathlib). So this is *not* new formalization territory.

## 3. The crux, reassessed

**The formalization crux MOVED.** It was "the magnitude bound / R." The lit dive shows R is now just
assembly of existing Mathlib tools. The genuinely-absent, load-bearing piece is **Borel–Carathéodory** — the
one theorem missing from Mathlib that the classical Layer-1-positivity→region argument cannot proceed without,
and that is broadly useful beyond this project. That is the sharp formalization crux.

**The honest novelty crux.** Because the region is already formalized in the PNT companion projects, this
effort's genuine additions are narrower than "a zero-free region": (i) **`residue_logDeriv`** (a real
general-order Mathlib gap-filler, upstreamable); (ii) the clean **general-cone + hinge (`a₀<a₁`) + Fejér-cap**
characterization of the positivity layer; and (iii) **Borel–Carathéodory itself**, if built, would be a
genuine Mathlib contribution. The self-contained region would duplicate known work; its value is pedagogical
+ the reusable pieces.

**The deep RH crux is unchanged** (three convergent verifications this session): the positivity layer is
Fejér-capped and *shared* with Vinogradov–Korobov; the region (classical or VK) is a bounded/analytic
improvement, not a step past the frontier; RH's real frontier is the VK *rate* (VMVT — scale-recursive,
absent from Mathlib, not certificate-shaped) and ultimately Weil positivity `Δ(f⋆f*)≥0` — neither
certificate-shaped nor near formalization. `conjecture1_proved = False`.

**One-sentence crux:** *finish R (now assembly) and formalize Borel–Carathéodory (the genuinely-missing
theorem) and the Fejér-capped positivity layer produces a zero-free region — but that region is already
formalized elsewhere, so the durable value is `residue_logDeriv` + the cone/hinge characterization + a
Borel–Carathéodory contribution, while RH's real frontier (VK rate → Weil positivity) stays untouched and
outside certificate/SOS methods.*
