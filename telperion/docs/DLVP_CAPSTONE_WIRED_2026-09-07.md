# dVP Capstone — WIRING DONE, numeric closing remains (2026-09-07)

> **UPDATE (2026-09-07, later): THE NUMERIC CLOSING IS ALSO DONE.** `dlvp_zeta_region_concrete`
> (`DlvpZetaConcreteClose.lean`, PR #306, kernel-clean, CI `rh-dlvp-concreteclose`) discharges `hnum`
> and `hpole` exactly per §7 below, and the dVP concrete zero-free-region reduction is now complete
> end-to-end. Two refinements vs the recipe below: (1) `hgb`/`hC` were NOT collapsed into a jensen
> bound — for the `∃ A L` form, `C₁,C₂` are just the actual divisor finsums (`hC = le_refl/.ge`), so
> `zeta_zero_count_strip` is not needed (the log RATE is not asserted). (2) Every big `set`-var must be
> `clear_value`d or tactics unfold huge terms → heartbeat timeouts; the theorem also needs
> `set_option maxHeartbeats 1200000`. The rest is exactly as written. `conjecture1_proved = False`.


**Supersedes the "PURE ASSEMBLY" framing of `DLVP_CAPSTONE_HANDOFF_2026-09-07.md`.** The assembly is
now a merged kernel-clean theorem. What remains is ONLY the numeric closing.

**Branch:** `bg/scl-lean`. Dir: `telperion/examples/zero_free_bridge/lean/`.
**Invariant:** `conjecture1_proved = False`. Reduction, NOT a proof of RH. No `sorry`. Every lemma
kernel-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Merge via
`gh pr merge --admin --merge`.

---

## What just landed (PR #303, merge 82d64c3)

`DlvpZetaConcreteWired.dlvp_zeta_region_concrete_wired` — the concrete instantiation of
`dlvp_zeta_region_of_bc_sums` for an actual ζ-zero `ρ₀ = β+iγ` (`β < 1`). Kernel-clean, CI job
`rh-dlvp-concretewired`. It discharges INTERNALLY, for both disks `c₀=2+iγ` and `c₁=2+2iγ`:
- both `CanonicalDecomp`s + analyticity bundles + `MeromorphicOn`s;
- `hbc₁` (height γ) via `hbc1_from_bounds`;
- `hbc₂` (height 2γ) via the parallel `c₁`-disk `hbc1_from_bounds` → `htwo_shape_of_bc_sum`
  (drops all zeros) → recentred to `c₀`-form via `neg_logDeriv_zeta_recenter_re`, `s₂=∅`;
- all divisor/geometry data for the concrete zero.

It concludes `β ≤ 1 - 1/(112·A·L)`. Its remaining hypotheses (the frontier) are exactly 4 families:
`hgb₁/hgb₂`, `hC₁/hC₂`, `hnum₁/hnum₂`, `hpole_pf`. Full signature: see the file (params
`σ A L β γ k R Bg₁ C₁ Bg₂ C₂` + `hA hL hk hσ_opt hβ1 hσ2 hR hβR himc0 hmρ₀`).

---

## The remaining task: one closing lemma `dlvp_zeta_region_concrete`

Choose `A, L`, discharge the 4 hypothesis families, feed `dlvp_zeta_region_concrete_wired`. Because
the pole neighborhood is non-explicit, the honest statement is EXISTENTIAL in a threshold:

```lean
theorem dlvp_zeta_region_concrete :
    ∃ Γ₀ : ℝ, ∀ (β γ : ℝ) (k : ℤ), 1/2 < β → β < 1 → Γ₀ ≤ |γ| →
      divisor riemannZeta (Metric.ball ((2:ℂ)+(γ:ℂ)*I) R?) ((β:ℂ)+(γ:ℂ)*I) = k → 1 ≤ k →
      ∃ A L : ℝ, 1 ≤ L ∧ 0 < A ∧ β ≤ 1 - 1 / (112 * (A * L))
```
(or, for the genuine dVP rate, conclude `β ≤ 1 - c / Real.log |γ|` for an explicit `c`; see §4.)
`R` should be chosen inside as a fixed function of `β` (e.g. `R := 7/4 - β/2 ∈ (5/4, 3/2)`), so it is
NOT a free parameter of the statement — set it, and `R'` (e.g. `R' := (R+3/2)/2`), internally.

### The 4 hypothesis families — how each is discharged

**`hgb₁` / `hgb₂` (TRIVIAL — one line each).** `hg_bound_gamma` IS the `∀ g, CanonicalDecomp → …`
witness. Set `Bg₁ :=` its RHS (with `z₀ = (σ:ℂ)+(γ:ℂ)*I - ((2:ℂ)+(γ:ℂ)*I)`), i.e.
`4 * Real.log ((2*|γ|+11)/(2-π²/6)) * (R + ‖z₀-0‖) / (R - ‖z₀-0‖)^2`, then
`hgb₁ := fun g D => hg_bound_gamma hR hR2 hγ D hz₀mem`. Needs `hR2 : R<3/2`, `hγ : R+2 ≤ |γ|`,
`hz₀mem : ‖z₀‖<R` (via `concrete_eval_eq`+`abs_of_nonpos`, `‖z₀‖=2-σ<R`). For `c₁` use `(γ := 2*γ)`
(so `Bg₂` has `2*|2γ|+11 = 4|γ|+11` in the log), `hγ₂ : R+2 ≤ |2γ|` (from `|2γ|=2|γ|≥|γ|≥R+2`).

**`hC₁` / `hC₂` (short — cast of `zeta_zero_count_strip`).** `zeta_zero_count_strip c₀ R R'` gives
`(↑(∑ᶠ u, divisor ζ (closedBall c₀ |R|) u) : ℝ) ≤ jensenRHS` (inner `r=R`, outer `R'`). Set
`C₁ := jensenRHS(c₀,R,R') = Real.log (((‖c₀‖+R')/(|c₀.im|-R') + (‖c₀‖+R')/(c₀.re-R'))/‖ζ c₀‖) /
Real.log(R'/R)`. Discharge `|R|=R`, `|R'|=R'` via `abs_of_pos`; `hRlt : R' < c₀.re-1/2 = 3/2`;
`himc : R'+2 ≤ |c₀.im| = |γ|`. Then `hC₁ := (zeta_zero_count_strip …)` after the `abs` rewrites
(the `∑ᶠ over closedBall c₀ |R| = closedBall c₀ R`). NB the wiring lemma's `hC₁` is stated with
`closedBall c₀ R` — the `|R|→R` rewrite matches it.

**`hnum₁` / `hnum₂` (THE CRUX — the numeric coupling).** `C_i/(R-‖z₀‖) + Bg_i ≤ A·L`. `‖z₀‖ = 2-σ`,
so `den := R-‖z₀‖ = R-2+σ`. Key decoupling (breaks the σ↔L fixpoint): `σ = 1 + 1/(2(3A+5AL))` gives
`σ ∈ (1, 1+1/(6A)]`, hence `2-σ ∈ [1-1/(6A), 1)`, hence `den > R-1 > 0` (R>1 since R>2-β>1) with NO
σ-dependence in the LOWER bound. So `C_i/den ≤ |C_i|/(R-1)` and `Bg_i ≤ 4·|Azlog_i|·(R+1)/(R-1)²`
(numerator `R+‖z₀‖ < R+1`, `1/den² ≤ 1/(R-1)²`). Both caps are γ-dependent-only (through the logs).
Now CHOOSE:
- `A := A₀` (the pole constant from `hpole_bounded`; if `A₀ ≤ 0`, take `A := A₀ ⊔ 1` and note
  `hpole_bounded`'s bound is monotone in A, so it still holds at the larger A);
- `L := max 1 ((|C₁|/(R-1) + Bg₁cap)/A) (…the c₁ analog…)` — an explicit `O(log|γ|)` quantity ≥ 1;
- then `A·L ≥ |C_i|/(R-1) + Bg_icap ≥ C_i/den + Bg_i`, giving both `hnum_i`.
`σ` is then DEFINED by `hσ_opt` (`σ := 1 + 1/(2(3A+5AL))`) — it is an OUTPUT, and `hσ2 : σ≤2`,
`hβR`, etc. follow from `σ ∈ (1, 1+1/(6A)]`. This is §7 of the old handoff, now the only analytic
bookkeeping left. `|C_i|` avoids needing `C_i ≥ 0`; `Bg_icap` uses `|Azlog_i|` to avoid needing
`Azlog_i ≥ 0` (both hold for large γ but the caps sidestep the sign proof).

**`hpole_pf` (needs σ in the pole neighborhood — source of the `∃ Γ₀`).**
`hpole_bounded : ∃ A, ∀ᶠ s in 𝓝[≠] 1, Re(-ζ'/ζ s) ≤ Re(1/(s-1)) + A`. Extract `⟨A₀, hA₀⟩`. The
`∀ᶠ` gives (via `Metric.eventually_nhdsWithin_iff` / `mem_nhdsWithin`) an `ε>0` with the bound for
`0 < ‖s-1‖ < ε`. For the real point `s = σ` (`σ>1`), `‖σ-1‖ = σ-1 = 1/(2(3A+5AL))`. Require `L`
ALSO `≥ (1/ε - 6A)/(10A)` (fold into the `max` above) so `σ-1 < ε` ⟹ `hpole_pf` holds at σ. The
`ε` (hence `Γ₀`) is non-explicit — this is why the theorem is `∃ Γ₀`, and why dVP's constant is
famously non-effective. `s = σ ≠ 1` since `σ>1`.

### `hmρ₀` / `hk` (the zero's multiplicity)

`k := divisor ζ (ball c₀ R) ρ₀`, `hmρ₀ := rfl`. `hk : 1 ≤ k` from `ζ ρ₀ = 0`: `analyticOrderAt ζ ρ₀ ≠ 0`
(`analyticOrderAt_eq_zero_iff`, `ζ ρ₀ = 0`) and `≠ ⊤` (ζ analytic, `≢ 0` on the connected disk —
nonzero at Re>1). `divisor_apply` = `(analyticOrderAt).untop₀ ≥ 1`. If painful, take `k, hk, hmρ₀`
as hypotheses of the closing theorem too (they are legitimately "the zero's multiplicity data").

## §4 — from `1 - 1/(112·A·L)` to the dVP rate `1 - c/log|γ|`

The wiring lemma gives `β ≤ 1 - 1/(112·A·L)`. With `A` constant and `L = O(log|γ|)` (an UPPER bound
`L ≤ K·log|γ|` is needed here, in addition to the lower bound from `hnum`), `1/(112 A L) ≥
1/(112 A K log|γ|) = c/log|γ|`. To get the clean rate you must prove `|C_i| ≤ K'·log|γ|` and
`|Azlog_i| ≤ K''·log|γ|` (from `U'' ≤ 2|γ|+11`, `‖ζ c₀‖` bounded below at `Re=2` by `2-π²/6`, and
`log(R'/R)` a positive constant). This is extra rational/log bookkeeping; if you only want the
`∃ A L` form, skip it.

## Gotchas confirmed this session (all in the merged file)

- `MeromorphicOn.mono` does not exist as dot-notation (unfolds to a Pi → tries `Function.mono`); use
  `MeromorphicOn.mono_set (h.meromorphicOn) ball_subset_closedBall`.
- `Finset.not_mem_empty` renamed → `Finset.notMem_empty`.
- `hbc1_from_bounds σ (2*γ)` reuses the height-γ producer for the `c₁=2+2iγ` disk verbatim (the
  `(↑(2*γ))` cast matches `((2*γ:ℝ):ℂ)` in `htwo_shape_of_bc_sum`).
- hbc₂ recipe (works): `rw [Finset.sum_empty, Complex.zero_re, sub_zero]`; build
  `hdc0 : DifferentiableAt ζ (c₀+(s₂pt-c₀))` by `rw [show …=s₂pt by ring]; exact hdiff₂`; then
  `rw [neg_logDeriv_zeta_recenter_re c₀ (s₂pt-c₀) hdc0, show c₀+(s₂pt-c₀)=s₂pt by ring]; exact htwo`.
- ζ≠1 at eval points via `congrArg Complex.re h; rw[hev_re] at this; simp at this; linarith`.
- Write the centres `(2:ℂ)+(γ:ℂ)*I` / `(2:ℂ)+((2*γ:ℝ):ℂ)*I` INLINE (no `set`) — `set`-folding vs
  the inline forms the producers emit causes `rw`/`exact` mismatches.

## Build/land

Iterate: `lake env lean Scratch.lean` (imports prebuilt oleans; ~fast, no Mathlib rebuild — Mathlib
`.olean` cache is present, so this is elaboration-only and safe, NOT a native build). Confirm
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. Then real file + `[[lean_lib]]` in
`lakefile.toml` + a `rh-dlvp-*` job in `.github/workflows/telperion-lean-e2e.yml` (copy the
`rh-dlvp-concretewired` block), commit (trailers: `Co-Authored-By: Claude Opus 4.8 (1M context)` +
`Claude-Session`), push `bg/scl-lean`, `gh pr create --base main` + `gh pr merge --admin --merge`.
