# dVP Capstone — Handoff for Closing the Final Wiring (2026-09-07)

**For:** a fresh session tasked with writing the ONE remaining theorem — the concrete instantiation
of the de la Vallée Poussin zero-free region.
**Branch:** `bg/scl-lean`. Dir: `telperion/examples/zero_free_bridge/lean/`. HEAD ~`d93cac0`.
**Invariant:** `conjecture1_proved = False`. This is a *reduction*, NOT a proof of RH. Never commit
`sorry`. Every existing lemma is kernel-clean (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`). Merge to `main` via `gh pr merge --admin --merge`.

Read first: `DLVP_SESSION_RELAY_2026-09-07.md` (the corrected-target finding) and memory topic
`rh_dlvp_frontier_2026-09-04`.

---

## 0. What is done, and what this task is

**The reduction is mathematically complete.** Every analytic input and every connector is a proven
kernel-clean lemma (21 PRs, #279–#301). Your job is PURE ASSEMBLY: write

```lean
theorem dlvp_zeta_region_concrete (β γ : ℝ) (k : ℤ) (hβ : 1/2 < β) (hβ1 : β < 1)
    (hγ : «|γ| large enough») (hζ : riemannZeta ((β:ℂ) + (γ:ℂ)*I) = 0) («…mult k data…») :
    β ≤ 1 - 1 / (112 * (A * L))   -- for the A, L you choose = 1 - c/log|γ|
```

by instantiating `dlvp_zeta_region_of_bc_sums` (`DlvpZetaBcBridge.lean`). It has ~25 hypotheses;
every one has a proven producer (table in §3). The genuine difficulty is the NUMERIC COUPLING (§7),
not any individual hypothesis.

**DO NOT target `dlvp_zeta_region_of_canonical_decomp`** — it is over-constrained (one disk for both
heights; the height-2γ point is ≈|γ| from `c₀`). Target `dlvp_zeta_region_of_bc_sums`.

---

## 1. Geometry (fix these first)

- `c₀ := (2:ℂ) + (γ:ℂ)*I`   (height-γ centre; encloses the zero `ρ₀`)
- `c₁ := (2:ℂ) + ((2*γ:ℝ):ℂ)*I`   (height-2γ centre; a SEPARATE disk)
- `ρ₀ := (β:ℂ) + (γ:ℂ)*I`   (the zero; `ρ₀ - c₀ = β-2`, a negative real)
- eval points: `σ+iγ` (height γ, at distance `2-σ` from `c₀`), `σ+2iγ` (height 2γ, at distance `2-σ`
  from `c₁`, but ≈|γ| from `c₀`).
- `R`: the disk radius. Constraint `R ∈ (2-β, 3/2)` (nonempty iff `β>1/2`); `R < 3/2 = c₀.re - 1/2`.
- `R'`: the outer Jensen radius for the count, `R < R' < 3/2`.
- `|γ|` large: need `R' + 2 ≤ |γ|` (for c₀) and `R' + 2 ≤ |2γ| = 2|γ|` (for c₁, automatic), and
  `σ+2iγ ≠ 1`, `σ+iγ ≠ 1` (Im ≠ 0). Take e.g. `hγ : 4 ≤ |γ|` (so `R'+2 ≤ |γ|` for `R'<2`).

---

## 2. The target signature (paste-ready)

`dlvp_zeta_region_of_bc_sums (c₀ : ℂ) (σ A L β γ : ℝ) (k : ℤ) (R : ℝ)` needs, in order:
`hA:0<A`, `hL:1≤L`, `hk:1≤k`, `hσ_opt: σ-1 = 1/(2*(3*A+5*(A*L)))`, `hβσ: β<σ`,
`hf_mero: MeromorphicOn ζ (ball c₀ R)`, `hf'_mero: MeromorphicOn (ζ(c₀+·)) (ball 0 R)`,
`hpole_pf: (-deriv ζ σ / ζ σ).re ≤ (1/(σ-1)).re + A`,
then the **height-γ block**: `s₁ hs₁_dom hcz₁ hdiff₁ hbc₁ hm₁ ρ₀ hρ₀ hρ₀_eq hmρ₀ hother₁`,
then the **height-2γ block**: `s₂ hs₂_dom hcz₂ hdiff₂ hbc₂ hm₂ hlt₂`.
Conclusion: `β ≤ 1 - 1/(112*(A*L))`.

Note `hbc₁`/`hbc₂` use `A*L` literally (so set the `AL` of `hbc1_from_bounds` to `A*L`), and their sum
is over `s₁`/`s₂` = the divisor-support `hfin.toFinset` (height γ) resp. `∅` (height 2γ, htwo drops all).

---

## 3. Producer table (every hypothesis → its proven lemma)

| Hyp | Producer / how |
|---|---|
| `1∉closedBall c₀ R` | `one_notMem_closedBall_of_himc` (`DlvpZetaAnaFoundation`) from `R+2≤|c₀.im|` |
| `⟨g,D⟩` for c₀ | `obtain ⟨g,D⟩ := zeta_recentered_canonical_decomp c₀ R hR h1 (by simp : 1<c₀.re)` |
| `hf_ana` (ball 0 R) | `(zeta_recenter_ana_closedBall c₀ R h1).mono ball_subset_closedBall` |
| `hf_ana_cl` (closedBall c₀ R) | `zeta_analyticOnNhd_disk c₀ R h1` |
| `hf_mero` (ball c₀ R) | `hf_ana_cl.meromorphicOn.mono ball_subset_closedBall` |
| `hf'_mero` (ball 0 R) | `hf_ana.meromorphicOn` |
| `hg_ana` | `canonicalDecomp_analyticOnNhd D` |
| `hg_ne` | `canonicalDecomp_ne_zero D` |
| `hfin` | `by simpa [Function.support_neg] using D.meromorphicOn.divisor_ball_support_finite` |
| `hpole_pf` | `hpole_bounded` (∃ A₀, ∀ᶠ near 1) — extract A₀ + apply at your σ (σ→1, in nbhd) |
| `hcz₁`/`hcz₂` | `concrete_hcz σ γ` / `concrete_hcz σ (2*γ)` — but note `hcz₂` uses `((2*γ:ℝ):ℂ)`, check the cast matches (`ring` should close either way) |
| `hdiff₁`/`hdiff₂` | `differentiableAt_riemannZeta (by …σ+iγ≠1 via Im=γ≠0…)` (see `DlvpZetaGBound` for the `congrArg Complex.im` trick) |
| `hg_bound` (Bg, height γ) | `hg_bound_gamma hR hR2 hγ' D hz₀` → explicit `Bg = 4·log((2|γ|+11)/(2-π²/6))·(R+‖z₀‖)/(R-‖z₀‖)²` |
| `hcount` (C, height γ) | `sum_divisor_recenter_le_jensen hR hRR' (1<c₀.re) hR'lt himc hf_mero hf'_mero hf_ana_cl hfin` → `C = log(U''(R')/‖ζ c₀‖)/log(R'/R)` |
| `hbc₁` | `hbc1_from_bounds σ γ hR hσ1 hσ2 hσR g D hf_ana hg_ana hg_ne hfin heval_ne hg_bound hcount hAL_bound` |
| `heval_ne` | `by rw[concrete_hcz]; exact riemannZeta_ne_zero_of_one_le_re _ (by simp; linarith)` |
| `hm₁`/`hm₂` | `fun ρ _ => zeta_divisor_nonneg h1 ρ` |
| `hother₁`/`hlt₂` | image points are ζ-zeros with Re<σ: `zeta_zero_re_lt (1<σ) h1 hρball hdiv`, `hdiv` via `divisor_comp_const_add_apply` (see §5) |
| `hρ₀` | `ρ₀-c₀ ∈ support` (from `hmρ₀=k≥1≠0` via translate), then `Finset.mem_image ⟨ρ₀-c₀, _, hcz⟩` |
| `hmρ₀` | given (the zero's multiplicity data) |
| `s₁` | `hfin.toFinset` |
| `s₂`, `hs₂_dom` | `∅`, vacuous (`fun u hu => absurd hu (Finset.not_mem_empty u)`) |
| `hbc₂` | §4 — the intricate one |

---

## 4. `hbc₂` recipe (the height-2γ block, the one intricate connector)

`hbc₂` (with `s₂=∅`) is: `(-(logDeriv (ζ(c₀+·)) (σ+2iγ - c₀))).re ≤ A*L - 0`. Produce it via the
PARALLEL c₁-disk, because `σ+2iγ` is far from `c₀` but close to `c₁`:

1. Obtain `⟨g₁, D₁⟩` for `c₁=2+2iγ` (same recipe as c₀, with height `2γ`). Get its analyticity bundle,
   `hfin₁`, and the c₁ eval point `σ+2iγ - c₁ = σ-2`.
2. Build the c₁-disk BC-SUM: `hbc1_from_bounds σ (2*γ) …` for c₁ (note: `hbc1_from_bounds` hard-codes
   centre `2 + (2nd-arg)i`, so `σ (2*γ)` gives centre `2+2iγ = c₁`, eval `σ+2iγ`, eval-c₁ = `σ-2`).
   Its `hg_bound` = `hg_bound_gamma hR hR2 hγ₁ D₁ hz₀` at height `2γ` (Azeta gives `O(log|2γ|)=O(log|γ|)`);
   its `hcount` = `sum_divisor_recenter_le_jensen` at c₁.
3. Apply `htwo_shape_of_bc_sum c₁ σ γ (A*L) R hf_mero₁ hf'_mero₁ hfin₁.toFinset hs_dom₁ hcz₂(for c₁)
   hdiff₂ (the c₁ hbc1_from_bounds output) hm₁ hlt₁` → gives `(-deriv ζ (σ+2iγ) / ζ (σ+2iγ)).re ≤ A*L`.
   (`htwo_shape_of_bc_sum` reindexes, recentres, AND drops the zeros — that is why `s₂=∅` downstream.)
4. Convert that to `hbc₂`'s c₀-recentred form: the goal `(-(logDeriv (ζ(c₀+·)) (σ+2iγ-c₀))).re ≤ A*L-0`.
   `rw [neg_logDeriv_zeta_recenter_re c₀ (σ+2iγ-c₀) (by …), show c₀+(σ+2iγ-c₀)=σ+2iγ by ring]`, then
   `simp [Finset.sum_empty]`, then `exact` the step-3 result. (Or use `neg_logDeriv_recenter_eq c₀ c₁
   (σ+2iγ) hdiff₂` to bridge directly.)

**Watch:** `htwo_shape_of_bc_sum`'s output is already `Re(-ζ'/ζ(σ+2iγ)) ≤ AL`; you only need to
rewrite the c₀-recentred `logDeriv` (LHS of `hbc₂`) into that via `neg_logDeriv_zeta_recenter_re`.

---

## 5. Divisor-data details (`hother₁`/`hlt₂`/`hρ₀`)

For `ρ = c₀ + u` in the image (`u ∈ hfin.toFinset`): it's a ζ-zero with `Re < σ`.
- `ρ ∈ ball c₀ R`: `u ∈ ball 0 R` (supportWithinDomain), `‖ρ-c₀‖=‖u‖<R`.
- `divisor ζ (ball c₀ R) ρ ≠ 0`: `= divisor(ζ(c₀+·))(ball 0 R) u` (via
  `divisor_comp_const_add_apply c₀ hf_mero hf'_mero huball hρball`), which is `≠0` (u∈support).
- then `zeta_zero_re_lt (show 1<σ) h1 hρball hdiv : ρ.re < σ`.
`hρ₀`: `divisor ζ (ball c₀ R) ρ₀ = k ≥ 1 ≠ 0`, translate to `divisor(ζ(c₀+·))(ball 0 R)(ρ₀-c₀)≠0`, so
`ρ₀-c₀ ∈ hfin.toFinset`, so `ρ₀ = c₀+(ρ₀-c₀) ∈ image`. (`concrete_hzne`/`DlvpZetaConcrete` has the
support-membership pattern.)

---

## 6. `hz₀` and geometric facts

- `z₀ := σ+iγ - c₀`. `‖z₀‖ = 2-σ` (via `concrete_eval_eq` + `Complex.norm_real` + `abs_of_nonpos`).
  `hz₀ : ‖z₀‖ < R` from `hσR : 2-σ < R` (or `concrete_hz_mem`).
- `hR2 : R < 3/2` needed by `hg_bound_gamma`/`Azeta`.
- `hγ'` for `hg_bound_gamma`: `R + 2 ≤ |γ|` (height γ); for c₁ use `R + 2 ≤ |2γ|` (weaker, automatic).

---

## 7. THE NUMERIC COUPLING (the actual crux)

`σ` is determined by `A, L` through `hσ_opt: σ-1 = 1/(2(3A+5AL))`, yet `σ` also appears in the eval
points, `R-‖z₀‖ = R-(2-σ)`, and the `Bg`/count geometric factors. So `A, L, σ` interlock.

Constraints to satisfy simultaneously:
- `hpole_pf`: need `A ≥ A₀` where `A₀` is `hpole_bounded`'s constant (O(1), γ-independent).
- `hbc₁` `hAL_bound`: `C₁/(R-(2-σ)) + Bg₁ ≤ A*L`, where `C₁, Bg₁ = O(log|γ|)`.
- `hbc₂` analog on c₁: `C₂/(…) + Bg₂ ≤ A*L`.
- `hL: 1≤L`, `hA: 0<A`, `hβσ: β<σ` (follows from `σ>1>β`), `hσ2: σ≤2`, `hσR: 2-σ<R`.

**Suggested resolution.** Because `σ = 1 + 1/(2(3A+5AL))` is within `(1, 1+1/(6A)]`, it is bounded
away from 2 and `2-σ ∈ [1-1/(6A), 1)`, so `R-(2-σ) ≥ R-1 > 0` (R>1 since R>2-β, β<1). Hence the
denominators are bounded below by a γ-independent constant, and `C_i, Bg_i ≤ K·log|γ|` for a constant
`K`. Then:
- pick `A := max(A₀, 1)` (a fixed constant),
- pick `L := max(1, (C₁/(R-1) + Bg₁)/A, (C₂/(R-1) + Bg₂)/A)` — an explicit `O(log|γ|)` quantity ≥ 1,
- then `A*L ≥ C_i/(R-(2-σ)) + Bg_i` (since `R-(2-σ) ≥ R-1`), giving both `hAL_bound`s,
- `σ` is then defined by `hσ_opt` (it is an OUTPUT, define it as `1 + 1/(2(3A+5AL))`),
- verify `σ ≤ 2`, `2-σ < R`, `β < σ` (all from `σ ∈ (1, 1+1/(6A)]`, `R>2-β`, `β<1`).

The subtlety: `L` depends on `Bg_i` which depend on `σ` (via `R-(2-σ)` and the geometric factor),
which depends on `L`. Break the loop by bounding the geometric factors by their `σ→1` limits FIRST
(σ ∈ (1, 1+1/(6A)] gives `R-(2-σ) ≥ R-1` and `(R+‖z₀‖)/(R-‖z₀‖)² ≤ (R+1)/(R-1)²`), so `Bg_i ≤`
(γ-independent constant)·log(...) with NO σ-dependence — then `L` is a clean function of γ, and `σ`
follows. This is the one place that needs care; everything else is mechanical.

The final rate: `β ≤ 1 - 1/(112·A·L) = 1 - c/log|γ|` with `c = 1/(112·A·K)`.

---

## 8. Gotchas (collected across the 21 PRs)

- `hana` is on `closedBall`; pointwise-at-0/interior uses need `.mono ball_subset_closedBall` first
  (else `mem_ball_self` type-mismatches).
- `AnalyticOnNhd.divisor_apply f U z = ((analyticOrderAt f z).map ↑).untop₀`.
- `apply_eq_zero_of_analyticOrderAt_ne_zero` beta-reduces the lambda — pin `(f:=…)(z₀:=…)`.
- `e ▸ hf` rewrites the WRONG way for differentiability args; use `e.symm ▸ hf` (e : c+(s-c)=s).
- `IsBigO` isn't destructurable directly — use `Asymptotics.isBigO_iff.mp` to get the `∀ᶠ ‖f‖≤C‖g‖`.
- `norm_one` not `Complex.norm_one`; `Re z ≥ -‖z‖` via `Complex.re_le_norm` on `-z` (+ `Complex.neg_re`,
  `norm_neg`).
- `open MeromorphicOn` for `divisor`; `norm_sub_rev` not `Complex.norm_sub_rev`.
- `gcongr` for `a/b ≤ c/d`; put `hRz : 0 < R-‖z₀-0‖` in context so its positivity discharger fires.
- `concrete_*`, `hg_bound_gamma`, `Azeta_le_of_c0_2_gamma` are GENERAL in the height — instantiate the
  γ-arg with `2*γ` for the c₁ versions (no re-proving).
- `hbc₂`'s `((2*γ:ℝ):ℂ)` cast vs `(2*(γ:ℂ))` — reconcile with `push_cast`/`ring` where they meet.

---

## 9. Workflow

Iterate against a scratch file with `lake env lean Scratch.lean` (fast, no rebuild). Only after clean:
`#print axioms` must be `[propext, Classical.choice, Quot.sound]`. Then move to a real file, add a
`[[lean_lib]]` to `lakefile.toml` + a CI job in `.github/workflows/telperion-lean-e2e.yml` (copy an
`rh-dlvp-*` block), commit (trailer: `Co-Authored-By: Claude Opus 4.8 (1M context)` + the
`Claude-Session` line), push `bg/scl-lean`, `gh pr create` + `gh pr merge --admin --merge`.

The capstone is large but every arrow is a proven lemma. Build it in stages: (i) the two `⟨g,D⟩` +
analyticity bundles, (ii) `hbc₁`, (iii) `hbc₂`, (iv) `hpole`+divisor data, (v) the numeric coupling +
final `exact dlvp_zeta_region_of_bc_sums …`. Land each stage as its own kernel-clean lemma if it helps.
`conjecture1_proved = False` — you are closing a REDUCTION, not proving RH.
