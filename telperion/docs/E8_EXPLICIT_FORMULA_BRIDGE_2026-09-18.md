# E8 explicit-formula bridge: `RH_limit_explicit_formula` proved on the `rvm_bridge` island (2026-09-18)

**Status: CLOSED.** The registry node `RH_limit_explicit_formula` (routes-roadmap milestone
E8 = B6 = D6, the unconditional Weil 1952 / Guinand 1948 explicit formula in the
Iwaniec-Kowalski Thm 5.12 normalisation, for every smooth compactly supported `g : ℝ → ℂ`) is
a kernel-checked theorem, `RvMBridge4.limit_explicit_formula` in
`telperion/examples/rvm_bridge/lean/E6Bridge4.lean`, stated verbatim (name, binders, body) as
`origin/rh/e8-statement:telperion/missions/rh/lean/Statements/RH_limit_explicit_formula.lean`,
over verbatim copies of the six `WeilExplicit.*` definitions of that branch's `RHDefs.lean`.
`#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`; no `sorry` anywhere in the
module, no `E6Bridge4WIP.lean` was needed.

**No RH progress is claimed.** This is the classical explicit formula, machine-checked; the zero
side is summed over the zeros wherever they are. `conjecture1_proved = False`.

Branch `rh/e8-proof` (worktree `/Users/peterwmurphy/arda-e8proof`), forked from
`rh/corridor-bound`; not pushed, no PR, `telperion/missions/` untouched.

## 1. What was proved

```lean
theorem limit_explicit_formula (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) :
    Integrable (WeilExplicit.archIntegrand g) ∧
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * WeilExplicit.weilKernel g ρ)
      (WeilExplicit.archSide g - WeilExplicit.primeSide g)
```

with (verbatim from the registry) `IsWeilTest g := ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
HasCompactSupport g`, `weilKernel g s := ∫ g u * exp((s − 1/2) u)`,
`zeroMult ρ := ((MeromorphicOn.divisor riemannZeta {0 < Re < 1} : ℂ → ℤ) ρ).toNat`,
`archIntegrand g r := weilKernel g (1/2 + r I) * (digamma (1/4 + (r/2) I)).re`,
`archSide g := weilKernel g 0 + weilKernel g 1 − g 0 · log π + (1/2π) ∫ archIntegrand g`,
`primeSide g := ∑' n, Λ(n)/√n · (g (log n) + g (−log n))`.

## 2. Why it is a normalisation bridge, not a new contour argument

The task brief asked first for an inventory of `Zeta23.WeilEF.*`. It contains the whole proof:
`Zeta23.WeilEF.EF_lit_zetaZeroConfig : Zeta23.EF.EF_lit zetaZeroConfig` (`WeilEF/Main.lean`),
where

```lean
def EF_lit (Z : ZeroConfig) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = literatureRHS k
def literatureRHS (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)
def gammaBracket (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π
```

with `zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ}` (`ζ ρ = 0 ∧ 0 < Re ρ < 1`),
`zetaZeroConfig.mult = Zeta23.zeroMult = (analyticOrderAt riemannZeta ·).toNat`,
`paperFT k z = ∫ k u * exp(I z u)`, `gammaOf ρ = (ρ − 1/2)/I`. Upstream, this is proved by the
rectangle contour on the completed zeta `Λ(s)` at good heights (`WeilEF/Contour.lean`,
`GoodHeights.lean`, `Horizontal.lean`), the prime side by Fourier inversion of the tilted test
function against the Dirichlet series of `−ζ'/ζ` (`VerticalLine.lean`), the `Γℝ` bracket
(`GammaRBracket.lean`), and absolute convergence of the zero side from the local count
(`ZeroSummability.lean`) — i.e. exactly the classical route the brief and the design memo
(§8) sketched, already done. The design memo's pole-in-box seam (§8 step 3) does not arise: the
upstream contour runs on `Λ(s)`, whose poles at `0, 1` are the residues `H(0) + H(1)`.

So the job reduced to five bookkeeping seams between the node's vocabulary and the upstream's.

## 3. Proof outline, lemma by lemma (all in `RvMBridge4`, `E6Bridge4.lean`)

| seam | lemma | content |
|---|---|---|
| test class | `contDiff_two_of_test` | `C^∞ → C^2` (`contDiff_infty`) |
| transform | `weilKernel_eq_Hfn`, `weilKernel_eq_paperFT_gammaOf` | `weilKernel g s = Hfn g s = paperFT g ((s−1/2)/I)`; integrands agree since `I · (x/I) = x` |
| transform | `weilKernel_line`, `weilKernel_zero`, `weilKernel_one` | `weilKernel g (1/2 + rI) = paperFT g r`, `weilKernel g 0 = paperFT g (I/2)`, `weilKernel g 1 = paperFT g (−I/2)` |
| archimedean | `archIntegrand_eq` | `archIntegrand g r = paperFT g r · gammaBracket r + paperFT g r · log π` (digamma argument `1/4 + (r/2) I = 1/4 + I r/2`) |
| archimedean | `inversion_zero` | `(1/2π) ∫ paperFT g r dr = g 0` (`Zeta23.EF.paper_inversion` at `u = 0`, integrability of `𝓕 g` from `integrable_fourier_of_contDiff_two`) |
| integrability | `paperFT_eq_Hfn_half`, `continuous_paperFT_real`, `norm_paperFT_le`, `integrable_paperFT` | `h(r)` continuous, `‖h(r)‖ ≤ C/(1+r²)` (`norm_Hfn_le` at `σ = 1/2`), integrable |
| integrability | `gammaBracket_eq`, `integrable_paperFT_mul_bracket` | bracket = `Γℝ'/Γℝ(1/2+rI) + Γℝ'/Γℝ(1/2−rI)` (`gammaR_bracket`); each product integrable by the upstream majorant lemma `integrable_mul_logDeriv_Gammaℝ_of_decay` (second copy via `Integrable.comp_neg`) |
| integrability | **`integrable_archIntegrand`** | the `Integrable` conjunct |
| normalisation | `archSide_eq` | `archSide g = paperFT g (I/2) + paperFT g (−I/2) + (1/2π) ∫ paperFT g r · gammaBracket r` (split the integral, absorb `−g 0 log π` by `inversion_zero`) |
| normalisation | `primeSide_eq` (rfl), **`archSide_sub_primeSide`** | `archSide g − primeSide g = literatureRHS g` |
| multiplicity | `zeroMult_eq_of_strip` | on `0 < Re ρ < 1`: divisor `.toNat` = `(analyticOrderAt ζ ρ).toNat` (`MeromorphicOn.AnalyticOnNhd.divisor_apply` + `Zeta23.RvM.analyticOnNhd_riemannZeta`) |
| multiplicity | `zeroMult_eq_zero_of_not_strip` | divisor vanishes off its domain (`supportWithinDomain`) |
| multiplicity | `zeroMult_eq_zero_of_not_nontrivial`, `zeroMult_eq_mult` | the node weight is supported on `IsNontrivialZero` (strip non-zeros: `analyticOrderAt_eq_zero`) and equals `zetaZeroConfig.mult` there |
| assembly | **`limit_explicit_formula`** | `hasSum_subtype_iff_of_support_subset` transports the node's `ℂ`-indexed family to the carrier subtype, where it is definitionally the upstream summand; `Summable.hasSum` + the upstream tsum identity + `archSide_sub_primeSide` |

Upstream inputs consumed as black boxes (all guarded): `Zeta23.WeilEF.EF_lit_zetaZeroConfig`,
`Zeta23.EF.paper_inversion`, `Zeta23.EF.integrable_fourier_of_contDiff_two`,
`Zeta23.EF.integrable_paperFT_ofReal`, `Zeta23.WeilEF.gammaR_bracket`,
`Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay`, `Zeta23.WeilEF.norm_Hfn_le`,
`Zeta23.WeilEF.continuous_Hfn_line`, `Zeta23.RvM.analyticOnNhd_riemannZeta`.

`E6Bridge2` (cumulative RvM) and `E6Bridge3` (corridor bound) are **not** imported: the
upstream's own good-height lemma and local zero count play their roles inside
`EF_lit_zetaZeroConfig`. They remain the registry's declared consumers-of-record for the node's
horizontal-edge and absolute-convergence steps in the from-scratch route; on this island that
route was not needed.

## 4. Verification (local, 2026-09-18, Lean v4.33.0-rc2, Zeta23 @ fbdc36bb)

`lake build`: `Build completed successfully (8825 jobs)`.
`lake env lean AxiomGuardRvMBridge.lean` (45 anchors, no `sorryAx`), verbatim:

```
'RvMBridge.rvm_unbounded_mean_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge.eventually_Ncount_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.rvm_cumulative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.int_mu_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge2.zetaZeroCount_eq_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.corridor_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.good_height_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_zeta_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.zeta_ne_zero_of_reflect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.logDeriv_Gammaℝ_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge3.norm_logDeriv_Gammaℝ_le_log_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.limit_explicit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.integrable_archIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.archSide_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.archSide_sub_primeSide' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.inversion_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.weilKernel_eq_Hfn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.zeroMult_eq_of_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RvMBridge4.zeroMult_eq_zero_of_not_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.N_eq_halfContour_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.halfContour_completedZeta_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.gamma_side' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.backlund_horizontal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.vertical_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.mu_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.riemannVonMangoldt_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.zeta_local_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.zetaSeam' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.zeta_logDeriv_partial_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.exists_far_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.logDeriv_completedZeta_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.StirlingVert.digamma_stirling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.EF_lit_zetaZeroConfig' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.EF.paper_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.gammaR_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.EF.integrable_fourier_of_contDiff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Drift check `python examples/rvm_bridge/generate.py --check`:

* on this branch (registry E8 files absent): passes, printing the two skip notices and
  `RH explicit-formula node statement matches its embedded copy`;
* in a scratch tree with `RH_limit_explicit_formula.lean` and the E8 `RHDefs.lean` copied
  from `origin/rh/e8-statement`: passes, `matches its embedded copy and the registry`,
  all six `WeilExplicit.*` def blocks equal;
* mutation test (theorem body `−` changed to `+`): fails on both the embedded and the
  registry half, as intended.

`_node_statement` in `generate.py` was generalised to accept explicit binders
(`theorem NAME (x : T) ... : BODY`); the three earlier nodes are binder-free and unaffected.

## 5. Remaining obligations

None. Every lemma in the module is sorry-free; there is no `E6Bridge4WIP.lean`.

## 6. Files

* `telperion/examples/rvm_bridge/lean/E6Bridge4.lean` (new; the bridge + verbatim defs + the node theorem; header embeds the registry statement between `BEGIN/END REGISTRY STATEMENT`)
* `telperion/examples/rvm_bridge/lean/lakefile.toml` (`E6Bridge4` lib, in `defaultTargets`)
* `telperion/examples/rvm_bridge/lean/AxiomGuardRvMBridge.lean` (8 bridge anchors + 5 upstream anchors added)
* `telperion/examples/rvm_bridge/generate.py` (fourth-bridge drift check, binder-aware node regex)
* `telperion/examples/rvm_bridge/lean/README.md` (fourth bridge section, refreshed guard output)
* this report

Follow-ups for the registry side (not done here, per scope): once `rh/e8-statement` merges,
`missions/rh/mission.toml` can grant `RH_limit_explicit_formula` from this island's artifact the
way the E6/E7 nodes are granted; the drift check then exercises the registry halves automatically.
