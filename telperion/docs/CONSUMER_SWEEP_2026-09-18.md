# Consumer sweep after the critical path closed (2026-09-18)

*Read-only sweep of every `open`/`draft` node in the three campaign registries
(`telperion/missions/{rh,anduril,mirrormere}` on `origin/main` @ `1a0d208a3`, plus
`RH_limit_explicit_formula` on `origin/rh/e8-statement` @ `73eaf386d`) against the four proved
bridges on the `rvm_bridge` island and the zeta-23-lean inventory. Every verdict names the exact
upstream statement and every seam, or says there is none. Nothing here is RH progress.*
**`conjecture1_proved = False`.**

## 0. Sources swept

| id | theorem (namespace) | where | statement |
|---|---|---|---|
| S1 | `RvMBridge2.rvm_unconditional` | `examples/rvm_bridge/lean/E6Bridge2.lean` (on `main`, #557) | the `RH_rvm_unconditional` node statement verbatim: `∃ C > 0, ∀ T ≥ 2, |N(T) − (T/2π·log(T/2π) − T/2π + 7/8)| ≤ C log T`, `N = RvMCount.zetaZeroCount` |
| S2 | `RvMBridge3.corridor_bound` | `E6Bridge3.lean` (branches `rh/corridor-bound`, `rh/e8-proof`; NOT on `main`) | the `RH_corridor_bound` node statement verbatim (zero-free segment `[−1,2]` at some `T' ∈ [T,T+1]`, `‖ζ'/ζ‖ ≤ C log² T`) |
| S3 | `RvMBridge4.limit_explicit_formula` | `E6Bridge4.lean` (`rh/e8-proof`; NOT on `main`) | the `RH_limit_explicit_formula` node statement verbatim (E8 on `C_c^∞`, `HasSum` over all `ρ : ℂ` with `WeilExplicit.zeroMult`) |
| S4 | `RvMBridge.rvm_unbounded_mean_density` | `E6Bridge.lean` (on `main`; granted to `MM_rvm_unbounded_mean_density`, #553) | `RvMUnboundedMeanDensity zetaOrdinates` (Theorem A + dyadic RvM) |
| S5 | zeta-23-lean, pin `fbdc36bb` | `arda-e6/.../.lake/packages/Zeta23` (5037 declarations inventoried) | the parts that matter below: `WeilEF.EF_lit_zetaZeroConfig` (explicit formula, `C_c^2`), `WeilEF.zero_sum_inv_sq` / `zero_sum_inv_sq_gen` (`Σ m(ρ)/(1+|γ_ρ|²) < ∞`), `RvM.zeta_local_zero_count` (`N(t,t+1] ≤ A₀ log(|t|+3)`), `WeilEF.Effective.zeta_local_zero_count_explicit` (`540000000·log(|t|+3)`) and `zeta_logDeriv_partial_fraction_explicit` (`135000000·log(|t|+3)`), `thmA₀`/`two_thirds_on_critical_line`, `StirlingVert.digamma_stirling`, `GammaFacts.digamma_series`, `WeilEF.logDeriv_completedZeta_one_sub`, `WeilEF.rectangle_identity`/`good_heights`/`horizontal_vanish` (the contour bricks), `FromPNTPlus/*` (a medium PNT, present in the package, not built by any bridge) |

Keyword sweep of S5 for the open nodes' objects: no `Li`, `Bombieri`, `taylorCoeff`, `Speiser`,
`UniformlyDiscrete`, `Dense`, `Binet`, `sawBernoulli`, `Guinand`, `tempered`; `hardyZ` appears only in
the `XiPrime` tree (zero counts of `ξ'` and Hardy's `Z'`, not box certificates); `deriv riemannZeta`
appears only through `ZFunction.lean` (the derivative of `Z`), never as a zero-free box.

All four bridges carry `#print axioms = [propext, Classical.choice, Quot.sound]` per their reports
(`RVM_CUMULATIVE_BRIDGE_2026-09-17.md`, `CORRIDOR_BOUND_BRIDGE_2026-09-17.md`,
`E8_EXPLICIT_FORMULA_BRIDGE_2026-09-18.md`). Island: Lean `v4.33.0-rc2` + Zeta23; registry
islands: rh `v4.34.0-rc1`/Mathlib `de5ce8a9`, mirrormere/anduril `v4.32.0`. Every discharge from
these sources is therefore a **cross-island grant by normalized containment** (precedent: #553).

## 1. The table

Verdicts: **DISCHARGED-ON-ISLAND** (kernel-checked theorem exists, registry link/grant pending);
**DISCHARGEABLE NOW** (a short bridge from a named source, all seams named);
**UNBLOCKED** (a source removes a blocker, real work remains); **GRANT-PENDING** (artifact exists
sorry-free on `rh/million-turing`, waiting on the branch reconcile; the sources change nothing);
**UNCHANGED** (wall or unrelated). Ranked by value per unit of work within each verdict.

| # | node | status | verdict | source theorem | seams / what remains |
|---|---|---|---|---|---|
| 1 | `rh/RH_rvm_unconditional` | open | **DISCHARGED-ON-ISLAND** | S1 `RvMBridge2.rvm_unconditional` | statement verbatim; `RvMCount.zetaZeroCount` mirrored verbatim (`generate.py --check` green); cross-island grant. Action: `mission link` + `mission grant` on `main`. |
| 2 | `rh/RH_corridor_bound` | open | **DISCHARGED-ON-ISLAND** | S2 `RvMBridge3.corridor_bound` | statement verbatim, Mathlib-only vocabulary (no mirror); artifact not yet on `main` (merge `rh/corridor-bound`); constant is `∃`-form (the effective form stays queued, now unblocked by S5's explicit constants, see §3). |
| 3 | `rh/RH_limit_explicit_formula` | open (on `rh/e8-statement`) | **DISCHARGED-ON-ISLAND** | S3 `RvMBridge4.limit_explicit_formula` | six `WeilExplicit.*` defs mirrored verbatim; merge order `rh/e8-statement` → `rh/e8-proof` → link/grant; **RHDefs reconcile**: `main`'s `build_rhdefs.py` carries a `DBN` extract but no `WeilExplicit` literal, `rh/e8-statement`'s carries `WeilExplicit` (and now `BombieriLagarias` on `rh/b7-ef-statement`) but no `DBN`; whichever merges second must carry all `parts` entries or regeneration deletes a block (the `05eaaadbc` footgun). |
| 4 | `mirrormere/MM_zeta_ordinates_not_uniformly_discrete` | open, no artifact | **DISCHARGEABLE NOW** | S4 `RvMBridge.rvm_unbounded_mean_density` composed with the conditional brick `zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density` (`examples/quasicrystal/lean/BoundaryLemmas.lean`, v4.32, artifact of `MM_nt_brick_conditional`, sorry-free on `rh/million-turing`) | (a) **toolchain island**: the brick lives on v4.32, S4 on the rvm_bridge island; there is no common island, so the brick's pigeonhole argument must be transcribed (about 30 lines, see §2); (b) **definition mirror**: `RvMBridge` already mirrors `RvMUnboundedMeanDensity` and `zetaOrdinates` verbatim from `MMDefs.lean`; `Quasicrystal.IsUniformlyDiscrete` must be mirrored verbatim too; (c) the **AUTHORED** `zetaOrdinates` pin (non-verbatim in MMDefs, read-back flagged) is what the node quantifies over; (d) cross-island grant. |
| 5 | `mirrormere/MM_euler_factor_section_offline` | open, no artifact | DISCHARGEABLE NOW, but **from an in-campaign source, not from S1–S5** | `twoFreq_realRooted_iff` (`examples/quasicrystal/lean/TwoFreqRigidity.lean`, the artifact of its own dep `MM_twofreq_realrooted_iff`) | five-line bridge on the v4.32 island: instantiate with `c₁ = 1`, `c₂ = −1/√2`, `lam₁ = 0`, `lam₂ = −log 2` (`1 ≠ 0`, `−1/√2 ≠ 0`, `0 ≠ −log 2` by `Real.log_pos`), the iff reduces the statement to `¬ (‖(1:ℂ)‖ = ‖((−1/√2 : ℝ) : ℂ)‖)`, i.e. `1 ≠ 1/√2` (`norm_num`, `Real.sqrt_two`). Listed because the sweep asked for concreteness; the sources play no role. |
| 6 | `rh/RH_li_rung0_kernel` | open | **UNBLOCKED** (new route from the B7 design, real work) | none of S1–S5 directly; the B7 companion identity at `n = 1` (memo `B7_BL_EXPLICIT_FORMULA_DESIGN_2026-09-18.md` §4.2) | rung 0 is `0 ≤ Re (taylorCoeff riemannXi 0)` and `taylorCoeff riemannXi 0 = ξ'/ξ(1) = 1 + γ/2 − (log 4π)/2 = 1 + riemannZeta 1` in Mathlib's convention (`riemannZeta_one : riemannZeta 1 = (γ − log (4π))/2`). Two lemmas close it hypothesis-free: (i) `LiCriterion.taylorCoeff LiCriterion.riemannXi 0 = 1 + riemannZeta 1` (a local Taylor computation at `s = 1`: `logDeriv (phi ξ) 0 = ξ'/ξ(1)`, `ξ = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`, `ψ(1/2) = −γ − 2 log 2` (Mathlib digamma), `ζ'/ζ + 1/(s−1) → γ` from `tendsto_riemannZeta_sub_one_div`); (ii) the numeric `2 + γ > log (4π)`: needs `γ > 0.5311` (Mathlib's `1/2 < γ` is NOT enough; `eulerMascheroniSeq_lt_eulerMascheroniConstant 20` gives `H₂₀ − log 21 = 0.5532 < γ`) and `log (4π) < 2.5772` (`Real.log_two_lt_d9`, `pi_lt_3141593`, and `log x ≤ (x−1)/√x` at `x = π/2` give `log 4π < 2.535`; margin 0.04). Class stays hard-known-shape only in the sense that (i) is a derivative object; it is no longer blocked on a difference-quotient bracket. |
| 7 | `mirrormere/MM_nt_brick_conditional` | open, artifact | GRANT-PENDING | (its own artifact `BoundaryLemmas.lean`, sorry-free on `rh/million-turing`) | its dep `MM_rvm_unbounded_mean_density` is now proved (S4), so its closure flag flips at grant time; the sources add nothing to the node itself. |
| 8 | `mirrormere/MM_bragg_bridge` | open, artifact | GRANT-PENDING | (`RvMBraggBridge.lean`, sorry-free on `rh/million-turing`) | unchanged; its header's "T→∞ needs the corridor bound" is now answered by S2+S3 (E8 is the limit), but the node is the finite identity. |
| 9 | `mirrormere/MM_rect_trace_reading` | open, artifact | GRANT-PENDING | (`RvMTraceReading.lean`, 59 lines, sorry-free on `rh/million-turing`) | unchanged. |
| 10 | `mirrormere/MM_bragg_defect_witness`, `MM_offline_pairs_le_defect`, `MM_primelog_spectrum_dense`, `MM_selfinversive_iff_hardyz_real`, `MM_spectral_cooked_control`, `MM_twofreq_realrooted_iff` | open, artifacts | GRANT-PENDING | (artifacts sorry-free on `rh/million-turing`) | unchanged. S5's `LinAlg/{Inertia,Sylvester,PosIndex}` overlaps the defect instrument's vocabulary (`MM_offline_pairs_le_defect`) but the node already has its artifact. |
| 11 | `anduril/AND_checkline_correct`, `AND_em_tail3_number`, `AND_em_zeta_strip`, `AND_first_zero_kernel`, `AND_g2_reflected_band`, `AND_stirling_binet_k1` | open, artifacts | GRANT-PENDING | (artifacts on `rh/million-turing`; the `sorry` grep hits in `CheckBand.lean:40` and `EMZetaComplex.lean:14` are comments) | unchanged. S5's `StirlingVert.digamma_stirling` / `RvM.logDeriv_Gammaℝ` are *inequality* forms of Γℝ'/Γℝ Stirling; `AND_stirling_binet_k1` is an *identity* with an explicit Binet remainder, not a corollary. |
| 12 | `mirrormere/MM_offline_disjoint_discs` | open, no artifact | UNCHANGED (Mathlib-only, not a bridge question) | none | dischargeable from Mathlib alone (finite set: a third of the least pairwise distance and of the least distance to `Re = 0, 1`); the sources are irrelevant. |
| 13 | `mirrormere/MM_recurrence_deficit_eq_excess` | open, no artifact | UNCHANGED (Mathlib-only) | none | `(e^δ − 1)(1 − e^{−δ}) = e^δ + e^{−δ} − 2` by `ring`/`field_simp`, equals `excess` at `δ = 1/10` by unfolding, positivity from `1 < e^δ`. |
| 14 | `mirrormere/MM_speiser_box_probe` | open | UNCHANGED | none | needs a `ζ'` winding-box certificate; S5's `XiPrime` tree counts zeros of `ξ'`/`Z'`, it does not certify a box. |
| 15 | `mirrormere/MM_torus_section_dictionary` (draft), `MM_torus_section_n2_rigidity` | draft / open | UNCHANGED | none | torus-section vocabulary; unrelated. |
| 16 | `rh/RH_dbn_H0_eq_xi`, `RH_dbn_debruijn_real_zeros`, `RH_dbn_rh_iff_H0_real_zeros` | draft | UNCHANGED | none | Route C (heat flow `H_t`); S5 has no `H_t`/theta-flow content. `RH_dbn_rh_iff_H0_real_zeros` needs only `H₀ = ξ/8` and the zero correspondence, both DBN-island work. |
| 17 | `anduril/AND_ladder_h280000`, `AND_ladder_1e6`, `AND_ladder_1e9`, `AND_ladder_1e13` | open / draft | UNCHANGED | none | finite height verification; S5's `two_thirds_on_critical_line` is a proportion theorem, not a height certificate. |
| 18 | `rh/RH_conjecture`, `mirrormere/MM_zeta_comb_membership` | draft goals | UNCHANGED (wall) | none | — |

Adversarial notes on rows 1–3: none of the three registry nodes says anything the island theorem
does not; the only content in a grant is the containment check plus the toolchain caveat. Row 3's
mirror of `zeroMult` uses `MeromorphicOn.divisor` on the open strip, and the bridge proves it equals
Zeta23's `analyticOrderAt` weight only on the strip (`zeroMult_eq_of_strip`); off the strip both are
0 by construction. No node in any campaign is dischargeable from `EF_lit_zetaZeroConfig` beyond E8
itself: every other explicit-formula-shaped node in the registry is finite (`MM_bragg_bridge`,
`MM_rect_trace_reading`) or on a different test class (the new `RH_bl_explicit_formula`, §3).

## 2. The one new bridge worth writing now (row 4), exact statement

On the `rvm_bridge` island, after the verbatim mirror of `IsUniformlyDiscrete`
(`MMDefs.lean`, Quasicrystal block):

```lean
namespace RvMBridge

def IsUniformlyDiscrete (S : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → δ ≤ |x - y|

/-- The MIRRORMERE node `MM_zeta_ordinates_not_uniformly_discrete`, verbatim. -/
theorem zeta_ordinates_not_uniformly_discrete : ¬ IsUniformlyDiscrete zetaOrdinates

end RvMBridge
```

Proof shape (the conditional brick, transcribed): assume `δ`-separation; apply
`rvm_unbounded_mean_density` at `r := 2/δ` to get `F ⊆ zetaOrdinates` inside `[a, a+L]` with
`(2/δ)·L + 1 < |F|`; a `δ`-separated finite subset of an interval of length `L` has at most
`L/δ + 1` elements (sort `F`; consecutive differences are `≥ δ`, so `(|F|−1)·δ ≤ L`); hence
`(2/δ)L + 1 < L/δ + 1`, impossible for `L ≥ 0`. Everything used is in Mathlib; the only zeta input
is S4. The registry grant is cross-island (v4.32 campaign, v4.33 artifact), same gate as #553.

## 3. Queue items unblocked (not nodes)

* **Effective corridor constant** (standing queue): S5's `WeilEF/Effective.lean` has explicit
  constants (`zeta_local_zero_count_explicit : N(t,t+1] ≤ 540000000·log(|t|+3)`,
  `zeta_logDeriv_partial_fraction_explicit` with `135000000·log(|t|+3)`), so the `∃ C` in
  `RvMBridge3.corridor_bound` can be made explicit by re-running its `good_height_real` with these
  inputs (the compactness step `corridor_small` still needs a numeric bound on `[2,8]`).
* **B7 test-class extension** (roadmap B7-ii): authored as `RH_bl_explicit_formula`, see
  `B7_BL_EXPLICIT_FORMULA_DESIGN_2026-09-18.md`. The proof route reuses S5's contour bricks and
  S1/S2; the E8 *statement* does not apply to Li's kernel (the family is not summable).
* **B7-i multiset seam**: `RH_bl_finite_multiset` quantifies over a `Finset` (no multiplicity); the
  window sums of the new node carry `zeroMult`. A multiple zero (none is known; none is excluded)
  would need the multiset form of B7-i. Recorded in the memo, not fixed here.

`conjecture1_proved = False`.
