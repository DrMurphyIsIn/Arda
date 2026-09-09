# Reusing the RvM / explicit-formula foundation (parallel session, 2026-09-08→09)

The overnight RH sprint (PRs #352–#391, session `01NzN1Gt…`) landed a large,
kernel-clean analytic foundation in `telperion/examples/zeta_zero_localization/lean/`
(primarily **`DiffractionCore.lean`**) that our emitter roadmap should build ON, not
re-derive. All names below are kernel-verified `[propext, Classical.choice, Quot.sound]`
and axiom-guarded (`AxiomGuardRHInBox.lean`); `conjecture1_proved = False`. Reusing them
keeps our emitters honest: cite the kernel-verified lemma, keep analytic remainders as
hypotheses (the trust seam).

## Track 3 (Weil positivity) + HermitianMomentInertia emitters — the core reuse

`DiffractionCore.lean`:
- **`rect_explicit_formula`** (:624) — THE finite-height Guinand–Weil identity: weighted
  sums over ζ's divisor = von Mangoldt prime-power sums + three explicit boundary integrals.
  This IS the explicit formula the Weil-positivity emitter certifies positivity on top of.
- **`logDeriv_zeta_eq_neg_LSeries_vonMangoldt`** (:472) — `ζ'/ζ = −Σ Λ(n) n^{-s}` (Re s>1),
  the prime side of the Weil functional.
- **`rect_weighted_pole_generic`** (:50), `rect_weighted_residue_sum_generic`,
  `bd_weighted_logDeriv_zeta` — the weighted (test-function) argument principle; the
  finite-dim PSD/Gram pairing (our `HermitianMomentInertia`) sits on the weighted zero sum.
- **`right_edge_prime_expansion`**, **`left_edge_prime_reflection`** (:867) — the edge prime
  expansions = the archimedean + prime terms of the Weil functional (left edge closed with
  zero Arb inputs).

## Counting / RvM foundation — for the count emitters (TwoMomentCount, N(T) work)

`DiffractionCore.lean`:
- **`zero_count_band_edge_decomp`** (:1641) — the band-difference RvM `N(T1)−N(T0)` (what the
  Turing height-ladder consumes).
- `count_eq_argZeta_diff_sub_left` (:1148), `zeta_total_argChange_eq_count` (:961),
  `bd_logDeriv_zeta_eq_count` (:912).
- `theta_eq_argChangeVert_gammaR` (:1066) — θ(T); `riemannS_eq_argZeta` (:1099) — S(T).
- FE symmetry machinery: `fold_pointwise` (:1379), `argChangeVert_fold` (:1496),
  `pole_total_argChange` (:1595), `fold_pointwise_zeta₀` (:1730),
  `argChangeVert_completedZeta_split` (:1770), and the reflect/conj family
  (`logDeriv_completedZeta_reflect` :807, `logDeriv_zeta_conj` :1221, `gammaR_conj` :1226).

## Track 1 (Jensen–Pólya) — real-rootedness

- `telperion/examples/dvp_atoms/lean/JensenZeroCount.lean` — Jensen zero-count; pairs with our
  `interlacing` / real-rootedness shape and the `jensen_box_hyperbolic_*` emitters.

## Argument-principle emitter family — already backed here

`telperion/examples/dvp_geom_atoms/lean/`: `ArgumentPrinciple.lean`, `FullArgumentPrinciple.lean`,
`RectArgumentPrinciple.lean`, `RectWinding.lean`, `BoxResidueSum.lean`, `SlitLoopWindingZero.lean`,
`AnnulusCount.lean`, `TwoScaleSeparation.lean`, `FarPoleSum.lean`, `HerglotzLower.lean`,
`LogProductBound.lean` — the winding/residue atoms our registered `argument_principle` family emits.

## dVP effective inputs — for κ-optimization / zero-free feeds

`dvp_bc_atoms/lean/{BCDerivRe,EntirePartBound,MaxModulus}.lean`,
`dvp_atoms/lean/{BCSplit,SphereBound}.lean`, plus the unconditional effective Binet/ψ bricks
(PRs #360/#361) — feed the effective dVP region and the TwoMomentCount κ = 1/λ + λ/3 lever.

## Capstones our tooling can consume (AxiomGuardRHInBox.lean)

`AllZerosUpToHeight.all_nontrivial_zeros_up_to_height_on_line[_tiled]`,
`RHInBoxBands.{rh_box_two_bands,rh_box_of_bands,rh_full_box_of_left_half}`,
`ZetaZeroConfinement.{zeta_zero_re_mem_strip,no_low_zeros_of_strip_clear}`,
`AllZeros_h{100,200,1000}.*`, per-band `RHInBox_*`.

## CI note (2026-09-09)
`proof-lean` + `proof-comparator` are GREEN on `main` (`8155b7cf`). `telperion-test` has no
recent *completed* run (each cancelled by the merge wave — a concurrency artifact), so the
Python suite's main status is unconfirmed, not confirmed-red. The pre-existing `type|None`
Python-3.9 import bug in `zeta_zero_localization/generate.py:305` is fixed on branch
`fix/zeta-loc-py39-annotations` (`from __future__ import annotations`).
