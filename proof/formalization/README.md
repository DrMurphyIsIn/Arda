# R3 (Phi <= 1) -- Lean 4 formalization pass

A machine-checkable formalization of the **exact-arithmetic core** of R3 (the branch bound `Phi <= 1`) from
the Brualdi-Goldwasser Laplacian-ratio maximizer proof, plus the real-analytic bridges that this core
supports, and an honest map of what remains.

> **Status: BUILDS CLEAN on Lean 4 v4.32.0 + Mathlib v4.32.0.** `lake build` completes with no errors and
> no `sorry`. `#print axioms` on `rhoB_pow11`, `rhoB_sq_ge`, `omega_neg`, `C1_lt_one`, `e2_two_rhoB_gt`
> reports only `[propext, Classical.choice, Quot.sound]` -- the three standard Mathlib axioms, **no
> `sorryAx`** -- so the arithmetic backbone of R3 is fully machine-verified with no gaps.

## What is here

- **`R3Cert/ExactCruxes.lean`** -- the load-bearing content, **fully proved (no `sorry`)**:
  - *Layer 1* (exact rational/integer cruxes, closed by `norm_num`/`decide`): `rho_B^11 = 621/64 = 3^3*23/2^6`;
    E3 crux `(3/2)^11 <= (621/64)^2`; R5 crux `(26/23)^11 < 621/64`; E2 Pell decay `11753^2 > 2*5741^2`;
    near-star tie `64*243*23 = 621*576`; the binding corner `(122948/100000)^11 > 621/64` and
    `132r^2+4r^3 <= 207`; and more.
  - *Layer 2* (real-analytic bridges, reduced to Layer 1 via `Real.rpow`/`Real.sqrt`/`Real.log` monotonicity):
    `rho_B^2 >= 3/2` (`rhoB_sq_ge`), `omega < 0` (`omega_neg`), `C_1 = (26/23)/rho_B < 1` (`C1_lt_one`),
    and the E2 chain decay `1 + sqrt 2 < 2*rho_B` (`e2_two_rhoB_gt`).
- **`R3Cert/DEC.lean`** -- the DEC decomposition identity as a **fully proved** real-log identity
  (`dec_identity`, `dec_near_star`; no `sorry`). Discharges the `DEC_identity` hypothesis of Structure.lean.
- **`R3Cert/Matching.lean`** -- the matching/permanent bridge, with two machine-checked layers (no `sorry`):
  - *(H2) algebraic core:* `cavity_step`, `log_telescope` -- the passage from the two subtree partition
    functions to the cavity ratio `r_v = 1/(1+S)`, and the log-telescoping.
  - *(H1) combinatorial framework + permanent-term arithmetic:* the Laplacian `lapl` of a `SimpleGraph` over
    ℝ (`lapl_diag`, `lapl_adj`), `EdgeSupported`, `edgeSupported_of_term_ne_zero` (a nonzero permanent term
    forces the support condition -- the first reduction of H1), `nonfixed_image`, and the per-factor
    evaluation `term_factor_fixed` (`= deg v`) / `term_factor_nonfixed` (`= -1`).
- **`R3Cert/Involution.lean`** -- the **crux of H1, now a machine-checked THEOREM** (`no sorry`):
  `acyclic_edgeSupported_involutive` -- on an acyclic graph, an edge-supported permutation is an involution.
  Proof: a non-involution has a σ-orbit of length `≥ 3`; `orbitWalk` iterates σ to build a closed
  `SimpleGraph.Walk` whose tail is a path (orbit vertices distinct via
  `Function.iterate_injOn_Iio_minimalPeriod`) of length `≥ 3`, hence a cycle
  (`isCycle_iff_isPath_tail_and_le_length`), contradicting `IsAcyclic`. This discharges the crux
  `AcyclicForcesInvolution` in Matching.lean (`acyclicForcesInvolution`), so it is no longer a target `Prop`.
  Both full identities are also proved in prose in `outreach/matching_bridge.tex` and verified numerically on
  trees up to 10 vertices; the remaining unformalized step of H1 is only the sum-reindexing bookkeeping
  (per L = Σ over the involutions/matchings), the combinatorial heart being done.
- **`R3Cert/Structure.lean`** -- the induction-step *skeleton*: how the proved cruxes assemble, with the
  remaining piece isolated as an **explicit hypothesis (not an axiom)**:
  - **(S)** the finite interval **sweep** (the `(s,j)` core `s<=64, j<=500` + two monotone tails).

Every arithmetic goal was independently verified in exact Python arithmetic before being stated -- see
`../lemma_proofs.py`, `../e2_closure.py`, `../pell_chain_structure.py`, `../rem_tie.py`,
`../gap_interval_certification.py`, `../adversary_sweep.py`.

## Honest scope

- **Fully machine-checkable now:** the entire arithmetic backbone of R3 -- every "clear the 11th root => exact
  inequality" crux, and the `omega<0 / C_1<1 / rho_B^2>=3/2 / 2 rho_B > 1+sqrt2` bridges that the structural
  lemmas rest on. This is the part that was historically stated as "exact rational fact" and is now proved in
  a proof assistant.
- **Not yet formalized (remaining work, not open mathematics):**
  - (G) requires a Lean development of trees, the Laplacian permanent, and the matching/cavity recursion to
    state and prove the DEC identity and the E0/E1 band classifications as theorems rather than `Prop`s. The
    Python side proves these (induction for E0/E1; a 1e-15 algebraic identity for DEC).
  - (S) requires either an interval-arithmetic decision procedure in Lean or a hand-closed form of the
    concave `(s,j)` maximization. The Python side certifies it rigorously (`gap_interval_certification`,
    `ALL_INTERVAL_CERTIFIED`; worst node `-0.007808 <= omega = -0.007707`).

`conjecture1_proved` remains **False**: this pass formalizes R3's exact core, not the whole conjecture.

## Build

Because Mathlib and its toolchain move together, the most robust route is to scaffold with `lake` and drop in
the two `.lean` files:

```bash
# 1. install elan (Lean version manager), which provides lake
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

# 2. fetch deps + prebuilt Mathlib, then build (confirmed working)
cd proof/formalization
lake update            # resolves Mathlib v4.32.0 + deps, syncs the toolchain
lake exe cache get     # downloads prebuilt Mathlib oleans (~minutes; avoids a multi-hour build)
lake build             # checks R3Cert.lean -> ExactCruxes.lean + Structure.lean
```

**macOS note.** On macOS 26 (Darwin 25)+, older Lean toolchains (e.g. v4.15.0) produce native binaries that
`dyld` rejects with `__DATA_CONST segment missing SG_READ_ONLY flag`, which breaks `lake exe cache get`. This
is fixed by using a recent toolchain -- the pinned **v4.32.0** builds and runs the `cache` binary correctly.

A clean `lake build` with no errors and no `sorry` warnings on `ExactCruxes.lean` means the exact-arithmetic
core of R3 is machine-verified.

## Version note (Layer 2)

**Layer 1** (the `norm_num`/`decide` cruxes) is robust across Mathlib versions -- these tactics settle the
exact rational/integer goals regardless of library churn.

**Layer 2** (the analytic bridges) uses standard monotonicity lemmas whose *names* shift between Mathlib
releases. The build is pinned to **v4.32.0**, where the reverse-power lemmas carry the `₀` suffix:
`le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) : aⁿ ≤ bⁿ → a ≤ b` and
`lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) : aⁿ < bⁿ → a < b` (both in
`Mathlib/Algebra/Order/GroupWithZero/Basic.lean`). The other Layer-2 lemmas
(`Real.rpow_pos_of_pos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.log_pow`, `Real.log_lt_log`,
`Real.sqrt_sq`, `Real.sqrt_lt_sqrt`, `div_lt_one`) are stable. If you retarget a different Mathlib version and
hit an unknown identifier, it is a one-line rename (`exact?` resolves it); every underlying inequality is
verified in exact Python arithmetic, so the content is settled regardless.
