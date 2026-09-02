# BG unified program — command picture (2026-08-31)

Single owner now drives both halves of the Brualdi–Goldwasser Laplacian-ratio effort. This doc merges the two
session handoffs into one architecture, records their (strong) mutual consistency, and prioritizes the open
work. `conjecture1_proved = False` throughout.

- **Analytic/combinatorial half** — `telperion/` (docs `BG_STAR_OF_BROOMS_{RESULT,HANDOFF}.md`,
  `BG_PIECE3_OBSTRUCTION_MAP.md`; skills `spider_broom`, `transfer_caterpillar`, …; gates `bg_broom_optimum`,
  `bg_arm_balancing`).
- **Lean structural half** — `proof/formalization/R3Cert/R47R7*.lean` (handoff `HANDOFF_TREE_TO_HUB_20260831.md`;
  the tree→hub reduction, PRs #166–#176).

## The object (identical in both halves)

`π(T) = Aobj(T) = per(L)/∏deg = Σ_{matchings M} ∏_{uv∈M} 1/(d_u d_v)` (`telperion.matching_free_energy.rho` =
Lean `Aobj = Ztot ∘ dtRealize`). Cherry weight `3/2` matches on both sides.

## Target and current best

`F* = lim_n (1/n) log max_{|T|=n} π(T) = log(621/64)/11 = 0.2065864`, achieved (asymptotically) by the
**single-hub star-of-B(5)-brooms** `S(k,5)`.

- **Lower bound `F* ≥ 0.2065864`** — PROVEN by exhibiting `S(k,5)` (exact, `telperion`).
- **Upper bound `F* ≤ 0.2065864`** — OPEN (this is Brualdi–Goldwasser).

## The two halves are the same object, and they CONVERGE on {4,5}

The Lean target class `IsBCHubForm := Balanced ∧ Capped ∧ backboneU` (`R47R7TreeReduce`) means a backbone whose
- `Capped`: every hub has `≥ 5` arms;
- `Balanced`: every arm carries `4 or 5` cherries, and each hub's direct cherry-load `≤ 5`.

Independently, the analytic half found the growth-rate optimum at **`c = 5` cherries/arm** (`bg_broom_optimum`,
`total(5) = 621/64`), with `c = 4` the immediate neighbour. **The Lean `Balanced` arm-load `{4,5}` is exactly
the analytic `c = 5` optimum (+ its neighbour).** Two independent derivations, same `{4,5}`, same `621/64`
constant (also the earlier Φ¹¹ near-star tie constant, `64·243·23 = 621·576`). This is strong mutual
corroboration, not a conflict.

**Key structural fact (verified exact, this session):** the maximiser *within* `IsBCHubForm` is the
**single-hub** (`m = 1`) form with all arms `= armU 5`. A `backboneU` hub carries `arms.map armU`, and `armU j`
is itself a broom of `j` cherries, so `backboneU [([5,…,5], 0)]` **is** `S(k,5)`. Multi-hub balanced-capped
backbones have strictly lower rate (uniform-path rate `0.2004 → 0.2059` as per-hub load grows, always `< F*`;
single-hub `→ 0.2065864`). So `S(k,5)` sits at the top of the exact Lean target class.

## Unified proof architecture (upper bound)

```
                    ┌─ tree→hub reduction (Lean, R47R7*):  ∀t ∃ balanced+capped s, Aobj t ≤ Aobj(backboneU s)
  F* ≤ 0.2065864 ⇐ ─┤        [conditional on Obligation A (Kelmans cavity) + B (root-invariance) + assembly]
                    └─ capping-max (analytic):  max over Balanced+Capped backbones of the rate = F*, at single-hub-c5
```
Chaining gives `∀t, rate(t) ≤ F*`. **Independent route** (analytic, my frontier): the pointwise Bethe discharge
`log π = Σ_v A_v − Σ_e B_e ≤ F*·n + C` (tight bulk discharge verified on the `S(k,5)` fixed point).

## Open obligations (priority order)

1. **Obligation A — Kelmans cavity inequality (shared crux, the BG wall).**
   `Aobj(node(A::B::rest)) ≤ Aobj(node(pushInto A B::rest))`: relocating branch `B` into `A`'s deep hub raises
   `Aobj`. Root child-count drops `|rest|+2 → |rest|+1` (degree-changing), so `node_Ztot_child_mono_deg` does
   not apply. Phase-0 strict 30/30 (no equality edge case). **Attack:** express both sides in the exact cavity
   `(U,M)` multilinear form (`Aobj` is affine in each child's `(Zopen, Ztot)` pair) — the analytic half's
   `vdb_exchange`/Bethe machinery is built for exactly this per-vertex `Aobj`-monotonicity; generalise the
   cap-3/16 cell certificate to the relocation site.
2. **Capping-max (analytic, my lane, tractable).** Prove: over Balanced+Capped backbones the growth rate is
   maximised by single-hub-all-c5 at `F*`. Decomposes into (i) `c∈{4,5}` arm rate `≤ c=5` (have `bg_broom_optimum`);
   (ii) single-hub `≥` multi-hub (concentration; verified exact, needs the transfer-rate lemma); (iii) direct
   hub cherries `≤5` don't raise the rate. Kernel-gateable like `bg_broom_optimum`. **Do this next** — it
   completes the second box of Route I independent of Obligation A.
3. **Obligation B — `Aobj` root-invariance seam.** Construct the address-graph `SimpleGraph.Iso` for re-rooting
   (algebraic engine `R47RootInvariance` done). Self-contained; unblocks 2138/2438 reroot witnesses.
4. **Structural assembly** — existence finder for `StraightProgress_sized` + context-lifting (mechanical-ish,
   Lean; blocked for this owner by the no-local-Lean constraint → CI-only, or hand to a Lean-capable session).
5. **Pointwise discharge upper bound** (independent Route II) — the universal `φ_v ≤ F*` discharge; hard.

## Ownership / constraints

- This owner runs the **analytic/computational + Telperion-gate** lane strongly (obligations 2, and 1/5 via
  exact cavity tooling). **Cannot build Lean locally** (SoC-watchdog constraint) → Lean edits are CI-only;
  heavy Lean assembly (4) is best left to / co-driven with a Lean-capable session.
- Everything exact (`Fraction`) + kernel-gated where emitted; `conjecture1_proved = False` until the full chain
  closes unconditionally.

## Next action

Obligation 2 (capping-max) — formalize + kernel-gate the "single-hub-c5 is the extremal Balanced+Capped
backbone" lemma, then probe Obligation A with the exact `(U,M)` cavity form. See
`telperion/docs/BG_STAR_OF_BROOMS_RESULT.md` §5b for the Bethe framework.
