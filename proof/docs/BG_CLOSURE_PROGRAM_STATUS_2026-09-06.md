# BG closure program — status & handoff (2026-09-06)

Consolidation of the literature-grounded closure program (design + execution) on branch
`bg/bg-closure`. Design/plan: `~/.claude/plans/quiet-singing-kahn.md`. `conjecture1_proved = False`.

## The reduction (unchanged, proven)
`conjecture1_of_layers_fixedN` (R47TopCapstoneFixedN.lean) reduces BG to a per-size `tie : ℕ → UTree`
+ `Hnorm` (tree→hub) + `Hdom` (hub→tie). `Aobj = per(L)/∏deg` is proven (`pi_utree`). The plan's
key structural wins: the naive **near-star tie is refuted** (`nearStar_not_maximal_at_five`, K<23),
and the oscillating `hrate` rate bound is **bypassable** by comparing to the exact broadened tie value.

## Confidence battery M2 (decisive, committed, self-verifying)
- **M2(1)** `exhaustive_maximizer_check.py` — every non-iso tree to n=20: the small-n maximizer is a
  **parity cherry-spider** (odd n → single hub deg (n−1)/2 with cherry arms; even n → two hubs), NOT
  the broadened load-5 family. ⇒ full-n closure with `tieBroadened` is impossible; **aligned-n
  scoping is necessary**.
- **M2(3)** `asymptotic_rate_gap.py` — the single-hub **load-5 (broadened) family is the top-rate
  family** (`rhoB`), beating cherry/Pant spiders (`√(3/2)`, exponential gap) AND multi-hub caterpillars.
  Together with M2(1) this brackets small-n (cherry-spider) and large-n (broadened) — de-risking the
  tie as the large-n/aligned maximizer.

## M1 — COMPLETE (Piece 1, tie definition), kernel-verified, axiom-clean
`R47TieBroadened.lean`, all in AxiomGuard + the proof-lean CI leaf list:
- `tieState K m` — single hub `(K−m)` load-5 + `m` load-4 arms + `m` cherries; `tie_trade_factor`
  (`114/115`, `473/1311`).
- `tie_Aobj_eq_V` — exact value `V(K,m)`; `tie_Aobj_factored`.
- `tie_trade_le` — objective comparison ↔ `tieQ` condition; `tie_trade_le_poly` — ↔ exact polynomial
  `203376(K+m) ≤ (1482K+1784m)(K+m+115)` (m=0 threshold = K=23); `tradeStop_persists` — upward-closed.
- `tie_step_up/down`, `tie_up_chain/down_chain`, **`tie_maximal_over_trades`** — the m-argmax: given
  `mstar` = least trade-stop, `tieState K mstar` dominates every trade count `m ≤ K`.

## M4 — two-hub domination: COMPLETE (kernel-verified), `R47R7TwoHubBridge.lean`
The abstract certs `two_hub_gap_pos_c0..c5` are now WIRED to `Aobj`. De-risked first in
`two_hub_bridge_certcheck.py`: the `pi↔Aobj` normalization is **C = 1** (Aobj = per(L)/∏deg on the
realized tree, `pi_utree`), and each Lean cert IS the sympy numerator (per-cell factor **1**) over a
positive denominator.
- `twoHub_Aobj_eq` — exact `Aobj` of the stuck two-hub `S2(pA,pB,cA)`, by specializing the proven head
  identity `Aobj_head_before_raw` (R47HeadId) — NOT a fresh cavity derivation.
- `twoHub_reduced_c0..c5` — the `V^K`-divided reduced inequalities, each the exact identity
  `RHS−LHS = ratio·cert/den` (ratios `3^12,3^9,3^6,3^3,1,1`) via `field_simp;ring` + `div_nonneg` +
  `nlinarith` on the matching cert.
- **`twoHub_le_tie`** — `Aobj(S2) ≤ Aobj(hubState (K+1−m) m 0)`, `m=5−cA`, per-`cA` power-factoring of
  the common `(621/64)^K` then `convert` to the reduced lemma.  Kernel-clean, in AxiomGuard + CI.
  Closes the **length-2** slice of `SharpRateNF`/`Hdom`.

## M3 — single-hub 2-D envelope: **COMPLETE for all aligned K** (kernel-verified)
`R47SingleHub2D.lean`.  A Balanced single hub at aligned size `11K` (c≤5) is exactly the bulk column
`colState K c t = hubState (K−c−9t) (c+11t) c` (b≡c mod 11 forces `b=c+11t, t≥0`), t=0 edge = `tieState K c`.
- **t-axis (kernel-verified):** `hub_bulk_stop_iff` (reduces `hub_bulk_le`'s hubQ condition to the
  22-digit `bulkStopABC` polynomial — the `tie_trade_le_poly` analog), `bulkStopABC_persists`,
  `col_step_up/down`, `col_up/down_chain`, **`col_maximal_over_bulk`** (each column's t-argmax dominates —
  the `tie_maximal_over_trades` analog).  De-risked in `broadened_tie_2d_envelope.py`.
- **c-envelope, clean regime `K ≥ 23` (kernel-verified):** `colStop_zero_large` (bulk doesn't help at the
  edge for K≥22, quadratic-in-K `nlinarith`), `col_le_edge_large` (column collapses to its tie edge),
  `tradeStop_zero_large`, **`col_le_nearStar_large`** — every Balanced single hub at size 11K, K≥23, is
  dominated by the near-star `tieState K 0`.  So near-star IS the aligned-size single-hub maximizer for
  K≥23 (dual to `nearStar_not_maximal_at_five`, K<23).  Kernel-clean, in AxiomGuard + CI.
- **decomposition + argmax + K≥22 envelope DONE:** `hubState_eq_colState` (Balanced hub at 11K =
  `colState K c (b/11)`; `b≡c mod 11` & `b≥c` by omega's div/mod), `tradeStop_exists`/`leastTradeStop`/
  **`mOf K`** = `min K (leastTradeStop K)` (the tie argmax for EVERY K — KEY FINDING: for `K≤4` no
  in-range `tradeStop`, argmax is the boundary `m=K`; `Nat.find` under `open Classical`),
  `tie_maximal_general` (tie edge maximized at `mOf K`, all K), **`singleHub_le_tie_ge22`** (every
  Balanced single hub at size 11K, `K≥22`, `≤ tieState K (mOf K)` — the length-1 sharpRate input,
  correct broadened-tie target).
- **`1 ≤ K < 22` finite patch DONE (`singleHub_le_tie_lt22`):** after decomposition the bulk position
  `t = b/11 ≤ 2`; `t=0` is the tie edge (`tie_maximal_general`), each interior `t∈{1,2}` a concrete
  rational comparison `colState K c t ≤ tieState K (mOf K)` via `hub_Aobj_eq`+`norm_num`, routed through
  `tie_maximal_general` to `m = mOf K` (no `mOf`-value proof needed).  Per-K blocks (correct `m`, no
  `first`-backtracking), `maxHeartbeats 2000000`.
- **`singleHub_le_tie` (ALL K≥1):** splits `K≤21` (patch) / `K≥22` (structural).  **The M3 2-D envelope
  is CLOSED** — the complete length-1 input to the assembly.

## Non-aligned-n single-hub envelope — ALL 11 residues, large sizes (`R47SingleHubResidue.lean`)
A general single hub at size `n` has `δ = b-c ≡ r mod 11` (`r = 5(n-1) mod 11`).  Extended the whole M3
machinery, parametrized by `r`, and CLOSED all 11 residue classes at large sizes (kernel-verified):
- **Residue-general atoms:** `hub_trade_le` (the general cherry trade, factor `114/115`, no `b=c`) +
  `hubTradeStop`/`hub_trade_stop_iff` (den `150765·d·(d+1)`); the bulk atoms (`hub_bulk_le`,`bulkStopABC*`)
  were already `(a,b,c)`-general.  `size(colStateR M r c t) = 1 + 11M + 9r` (indep of `c,t`).
- **Two argmax axes:** the shifted edge `rtieState M r c = hubState (M-c)(c+r)c` with trade argmax
  `rtie_maximal_general`/`rMOf`; the shifted bulk column `colStateR` with `col_maximal_over_bulkR` and
  clean-regime collapse `colStopR_zero_large`/`col_le_edgeR` (M≥22, all `r≤10`).
- **r = 0..7 (`singleHubR_le_tie_07`, M≥22):** the maximizer is the `δ=r` edge; `δ≥r` configs via
  `col_le_edgeR`+`rtie_maximal_general`, the finite sub-edge (`t=-1`) configs at `r=6,7` via `rNeg_r6`/
  `rNeg_r7a`/`rNeg_r7b` (symbolic-`M` `hub_Aobj_eq`+`nlinarith`).
- **r = 10 (`singleHubR_le_tie_10`, Mn≥31):** the maximizer is the SINGLE fixed `δ=-1` edge `negEdge`;
  built its trade argmax (`neg_maximal_general`/`negMOf`), the bulk-link `neg_bulk_link` (`δ=10` edge ≤
  `δ=-1` edge), and the `c=0` boundary `rNeg_c0`.
- **r = 8, 9 (`singleHubR_le_tie_89`, Mn≥40):** the maximizer is the MAX of TWO edges (`δ∈{-3,8}` /
  `{-2,9}`).  Generalized `negEdge` → `offEdge M off c = hubState (M-c)(c-off)c` (`off=11-r`) with argmax
  `off_maximal_general`/`offMOf`; every config ≤ `max(low-edge argmax, high-edge argmax)`.  **KEY
  CORRECTION:** r=8,9 are MECHANICALLY closable (the "oscillation" is just a two-edge max), NOT entangled
  with Pant-open — Pant-openness is the MULTI-hub case, not single-hub.
- **Tie validity:** `mOf_le_five`/`rMOf_le_five`/`negMOf_le_five`/`offMOf_le_five` — every tie's cherry
  count `≤ 5`, so all tie states are valid `Balanced` states (`tradeStop K 5` etc. positive-definite).

**Net:** the single-hub (length-1 `Hdom`) maximizer is fully characterized across all 11 residues at large
sizes, a clean standalone result.

**SMALL-M PATCHES DONE — single-hub envelope now COMPLETE at EVERY size (all 11 residues).**
- **r = 1..5 (`singleHubR_le_tie_small_r1..r5`, 1≤M≤21):** single-edge, decompose → `colStateR`,
  per-M `interval_cases` with correct `m=rMOf(M,r)`, `t=0` via `colStateR_zero`+`rtie_maximal`, interior
  `t∈{1,2}` via `hub_Aobj_eq`+`norm_num`.
- **r = 6..10 (`singleHubR_le_tie_small_r6..r10`, 1≤M≤30 ⟹ Mn=10..39):** these are TWO-edge (maximizer
  flips to the `δ=r-11` sub-edge at small size). Unified `max`-of-two template — sub-edge configs
  = `offEdge (M+9) (11-r) c` → `off_maximal_general`; high-edge configs reuse the per-M patch under
  `le_max_of_le_right`. `t≤3`; r=10 uses `off=1` (=negEdge). KEY: the `M`-param (size `11M+9r`, offEdge
  budget `M+9`, rtie budget `M`) avoids the `Mn`-param's tiny-size truncation (`11Mn-9off → 0`) degeneracy.
- **Tail (`singleHubR_le_tie_tail_r8/r9/r10`, 3≤Mn≤9):** below the offEdge budget the low edge alone
  dominates every config — fully enumerated (`interval_cases Mn/c/b/a`), each routed to `off_maximal_general`
  at the concrete argmax via `hub_Aobj_eq`; `rw [offEdge] <;> …` handles the config=argmax reflexive case.

Combined with the large-size lemmas (`singleHubR_le_tie_07` M≥22, `_10` Mn≥31, `_89` Mn≥40), residues
8,9,10 are dominated at all Mn≥3, and every residue is closed at every size.  All kernel-clean (no `sorryAx`).

## Assembly — length-1 Hdom slice DONE (`R47SharpRate.lean`, kernel-verified)
`singleHub_dominated` / `sharpRate_singleHub_aligned`: an arbitrary Balanced+Capped single hub
`[(arms,c)]` at an aligned size (`11 ∣ 9·count 4 + 2c`) reduces via arm-permutation
(`Aobj_backbone_arm_perm` → `balancedArms_perm` → `(a,b)` counts) to `singleHub_le_tie`, hence is
dominated by `alignedTie` at its own `stateSize` (`= 1 + 11·count5 + 9·count4 + 2c`, `stateSize_singleHub`).
This is the length-1 case of `SharpRateNF`/`Hdom`, discharged by the M3 envelope.

## Honest frontier / next steps (dependency-ordered)
The single-hub (length-1 `Hdom`) side is now FULLY settled: **all 11 residues dominated at EVERY size,
with valid Balanced ties.**  The non-aligned-n layer for length-1 is CLOSED (it was NOT
Pant-entangled — that was an overstatement, corrected).  The small-M finite patches (item 1 below) are
now DONE (see the "SMALL-M PATCHES DONE" block above).  What genuinely remains:
1. ~~Small-M finite patches per residue~~ — DONE (`singleHubR_le_tie_small_r1..r10` + `_tail_r8/9/10`).
2. **GENUINELY OPEN (the real BG frontier):** `m ≥ 3` multi-hub domination — has only PROBES
   (`multi_hub_probe`, `three_hub_residual_probe`), NO all-nonneg Positivstellensatz cert like the
   two-hub `twoHub_le_tie`; the "5 non-box-certifiable cb≥1 cells" + the environment-merge machinery are
   the true obstruction.  And Hnorm / `StraightProgress_sized` (the tree→hub coverage dichotomy).
3. Assembly (`sharpRate_of_tieDomination`) at length ≥ 2 depends on (2) plus the multi-hub tie targets.

Full closure stays gated on the genuinely-open mathematics (Pant 2026: the global maximizer is open, and
the m≥3 multi-hub reduction is the concrete Lean-side obstruction).  The realistic, honest deliverable is
now large: both hard cores (M4 two-hub, aligned M3), the length-1 Hdom slice, and the FULL single-hub
envelope across all 11 residue classes at EVERY size — all kernel-anchored — with the open frontier
precisely delimited to `m≥3` multi-hub + Hnorm.  `conjecture1_proved = False`.

---

# ADDENDUM 2026-09-08 — the open-cores campaign (branch `bg/multihub-hnorm`)

The two "genuinely open" items above were attacked directly.  Both are now reduced to a SINGLE named
open piece each, with all surrounding machinery kernel-proven (no `sorryAx`; every module in the
proof-lean leaf list + AxiomGuard).  The stale framings above (the "5 non-box-certifiable cells", the
"coverage dichotomy" as an amorphous obstruction) are SUPERSEDED by the sharper reductions below.

## Hnorm (B-track): the FLP move class + the coverage reduction

- `BGSCLFlpMove.flp_local_straightStep` — the degree-equalizing FLP flip at its strDefect-reducing
  site is a `StraightStep_sized` (B1).
- `BGSCLFlpDeepLift` — **the per-level Obligation-A debt is DISCHARGED**: the cavity-gain pair
  (G1: `Ztot(dtSub)≤`, G2: `Zopen(dtSub)/udeg≤`) self-propagates through any ancestor frame
  (`dtSub_gains_lift`), closing at the root (`Aobj_child_replace_of_gains`); a deep FLP flip is an
  UNCONDITIONAL `StraightStep_sized` (`flp_deep_straightStep`) (B2).
- `BGSCLFlpStepAt` — the depth-closed, order-insensitive multi-flip class (`FlpStepAt`, `2m` leaves
  + all-cherry crest completed to an arm in one composite step); `FlpStepAt.straightStep`
  unconditional; `hnorm_of_coverage` reduces Hnorm's open half to EXACTLY a coverage statement (B3).
- HONEST coverage numbers (exact, n≤12): single-flip 48.5%, multi-flip 52.4% — and the class is
  COMPLETE for internal piece-completion.  Every escape is genuinely blocked: PARITY (piece sizes are
  {1,2}∪{odd≥3}, so even-size≥4 defective subtrees can never complete internally) or arm-children
  needing dismantling.  **Residual: cross-boundary move classes** (need a two-child joint-gain
  version of the lift machinery).

## m≥3 Hdom (A-track): the weak-pair telescope

- `R47R7StuckChar` — stuckness characterized structurally (`stuck_pair_deloaded`/`_dichotomy`:
  every adjacent pair's designated donor is de-loaded); the split precondition = a five-count
  inequality (A1).
- `R47WPairLift` — the strong pair fails for degree-jumping replacements; the WEAK pair
  (W1: `Ztot≤`; W2: `Ztot+Zopen/udeg≤`) survives by endpoint linearity in the ancestor weight
  `w∈(0,1]` and self-propagates (`dtSub_wpair_lift`, `Aobj_child_replace_of_wpair`) (A3(1)).
- `R47MHubTelescope` — **Hdom at ANY length (no stuckness!) reduces to ONE named certificate**:
  `PairCollapse` (every Balanced+Capped pair collapses to a same-size Balanced+Capped single hub
  with W1 ∧ W2 ∧ root-`Aobj`) + the single-hub tie bound (envelope DONE at every size).  Measured
  true with a common canonical target (c′=0, maximal-five) on all 15,876 grid pairs
  (`proof/verification/A3_WEAK_PAIR_COLLAPSE_FINDINGS.md`) (A3(3)).

## The honest frontier now

1. **`PairCollapse`** (A3(2)) — the symbolic 3-clause collapse certificate. De-risked; expect
   residue-class splits + monotone tails in the style of the single-hub envelope campaign.
2. **Cross-boundary move classes** for Hnorm's parity-blocked residual (two-child joint-gain lift).
3. **The tie-definition layer** — the non-aligned-n `tie : ℕ → UTree` representative selection
   consuming the envelope argmaxes (mechanical-ish assembly, known-open bookkeeping).

Full closure stays gated on the genuinely-open mathematics (Pant 2026).  `conjecture1_proved = False`.
