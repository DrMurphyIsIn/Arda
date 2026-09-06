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

## M3 — single-hub 2-D envelope: t-axis DONE + K≥23 envelope DONE, c-envelope tail OPEN
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
- **OPEN tail:** (a) the general `hubState a b c → colState K c t` size-decomposition lemma (b≡c mod 11,
  Nat); (b) `K = 22` (argmax mstar=1, not near-star) + the **5 ≤ K < 22 finite interior patch** (26
  explicit (K,c,t=1) configs, enumerated by `broadened_tie_2d_envelope.py`) → a general `mOf K` tie
  argmax; (c) assemble into `singleHub_le_tie` for all K.

## Honest frontier / next steps (dependency-ordered)
1. **M3 c-envelope tail:** the size-decomposition + `mOf K` + the 26-config finite patch → full
   `singleHub_le_tie` (length-1 SharpRateNF, all aligned K).  The clean K≥23 core is DONE.
2. **`sharpRate_of_tieDomination`** (bypassing the open `hrate`): case-split `s.length` → `singleHub_le_tie`
   (length 1) + `twoHub_le_tie` (length 2, DONE) + an explicit `hMulti` hyp (length ≥3).  Feed
   `Hdom_of_sharpRate` → `conjecture1_of_Hnorm_sharpRate`.
3. `m ≥ 3` multi-hub (the assisted-merge environment rules) and Hnorm / `StraightProgress_sized` (the
   tree→hub coverage dichotomy) remain the other open layers.

Full closure stays gated on the genuinely-open mathematics (Pant 2026: the global maximizer is open);
the realistic target is a scoped aligned-n result + a sharpened, kernel-anchored frontier. `conjecture1_proved = False`.
