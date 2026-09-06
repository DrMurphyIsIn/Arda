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

## M3 — single-hub joint optimum (2-D): atoms landed, envelope OPEN
CORRECTED scope (a false shortcut was caught by the build + refuted numerically): the maximizer is
the trade family, but proving it is the 2-D optimum over all Balanced `(a,b,c)` with `11a+9b+2c=11K`,
`c≤5` — parametrized as `(K−c−9t, c+11t, c)` for `c∈{0..5}, t≥0` (trade family = `t=0` edge).
- **t-axis atoms (kernel-verified):** `hubState`, `hub_Aobj_eq` (general single-hub value),
  `hubQ`/`hub_Aobj_factored`, **`hub_bulk_le`** — the bulk-swap comparison (9 load-5 → 11 load-4 arms,
  factor `F=(513/80)^11/(621/64)^9`), the exact analog of `tie_trade_le`.
- **OPEN (the hard core):** the **2-D envelope** `max_t Aobj(c,t) ≤ Aobj(mstar,0)`. The per-axis
  optima don't align (c=0 favors t=1), and there is **no uniformly-finite monotone move-chain**
  (verified: bounded-move local-max traps whose escape-support grows with K). Needs a genuine 2-D
  argument (t-unimodality via the bulk atom + a c-envelope), not a separable proof.
- Useful existing piece: `R47ArmPerm.lean` proves `Aobj` **arm-permutation invariance**.

## M4 — two-hub domination: diagnosed, Aobj bridge OPEN
`two_hub_gap_pos_c0..c5` (R47R7KelmansTwoHubCert) are **proven but ABSTRACT** Positivstellensatz facts
`0 < poly(x,y)` — NOT wired to `Aobj`. The closed forms `pi_two_hub_closed`/`pi_template_closed` are
the *Python* source, not Lean. `twoHub_le_tie` needs that bridge **ported**: compute `Ztot(dtSub hubB)`,
plug into `Ztot_hubNode` (R47Backbone) / `Aobj_backbone` (R47BackboneAmp) for hub A, clear to the
`(x,y=pA−1,pB−1)` form, and prove equality to each cert's numerator. Machinery exists; the exact
denominator-cleared **polynomial match is the multi-hour crux**. (m≥3 multi-hub + the 5 cb-heavy
general-env cells remain open beyond two-hub — see `BG_RESIDUAL_CORE_ISOLATION` closure: they are
outside the Balanced+Capped merge domain Hdom uses.)

## Honest frontier / next steps (dependency-ordered)
1. **M4 Aobj bridge** (concrete, ~hours): port `pi_two_hub_closed`/`pi_template_closed` via `Ztot_hubNode`
   + match `two_hub_gap_pos_c*` → `twoHub_le_tie` (Hdom, length-2, aligned n).
2. **M3 2-D envelope** (needs a real insight): t-unimodality (bulk atom, near-copy of `tradeStop_persists`
   but messier `F`) + the c-envelope bound.
3. Then `sharpRate_of_tieDomination` (bypassing `hrate`) → `Hdom` for single+two-hub, aligned n.
4. Hnorm / `StraightProgress_sized` (the tree→hub coverage dichotomy) remains the other open layer.

Full closure stays gated on the genuinely-open mathematics (Pant 2026: the global maximizer is open);
the realistic target is a scoped aligned-n result + a sharpened, kernel-anchored frontier. `conjecture1_proved = False`.
