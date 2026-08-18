# The R7' proof architecture: a complete skeleton (2026-08-14)

Synthesis of the day's ten commits (MR !69) with the pre-existing program: how the pieces now
COMPOSE into an end-to-end argument for R7' -- "for all large n, the de-loaded single-hub
five-cherry-bundle star S* maximizes pi(T) = per L(T)/prod deg over n-vertex trees" -- with
every remaining gap named and scoped.  Constants note: C_1 = (26/23)/rhoB = 0.919446 (an early
MR note said ~0.881 -- wrong arithmetic in prose only; every budget number used the correct
value).  conjecture1_proved = False: this is an architecture with named gaps, not a proof.

## Exact anchors (no asymptotics)

* **A1 (rate identity)** [rate_bound_fixed_n.py; Lean-portable on BridgeStep4c + phi_le_one]:
  for every tree T and every leaf root r,
  `pi(T) = Z(T^r) * R(r)`, `Z = exp(logPhi(parse)) * rhoB^n`, `R = (1+S)/(1+S/2) <= 4/3`.
  Hence `A(T) := pi/rhoB^n = exp(logPhi) * R`.
* **A2 (star value)** [one line, exact]: the de-loaded star with K five-cherry arms has
  `pi(S*) = (621/64)^K * (26/23) = C_1 * rhoB^n` EXACTLY (n = 1 + 11K).  Residue-absorbing
  balanced templates (arm loads {4,5}, hub load c0) give `A > C_1` slightly (e.g. 0.9203 at
  n = 211) -- the finite-n maximum is >= C_1 at every large n, so eliminating `A < C_1`
  never eliminates the maximizer.
* **A3 (ledger identity)** [slack_ledger_dichotomy.py; from the Lean-checked hinge]:
  `logPhi(T) = -phi(cav_root) - SUM_v slack_v`, slack_v >= 0, on plain parses.

## The pipeline

**STAGE I -- eliminate far trees (unconditional).**  By A1+A3, `A(T) <= (4/3) exp(-ledger)`;
ledger > log(4/(3 C_1)) = 0.37167 forces `A(T) < C_1 <=` the same-n maximum (A2).  The
context-free floors + the amortized hub bound [amortized_hub_bound.py] make this
UNCONDITIONAL: the surviving family F_n has (per parse) at most 15 pure hubs, 7 bare-leaf
defects, 68 chain/spacer nodes, 360 four-arm bundles, ... over free five-arm bundles.

**STAGE II -- reduce multi-hub survivors (the merge layer).**  Within F_n, hub-pair merges are
fixed-n surgeries and the UNIFIED TOPPED-UP MERGE [kelmans_unified_merge.py] is strictly
pi-increasing for all 36 load cells in any environment with per-neighbour 3deg+4load >= 16.
Any survivor admitting a certified merge is not the maximizer.  Repeated merging drives
survivors toward single-hub configurations.

**STAGE III -- the terminal single-hub family.**  Arms balance and the hub de-loads by the
proven Polya certificates (distribution.py / hub.py / arm_bound.py = R6), landing on the
balanced templates of A2; among these, the exact closed forms identify the per-residue
maximum (de-loading schedule), = S* at n = 1 mod 11 and its balanced variants otherwise --
the Conjecture-1 shape.

**STAGE IV -- strictness/uniqueness.**  Strict inequalities: the merge certificates have
strictly positive constants on the two-hub family; the ledger floors are strict off the free
shape; R5's exact crux (26/23)^11 < 621/64 breaks remaining ties.

## Named gaps (each precise, none an open-ended idea)

| # | gap | where it lives | status |
|---|-----|----------------|--------|
| G1 | symbolic hardening of the ledger floors (each a 1-var piecewise-smooth hinge minimization; 6 window shapes + ~10 key classes) | slack_ledger / amortized_hub | OPEN (routine, per class) |
| G2 | Plainify bookkeeping | gap_discharges.discharge_G2 | **DISCHARGED 2026-08-14**: plainification preserves logPhi EXACTLY (plainification_theorem.py); ledger telescoping + slack >= 0 verified on ALL rooted trees (nl arbitrary, matching the Lean quantifier); nl >= 2 classes carry floors >= 0.109 (+~0.18/leaf).  The dichotomy covers EVERY tree, losslessly |
| G3+G4 | merge blocking + small donors | g34_merge_unblocking.py | **NARROWED to one named family 2026-08-14**: (A) cap widened to 1/5 (35/36 cells + certified receiver-borrow route for (1,5)) -- arm(3) blockers gone; (B) the BALANCING LEMMA (certified: hubs with >= 2 other arm-neighbours; sharp in kind -- bare 2-arm hubs genuinely reverse) lifts leaves/low arms into the cap on arm-rich hubs; (C) boundary factor sharpened to R <= 6/5 at cherry-tip roots (S <= 1/2 exact) => budget 0.26631: nl>=3 nodes eliminated outright, hubs <= 11, leaves <= 5.  RESIDUAL DISCHARGED FOR TWO HUBS (g34_residual_domination.py, 2026-08-14): every defected two-hub stuck config (leaves <= 2, arm1 <= 9, arm2 <= 13 -- the ledger budget) is dominated by a same-n single-hub template, via receiver/donor symbolic tails (factor-bound + per-residue comparator search; donor arm2 full-symbolic to j = 6, higher j routed) + a 442,800-case exact rational finite sweep.  KEY: the winning comparator is residue-dependent (sometimes the load-6 hub -- the defect-carrying template genuinely loses at small odd-residue sizes).  G34-MULTI STAR-OF-HUBS DISCHARGED (g34_multi_starofhubs.py, 2026-08-14): the depth-2 archetypes (cheapest vertex covers: top-defected AND all-subs-defected stars of hubs) dominated via exact factored closed forms + 972 symbolic certificates (S = 2..10 concrete, symbolic in (pT, q), per-residue comparator search, ZERO hard cases) + 2520-case exact asymmetric sweep.  G34-DEEP DISCHARGED (g34_deep.py, 2026-08-14): (1) the GENERIC THETA-LEMMA -- ledger > 0.2813 (= sharpened budget + max G5 template deficit) => dominated at any shape/depth/placement; (2) depth >= 4: ALL adversarial chains clear THETA (min ledger 0.3299) -- generic; (3) depth-3: sub-THETA region proven FINITE (every family's ledger clears THETA in pL) and exactly dominated via the verified chain-3 closed form (worst ratio 1.175); (4) asymmetric depth-2 tails: 400 random large defected stars exactly dominated (worst 1.172), ratio FLAT in each size (spread 0.008 vs 17%+ margins).  INTERPOLATION LEMMA PROVED (interpolation_lemma.py, 2026-08-14): (I1) the EXACT sub-hub curve -- cav(q) = 23/(26q+23), B*rhoB = 26/(23+3cav) (V5 = rhoB^11 exactly); (I2) the EXACT sign dichotomy -- the config bound is monotone in every cavity with sign polynomial 23z_t - 3 - 3Tz_t, i.e. decreasing iff the top is arm-heavy (3dt+4cT >= 23); hence the sup over ALL size vectors is at cav->0 (heavy tops: top-only limit, certified, margin 1.106) or at q=1 (light tops: 212 finite exact checks).  Stage II of R7' is REDUCED TO A NAMED G1 SLIVER (Amendment 1 below; NOT "closed" -- g34_deep's depth>=3 genericity rests on sampling + an unproven monotonicity, and the interpolation lemma is a theorem only for depth-2 stars-of-hubs).  Remaining across the whole architecture: G1 symbolic hardening of the numeric-certificate layers, G7 (the Lean campaign), independent review |
| G5 | STAGE III finite-n de-loading | gap_discharges.discharge_G5_lemmas + finite_table | **DISCHARGED 2026-08-14**: four symbolic shedding lemmas (L1 c0-shedding K>=25; L2 j6-beats-c0 K>=40; L3 pair-shedding K>=25; L4 arm-count K>=40, engine V5^9/W4^11 = 1.0114) prove the canonical template (d,0,0)/(0,-d,0) wins at every residue for K >= 40; exact rational winner table below (the de-loading schedule, matching maximizer_structure empirics) |
| G6 | the "large n" threshold | gap_discharges | **DISCHARGED**: n0 = 421 (K >= 40); below n0 the finite exact table applies |
| G7 | Lean formalization of the above (the campaign's R47 phases; P2B design + rate-identity port notes already in this directory) | R47 campaign | OPEN (the campaign) |

## What exists in Lean today vs what this adds

CI-green now: phi_le_one (the hinge), the full Branch->per(L) bridge (4j capstones), R47 P1
(pi_utree) + P2a.  This document's stages I-IV consume: phi_le_one (A3's engine), the bridge
(A1's engine), and the merge/floor certificates (all LemmaA-style rational inequalities,
positivity-friendly).  Nothing in the pipeline requires a tool the program has not already
machine-checked at least once in kind.

## Honest overall status

Every stage is either proven (numeric-certificate rigor or better) or reduced to a NAMED,
bounded gap (G1-G7).  No stage rests on an unformulated idea.  The marginality wall -- the
program's historic obstruction -- enters only through the Lemma-A locus and is priced and
contained (tax + amortization).  The residual mathematical risk concentrates in G3/G4 (the
finite defect-adjacent case analyses), which are exactly the kind of finite structured
problems this program has repeatedly closed.  conjecture1_proved = False until G1-G7 are
discharged and independently reviewed.

## Amendments from the independent review (2026-08-14, REVIEW_20260814_MR69.md)

1. **Stage II status, corrected language**: read "CLOSED" above as **"reduced to a named
   G1 sliver"** (the modules' own in-file language). Specifically: `g34_deep`'s depth >= 3
   genericity/finiteness rests on sampling + an unproven monotonicity, and the
   interpolation lemma is a theorem for depth-2 stars-of-hubs; the deeper-shape closure is
   at numeric-certificate rigor pending G1 hardening.
2. **PRIORITY G1 item (reviewer finding)**: `amortized_hub_bound`'s intermediate
   `DELTA_CHARGE = 0.0240` is FALSE in the limit (true infimum `EPS/(1+T0) = 0.023587`,
   approached by all-children-just-below-window; the in-module sweep misses the
   minimizer).  The FINAL bound `DELTA_AMORT = 0.0235` survives on the true infimum but
   with only ~9e-5 margin at float rigor — the <= 15-pure-hub cap is fragile and must be
   re-derived from the true infimum during G1.  Also reconcile the status contradiction:
   `slack_ledger_dichotomy.py` calls this layer CONJECTURAL/named-open while
   `amortized_hub_bound.py` says PROVEN/UNCONDITIONAL — the former is correct until G1.
3. **Lean status correction**: the review's G7 note that the permanent-of-Laplacian
   bridge is unformalized is stale; the bridge IS machine-checked (2026-08-14 capstones
   `pi_litHub'`/`amplitude_bridge_real'`/`pi_utree`, reviewed PASS).  The true A1 residual
   is the phantom-root parse identity `pi = Z * R` for arbitrary trees (the mapped port).
