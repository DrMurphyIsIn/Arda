# R4-R7 formalization campaign — design (2026-08-14)

Goal: formalize the reduction layer of the Brualdi--Goldwasser program — that every tree is
dominated by the de-loaded single-hub 5-cherry-bundle star — on top of the CI-green R3
bridge (`phi_le_one`, `pi_litHub'`, `amplitude_bridge_real'`, reviewed PASS 2026-08-14).

HONEST STATUS AT START (conjecture1_status.py): R1, R2, R4, R5, R6 are PROVEN at
Python/paper level with exact certificates; **R7 is OPEN even on paper** — the rewrite
system (kelmans_confluence.tex) gives termination + local-confluence architecture, but
(a) rule (K)'s A-monotonicity on the measure-zero stratum boundary is only verified to
n = 240, and (b) making R3's branch-replacement globally well-defined and non-decreasing
is not done. The campaign therefore follows the R3 playbook: scaffold everything,
machine-check the provable layers, and REDUCE Conjecture 1 to explicitly named open
hypotheses — never assert them.

## Ground truth

- `outreach/kelmans_confluence.tex` — the rules (def:rules), measure (def:measure),
  termination (prop:term), local confluence (critical pairs), Newman assembly.
  Rules: (H) hub-merge [R5], (B) branch-to-arm [R3], (K) Kelmans compression [R4],
  (L) leg-to-cherry [R2], + rebalancing [R6]. Measure mu(T) = (h, b, d, e) in N^4, lex.
- `global_assembly.py`, `psi_close.py` (R4 bilinear identity + corners), `legs.py` (R2),
  `rem_tie.py` + ExactCruxes `(26/23)^11 < 621/64` (R5), `distribution.py`/`hub.py` (R6),
  `spiders.py` (R1, N0 = 412).

## Design decisions

1. **Objects**: new inductive `UTree := node (List UTree)` (unweighted rooted trees) for
   the rewrite layer. The paper's objects are unrooted; the plan is canonical rooting (at
   a hub / centroid) with root-invariance lemmas where surgery demands it. RISK: rooted vs
   unrooted bookkeeping is the main modeling hazard — resolve in P1 before any rule work.
2. **Objective through the bridge, not permanents**: define `dtRealize : UTree -> RTree`
   (true-degree weights: root d = childCount, internal d = childCount + 1, weight
   1/(d*d') per edge — exactly the `litHub`/`GoodTree` convention) and
   `A (t) := Ztot (dtRealize t)`. Then generalize `BridgeStep4i/4j` beyond `litHub`:
   `pi_utree : per L (aGraph (realize (dtRealize t))) / prod deg = A t` — `realize_weights`
   and `aGraph_realize_isAcyclic` are ALREADY generic; only a `GoodTree` instance +
   `childCount` arithmetic for `dtRealize` is new. All rule comparisons then live in the
   rational `Ztot` recursion (LemmaA/e2-style algebra), never in permanents.
3. **Rules as an inductive relation** `Step : UTree -> UTree -> Prop` (constructors H, B,
   K, L, R for rebalance), each a local surgery expressed structurally (no graph surgery:
   list edits at a node). mu as `UTree -> N x N x N x N`; termination =
   `WellFounded (InvImage (Prod.Lex ...) mu)` on Step-inverse.
4. **Conditional assembly first**: Newman's lemma (check Mathlib: `Relation.*` — if absent,
   prove it; it is short over a well-founded order) gives unique normal forms from
   termination + a `LocalConfluent Step` hypothesis; A-dominance along rewrite chains from
   per-rule hypotheses `A_mono_H/B/K/L/R : Step_X t t' -> A t <= A t'`. The conditional
   capstone: `conjecture1_of (hlc) (hH) (hB) (hK) (hL) (hR) (hNF) : forall t, A t <= A (star-config n)`.
5. **Discharge order** (easiest exact-arithmetic first):
   - `A_mono_L` (R2, legs.py rational inequalities),
   - `A_mono_K`-INTERIOR (R4, psi_close bilinear identity + nonneg corners — nlinarith/SOS),
   - `A_mono_H` (R5: the `(26/23)^11 < 621/64` crux is ALREADY in ExactCruxes.lean),
   - `A_mono_R` (R6: Polya rebalancing + hub de-loading transfer),
   - local confluence `hlc` (critical-pair case analysis — long but mechanical),
   - normal-form characterization `hNF` (no rule applies -> star shape),
   - `A_mono_B` (R3 seam: finite-n branch dominance from `phi_le_one` — contains the open
     "globally well-defined branch replacement" question; may need its own mini-bridge),
   - `A_mono_K`-BOUNDARY — **the known open gap** (n <= 240 verified). Stays a named
     hypothesis until proven; this is the research frontier, not a formalization task.

## Phases (each = 1-3 CI-sized files, the bridge cadence)

- **P1** `R47Tree.lean`: UTree, size, degrees, dtRealize + GoodTree instance + childCount
  arithmetic, `A`, `pi_utree` (unconditional). Payoff: the objective is machine-checked to
  be THE real quantity for EVERY tree, before any rule exists.
- **P2** `R47Rules.lean` + `R47Measure.lean`: hubs/legs/arms recognizers, Step, mu,
  per-rule mu-drop lemmas, `WellFounded` termination.
- **P3** `R47Newman.lean`: Newman (or Mathlib import), unique normal form + A-dominance
  along `Relation.ReflTransGen Step`, the conditional capstone `conjecture1_of ...`.
- **P4** `R47MonoL.lean`, `R47MonoK.lean` (interior): exact-arithmetic discharges.
- **P5** `R47MonoH.lean`, `R47MonoR.lean`: R5 crux reuse + R6 transfer algebra.
- **P6** `R47Confluence.lean` + `R47NormalForm.lean`: critical pairs; star characterization.
- **P7** `R47MonoB.lean`: the R3 seam (needs its own design note once P1-P3 exist).
- Remaining open after P1-P7: K-boundary (+ whatever P7 isolates). Ledger stays
  `conjecture1_proved = False` until BOTH close and a further independent review passes.

## Method (inherited from the bridge, non-negotiable)

Grep the PINNED Mathlib/core for every lemma signature before writing; one file per CI
cycle where possible; ascribe every `tendsto_const_nhds`-style composition; `dsimp only`
only for genuine proj-redexes; expect kernel restrictions on nested inductives (no
recursive occurrence under `And`); never run `lean` locally; monitor the lean-verify JOB.
All state to memory + this doc after every cycle. conjecture1_proved=False.

## P2 design addendum (2026-08-14, after reading global_assembly.stratification)

FINDING: R7's live formulation is a STRATIFICATION, not a rewrite on arbitrary trees:
(i) rate < rho_B stratum: A(family) -> 0 < C_1. Largely SUBSUMED by R3 — whole-tree
    Phi<=1 (the per-node induction at any rooting) IS rate <= rho_B; the residual is the
    sub-exponential arm-normalization -> rate link. Lean target: a whole-tree corollary of
    `phi_le_one` (apply the Branch induction to arbitrary rooted trees — needs the
    Branch-encoding of a general tree or a direct Ztot bound), then the growth-rate link.
(ii) rate = rho_B stratum: branches are cherry-arms => backbone of hubs carrying arms;
    the Kelmans rewrite (K/H + rebalance) operates ONLY on this structured family —
    MUCH smaller rule domain than "any tree": states are (backbone of hubs, arm counts,
    cherry loads), i.e. essentially INTEGER COMPOSITIONS, not general trees.

CONSEQUENCES for P2:
1. The rewrite layer's state space can be a COMBINATORIAL encoding (hub sequence with
   arm/cherry counts) rather than raw UTree surgery — rules become arithmetic moves on
   lists of naturals; mu-termination and confluence become elementary. The UTree/Aobj
   layer (P1, done) connects the encoding to the real objective via a realization map
   (encoding -> UTree) — one honest seam lemma per rule instead of general tree surgery.
2. (L)/(B) (legs/branches) live in the STRATIFICATION step (rate-maximality forces
   cherry-arms), not in the rewrite: formalize them as part of stratum (i)/(ii)
   classification, not as fixed-n surgeries. This dissolves the fixed-n size-accounting
   problem flagged in the base design.
3. Objective at fixed n: Aobj (P1) suffices — rho_B^n is constant per n, so
   pi-monotonicity = A-monotonicity within a stratum step.
REVISED P2: (a) the stratum-(ii) state encoding `HubState := List (arm-count, cherry-load)`
+ realization to UTree + Aobj formula on states (closed form via Ztot recursion — compare
Ztot_litHub); (b) K/H/rebalance as arithmetic moves on HubState with mu; termination.
P3+ unchanged in spirit; stratum-(i) becomes its own phase (whole-tree phi_le_one
corollary + the rate link — flagged open pieces stay named hypotheses).

## 🏁 MERGE-LAYER CAPSTONE GREEN (2026-08-15, 63876364)

R47StepMono machine-checked: step_mono + chain_mono + chain_to_normalForm — every
Balanced∧Capped state rewrites, monotonically in per L/∏deg (pi_utree), through
certified ordered merges (both directions, strict-mirror ordering complete at all
depths, no stuck states) to an ordered-merge normal form.  All 25 R47 files green,
no sorry.  The P1-P5e program is COMPLETE.  Next: the (L)/(B) normalization layer
(gate + ground truth in P5_SEAM_DESIGN.md).  conjecture1_proved=False.

## P2b status (2026-08-14)

DONE (R47Step.lean, R47StepSize.lean): the Step relation with the unified topped-up
merge as the single constructor (P2B_MERGE_DESIGN) + tail congruence; machine-checked
no-debris ({4,5}-family invariance), one-hub-per-step measure drop, well-founded
termination, head-pair applicability from a count witness, normal-form existence,
single-hub sink, conditional A-dominance chain seam; and FIXED-n conservation
(usize/stateSize invariant under Step -- the `1+2cb+11k = 9k+11 at cb+k=5` bookkeeping).
The per-step A-monotonicity is the named hypothesis for P4/P5 (the 36-cell certificates).
Lean gotcha: `++` is LEFT-assoc (infixl) -- `simp [mem_append]` on `a ++ b ++ c ++ [x]`
yields a LEFT-nested disjunction `((A ∨ B) ∨ C) ∨ D`; rcases patterns must nest left.

## P4 status (2026-08-14): the 36-cell certificate table in Lean

DONE CI-green (P4a `R47Cert.lean`, P4b `R47CertB.lean`) + in-CI (P4c `R47CertC.lean`,
P4d `R47CertD.lean`): `Fw`/`zw` loaded-hub factors, `beforeD`/`afterD` merge comparison,
`bilinear_corner_nonneg` (box-to-corner reduction), and per cell: bilinear decomposition
theorem + four sympy-exported Polya corner certificates (all-nonneg-coefficient numerator
over factored positive denominator; `field_simp`+`ring` identity, `positivity` closes) +
assembled box theorem.  Generator `gen_r47cert_cells.py` (laplacian_ratio/) emits any
cell from the sympy certification with per-cell self-checks (symbolic decomposition +
nonneg numerators, all 36 pass).  Template proven first-try green in P4a AND on the
generated P4b row.

REMAINING for per-step A-monotonicity (the P2b named hypothesis): the ENVIRONMENT SEAM —
the exact factorization `pi(T'') - pi(T) = Penv * FQ * FSr * D(sigma_Q, sigma_r)` on the
HubState realization, plus the marginal-box bounds (sigma in the certified boxes under
the 3deg+4load >= 16 cap) — the one structural induction left (porting order item 4,
mirrors psi_close piece (2)).  Then `Aobj_mono_chain`'s hypothesis discharges on the
balanced family and the merge layer's monotonicity is a theorem.

## Stratum-(i) rate-identity port note (from rate_bound_fixed_n.py, mapped 2026-08-14)

Two simplifications fall out of the campaign's dtSub/dtRealize conventions:
* the PHANTOM-ROOT weight 1/(d+1) IS `dtSub`'s root convention (`dtChildren (cs.length+1)`),
  while the true-root weight 1/d is `dtRealize`'s -- so the exact identity
  `pi = Z * R` is the linear-in-root-weight comparison `Aobj t` vs `Ztot (dtSub t)`,
  with the A0/A1 split ALREADY proven as `Matched_factor`;
* step (2)'s matching injection (S <= 1 at a leaf root) is FREE here: at d = 1,
  S = z_c * Zopen/Ztot <= 1 follows from `Matched_dtCh_nonneg` (Ztot >= Zopen) +
  `Zopen_dt_pos` -- no injection argument needed.
The remaining genuine seam for the port is the raw-tree -> Branch parse
(`Ztot (dtSub t) = Ztot (litRealize (parse t))`, the cherry-folding direction of
BridgeStep2/STEP4C) feeding `exp_logPhi_mul_rhoB_pow` + `phi_le_one`.

## P2a3 spec (backbone seam) — ready to execute

State recursion (new file R47Backbone.lean, imports R47HubForms):
- `hubTailDeg : Hub -> List Hub -> N` = arms.length + c + (if rest = [] then 0 else 1) + 1
  (INTERNAL hub full degree); root hub degree drops the trailing +1.
- Mutual state functions (structural on List Hub):
    `ZtotS/ZopenS : Hub -> List Hub -> R` mirroring Zopen/Ztot of dtSub (backboneU ...):
    ZopenS h rest = Popen-part = (prod arm Ztots) * (3/2)^c * (ZtotS-of-rest if any)
    ZtotS h rest  = ZopenS * (1 + sum wQ arms + c/(3 dInt) + wQ-of-rest)
  BUT simpler and less error-prone: DON'T define separate state functions; prove the seam
  DIRECTLY as closed-form recursion lemmas about `Ztot (dtSub (backboneU s))` and
  `Zopen (dtSub (backboneU s))`, i.e. two mutual theorems computing them by the assembly:
    `Ztot_backbone_cons : Ztot (dtSub (backboneU ((arms,c) :: rest))) = ...`
  using: dtSub_node + dtChildren_append (twice) + Popen_append/Matched via `Matched_factor`
  (hne from positivity of all child Ztots: arms (Ztot_dtSub_armU_pos), cherries (3/2 > 0),
  tail (recursion)) + Popen_dtChildren_arms + Popen_replicate_cherry-analog
  (`dtChildren_replicate_cherry` + Popen_replicate_cherry) + sum_wQ_arms + sum_wQ_cherries
  + the tail singleton (dtChildren d [backboneU rest] = [(1/(d * udeg(backboneU rest)), dtSub ...)]).
- CAREFUL: the match-in-def of backboneU means its equation lemmas need `rw [backboneU]`
  with the rest-shape split (rcases rest); prove `backboneU_nil` and `backboneU_cons_nil`/
  `backboneU_cons_cons` equation lemmas FIRST and only ever rw with those.
- Root seam: `Aobj_backbone : Aobj (backboneU s) = ...` — same assembly with root degree
  (childCount, no +1); factor the shared computation over a DEGREE PARAMETER d:
    ONE core lemma `Ztot_hubNode (d) (hd : 0 < d) (arms c tail-part)` computing
    `Ztot (RTree.node (dtChildren d (arms.map armU ++ replicate c cherryU ++ ts)))`
  for `ts` either [] or [backboneU rest], THEN instantiate d := internal/root. This avoids
  duplicating the assembly.
- Positivity chain: `Ztot_dtSub_backbone_pos` mutual with the recursion (for Matched_factor's
  hne and later cavity ratios).
Deliverables: Ztot_hubNode core lemma; backboneU equation lemmas; Aobj_backbone +
Ztot/Zopen_dtSub_backbone recursions; positivity. NO AState needed — the recursion lemmas
ARE the state-level interface for P2b's monotonicity proofs.
