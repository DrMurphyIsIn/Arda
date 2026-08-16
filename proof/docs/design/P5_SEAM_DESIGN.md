# P5 design: the environment seam — from the certified D-table to per-step Aobj monotonicity

Goal: discharge P2b's named hypothesis
`Step s s' → Aobj (backboneU s) ≤ Aobj (backboneU s')` (on the certified family),
using the CI-green 36-cell table (P4a-P4d) — the Lean analogue of the Python identity
`pi(T'') − pi(T) = Penv · FQ · FSr · D(σ_Q, σ_r)`.

## The key algebraic facts (derived 2026-08-14, to be Lean-ified)

**S1 — the dressing lemma.** The P2a hub form folds EXACTLY into the loaded (F, z)
language already defined in R47Cert:
`F(d,c) = (3/2)^c · (1 + c/(3D))` with `D = d + c` the FULL degree (check:
`(3/2)^c + (c/(2(d+c)))(3/2)^(c-1) = (3/2)^c(1 + c/(3(d+c)))` — pure algebra), and the
neighbour-sum folding
`(3/2)^c · (1 + c/(3D) + (1/D)·Σ qᵢ) = F(d,c) · (1 + z(d,c) · Σ qᵢ)` where
`z(d,c) = 3/(3d+4c)` and `qᵢ = Qᵢ/Dᵢ = (Zopen/Ztot)ᵢ / udegᵢ` per structural neighbour
(uses `3D + c = 3d + 4c`).  So `Ztot_hubNode` re-expresses as
`Ztot = (child blocks) · F(d,c) · (1 + z(d,c) · Σ qᵢ)` — a field_simp/ring corollary of
the existing `Ztot_hubNode`.  The certificate table's `Fw`/`zw` are ALREADY this F and z
(cross-checked against Python `F_of`/`z_of` in P4a).

**S2 — arm activities are exact.** For a bare load-j arm: `Ztot(dtSub (armU j)) = F(1,j)`
(P2a closed form; j = 5 gives 621/64 = the tie constant) and its dressed contribution
`q = Q/D = 3/(4j+3) = z(1,j)` EXACTLY (from `Zopen/Ztot_dtSub_armU`, `udeg_armU`).
So load-5 arms contribute exactly `z15 = 3/23`, load-4 arms exactly `z14 = 3/19` — the
constants hard-wired in `beforeD`/`afterD`.  These are 1-line corollaries of P2a.

**S3 — the head-merge identity.** For a merge at the HEAD of the state, apply S1 twice
(root hub a; donor sub-hub b) and collect:
`Aobj(after) − Aobj(before) = (positive common blocks) · D(σ_Q, σ_r)`
with `σ_Q` = the dressed q-sum of a's other neighbours, `σ_r` = the donor's non-borrowed
movers' q-sum.  One large field_simp/ring identity over the P2a recursion forms — the
Lean analogue of `verify_unified_identity`.  This is the core new content of P5.

**S4 — box bounds on the certified family.** The certificates need
`σ_Q ∈ [0, (da−1)·3/16]`, `σ_r ∈ [0, v·3/16]` (topped-up) / one-arm floor `σ ≥ 3/23`
(direct).  Per-neighbour bounds:
* load-5 arm: q = 3/23 ≤ 3/16 (exact, S2); load-4 arm: q = 3/19 ≤ 3/16 (exact, S2) —
  note the crude bound q ≤ 1/D = 1/5 > 3/16 FAILS for load-4 arms; the exact dressed
  value is required;
* tail hub with ≥ 5 arms: q = Q/D ≤ 1/D ≤ 1/6 ≤ 3/16 (Q ≤ 1 from positivity; D ≥ 6) —
  the crude bound suffices;
* the one-arm floor (direct cells): a's bundle contains a load-5 arm ⇒ σ ≥ 3/23 exact.
CONSEQUENCE: the family invariant needed is `Balanced` (arms ∈ {4,5}, P2b) PLUS a cap
condition on backbone hubs (≥ 5 arms, or any shape with full degree ≥ 6).  Define
`Capped : List Hub → Prop` and prove Step preserves it (the residue is arms {4,5} and
the absorber's degree grows — preservation should be easy).

**S5 — the degree-ordering premise (HONEST FLAG).** The table is certified for
`da = db + u, u ≥ 0` — the ABSORBER has degree ≥ the donor.  P2b's `Step.merge` has NO
such premise today.  The discharge therefore needs either (a) adding
`hord : donor degree ≤ absorber degree` to the `merge` constructor (P2b amendment —
matches the Python dichotomy's "hubward pair a ≥ b, else reverse roles"), or
(b) a reversed-roles merge constructor with its own certified table.  Take (a) first;
(b) only if the R5/R6 layer needs both directions.

**S6 — tail congruence WITHOUT environment induction.** A merge deeper in the backbone
changes the tail subtree.  Aobj of `hd :: s` is LINEAR in the tail's pair
`(Ztot_tail, Zopen_tail)` with POSITIVE coefficients (from `Ztot_hubNode`:
`... = α·Ztot_tail + β·Zopen_tail`, α, β > 0 — the `w·Q` term is `w·Zopen/Ztot` times
the Ztot factor).  So the `tail` case follows if the merge does not decrease BOTH
`Ztot (dtSub (backboneU ·))` AND `Zopen (dtSub (backboneU ·))` of the sub-backbone.
* The Ztot comparison = S3 in the INTERNAL-degree convention (Ztot_dtSub_backbone).
* The Zopen comparison is SIMPLER: Zopen = product of child blocks (no root coupling),
  and the after/before ratio is the σ_Q-free part of D — a smaller affine certificate
  per cell (no sQ variable; likely provable from the existing corners at sQ = 0, or a
  6×… mini-table to generate).
This AVOIDS porting the arbitrary-environment Penv factorization entirely — the
recursion IS the environment induction, done once in P2a.

## Phasing

* **P5a** `R47Dress.lean`: S1 (dressing corollary of Ztot_hubNode) + S2 (arm q's) +
  the subtree bounds Q ≤ 1, q ≤ 1/D (positivity chain exists in P2a4).
* **P5b** `R47Capped.lean`: the `Capped` invariant + Step preservation + S4 box bounds
  for a state's neighbour lists (sums over mapped arms with per-element bounds).
* **P5c** `R47Head.lean`: S3 head-merge identity (Ztot internal + Aobj root forms),
  likely the hardest single ring identity of the campaign; validate on the (0,5) cell
  end-to-end first (head merge, no movers: k=0 σ_r floor case).
* **P5d** `R47MonoStep.lean`: S5 ordering amendment to Step.merge (P2b edit + re-run
  its theorems), S6 Zopen mini-table + linearity, assembly:
  `step_mono : Step s s' → StateOK s → Aobj (backboneU s) ≤ Aobj (backboneU s')`,
  then `Aobj_mono_chain` instantiates — the merge layer's monotonicity becomes a
  THEOREM on the certified family.

## P5d-2 spec: the 36-branch dispatch (executable design, 2026-08-15)

Per-cell ADAPTER theorems in ℕ-degree form (generated, extend gen_r47cert_cells.py):
for cell (cA, cb), k = 5-cb, given `dA dB : ℕ`, `hord : dB ≤ dA`,
`hdb : k+1 ≤ dB` (topped) / `2 ≤ dB` (direct), and the UNIFORM box
`sQ ∈ [0, (dA-1)·3/16]`, `sr ∈ [floor_row, (dB-k-1)·3/16]` (floor 3/23 iff cb = 5;
note (dB-k-1) covers BOTH rows since direct has k = 0):
conclude `beforeD (dA:ℝ) (dB:ℝ) cA cb k sQ sr ≤ afterD (dA:ℝ) (dB:ℝ) cA k sQ sr`.
Proof template: u := ((dA-dB : ℕ):ℝ), v := ((dB-(k+1) : ℕ):ℝ) (direct: dB-2) --
ℕ-subtraction exact under hord/hdb, so `Nat.cast_sub` gives
`e1 : (dA:ℝ) = u + v + (k+1)`, `e2 : (dB:ℝ) = v + (k+1)`; `rw [e1, e2]` in goal
(safe: e-RHSs contain casts of subtractions, not the bare `Nat.cast dA/dB` patterns);
rewrite the box hyps by the same ring equalities; `exact <cell>_cell u v sQ sr ...`.

Top-level `head_merge_le` (hand-written): hypotheses = hsplit + BalancedArms armsA/
others + Capped rest + `5 ≤ armsA.length`/`5 ≤ armsB.length` (family) +
`hord : armsB.length + |tailU rest| ≤ armsA.length` (S5 ordering, named residual for
the anti-hubward direction) + `cA ≤ 5`, `cb ≤ 5`, `k = 5-cb`.
Box data established ONCE from P5b/P5d-1: hQ1 via `sum_zw_arms_le` (dA-1 =
armsA.length), hS1 via `sum_zw_arms_le` + `qSum_tailU_le` (dB-k-1 = others.length +
|tail| by hsplit.length_eq), floor via `sigmaArms_floor` (others ≠ [] from hB5 at
k = 0) + `qSum_tailU_nonneg`.  Then `apply head_merge_le_of_cellD`, subst k,
`interval_cases cb <;> interval_cases cA`, 36 branches each
`exact dispatch_<cell> ...`.

After P5d-2: the Step-level assembly (P5e) = the ordering-conditioned `merge` case +
S6 tail congruence (the Zopen mini-table: the sigma_Q-free comparison per cell — check
first whether the existing corners at sQ = 0 suffice via the bilinear structure).

## P5e design: the Step-level assembly (probed + designed 2026-08-15)

**S6 two-channel route REFUTED (probe, 289 states):** the parent sees a child through
the pair `(Ztot, Zopen/D)`, and the merge DECREASES the `Zopen/D` channel in 284/289
cases (ratios to 0.71) while `Ztot` never decreases (0/289).  Channel-wise
monotonicity is FALSE — the whole-tree increase is a compensated trade
(the environment identity's σ_Q coupling).  Do NOT retry per-channel induction.

**The route that works — root at the absorber:**
1. `Aobj` is a matching sum over the TRUE-degree edge-weighted tree; the weights are
   root-independent, so Aobj is invariant under re-rooting the encoding (backbone
   REVERSAL verified exactly, 60/60).  Formal path — SUPERSEDES the earlier
   msum-relabeling idea (no relabeling needed): the EDGE-SPLIT identity
   `Ztot (node (X ++ (w,T) :: Y)) = Ztot (node (X++Y)) * Ztot T
      + w * (Zopen (node (X++Y)) * Zopen T)`
   (R47Rotate, part 1 -- pure Popen/Matched append algebra) is SYMMETRIC in the two
   edge components; one-step root rotation follows because both rootings of an edge
   reduce to the SAME four component terms with the SAME degrees (the u-side rooted
   at u has degree |blockA|+1 whether u is the root or v's child -- the +1 is the uv
   edge either way, and the edge weight 1/(D_u D_v) is symmetric).  Iterating along
   the backbone places the root at any hub.  Part 2: the state-level rotation
   (`AobjV up h down` with the up-tail as a distinguished middle child, via
   `Ztot_append_split` at both rootings) -- no permutation lemmas needed if the
   split is taken at the actual child position.
2. The rooted-at-absorber view of an INTERIOR merge is a hub with arms + cherries +
   TWO tail blocks — and `Ztot_hubNode_dressed` already takes an ARBITRARY child
   block `ts`; a two-element `ts = [donor-side, parent-side]` re-instantiates the
   head identity verbatim, with the parent-side environment entering σ_Q exactly as
   the certificates expect (`da` counts it; its dressed cavity ≤ 3/16 under Capped
   via `q_dressed_le_of_udeg`).  So the interior-merge identity is a cheap
   re-instantiation, NOT new machinery.
3. Assembly: `OrderedStep` (Step + the hubward ordering side condition per merge) →
   `step_mono` on Balanced ∧ Capped states → `Aobj_mono_chain` discharges.

Phasing: P5e-1 msum relabeling + rotation identity; P5e-2 the Vee-form identity +
interior dispatch; P5e-3 OrderedStep + step_mono + the chain corollary.

**The chain corollary (final assembly, exact shape):**
`OrderedStep` = an inductive mirroring `Step` whose merge constructor carries the
hubward side condition (donor's structural degree ≤ absorber's) — with
`OrderedStep.toStep` so P2b's termination/fixed-n/preservation lift.  `StateOK s` :=
`Balanced s ∧ Capped s`; preservation = `Step.balanced` + `Step.capped` via toStep.
Then:
* `step_mono : OrderedStep s s' → StateOK s → Aobj (backboneU s) ≤ Aobj (backboneU s')`
  (P5e-3c: inversion to `pre ++ a :: b :: post`, `Aobj_eq_AobjV` at the absorber via
  `List.reverseAux_eq`, one `vee_merge_le`);
* `chain_mono : Relation.ReflTransGen OrderedStep s t → StateOK s →
     Aobj (backboneU s) ≤ Aobj (backboneU t)` — induction on the chain, threading
  StateOK by preservation (NOT the hypothesis-parameterized `Aobj_mono_chain`, whose
  unconditioned `hmono` is too strong to discharge; state the conditioned version
  directly);
* `chain_to_normalForm : StateOK s → ∃ t, ReflTransGen OrderedStep s t ∧
     (∀ u, ¬ OrderedStep t u) ∧ Aobj (backboneU s) ≤ Aobj (backboneU t)` — from
  `exists_normalForm`'s WF argument transplanted to OrderedStep (its termination is
  Step's via toStep) + chain_mono.
This closes the merge layer: every certified state rewrites, monotonically in the
objective, to an ordered-merge normal form.  Residuals unchanged (anti-hubward, (L)/(B),
R5/R6, stratum-(i) port).

## NEXT LAYER after the merge capstone: (L)/(B) normalization (gate pinned 2026-08-15)

The merge layer operates on the CERTIFIED family (Balanced {4,5}-arms, Capped >= 5-arm
hubs, enough load-5 borrow arms).  The (L)/(B) layer is the rewrite stage that brings
small structures INTO that family, and it needs its own design pass (a new
P2B-style doc) BEFORE any Lean.  Ground truth to survey at the gate:
* `legs.py` — R2 (legs -> cherries) rational inequalities, the proven leg-normalization;
* `kelmans_confluence.tex` def:rules — the (L) and (B) rules and their measure;
* `kelmans_env_rules.py` — the small-structure boundary (arms load <= 3, hubs with
  <= 4 arms and load 0, bare/low-load leaves = exactly what the 3/16 cap excludes);
* P2B_MERGE_DESIGN honest boundary — "(L)/(B) BEFORE topped-up merges touch a region";
* the campaign base design's flagged open item (b): fixed-n branch-replacement
  bookkeeping for (B) — the piece the stratification note says lives in the
  CLASSIFICATION step, not the rewrite (P2 addendum consequence 2).
Method: as always — survey Python certificates, validate every identity/inequality
numerically in exact rationals, THEN Lean against the validated statements, one
CI-gated file at a time.  conjecture1_proved=False.

## LAYER after (L)/(B): R5/R6 (gate pinned 2026-08-15)

Scope NOTE: the unified topped-up merge already DISSOLVED the classical R5/R6
mid-rewrite content (no rebalancing between merges, no stuck states — P2B design
consequences 1-2).  What remains for this gate, per R7_ARCHITECTURE and the ledger:
* R5's tie crux `(26/23)^11 < 621/64` is ALREADY machine-checked (ExactCruxes,
  consumed by the rhoB bridges) — the residual is wiring it to the single-hub
  END-STATE comparison (normal forms are single hubs; which single-hub state wins);
* R6 = the de-loading schedule: `gap_discharges.py` G5/G6 (four shedding lemmas,
  n0 = 421, de-loading schedule THEOREM at Python level) + `distribution.py`/`hub.py`
  — the normal-form hub de-loads to the 5-cherry-bundle star;
* the amortized-hub layer (`amortized_hub_bound` + g1 rational certificates, reviewed
  PASS) bounds pure-hub counts <= 15 — its Lean port map is G1_KERNEL_LEAN_DESIGN.md
  (log_le_sub_one_of_pos kernel + exp-Taylor constants + norm_num; 3-5 CI files).
Survey → validate → Lean, one gated file at a time.  conjecture1_proved=False.

## RATE-PORT GATE OPENED (2026-08-15, post R5/R6-green): the plan is COMPLETE

All four steps now have validated designs:
(1) pi = Z * R -- the linear-in-root-weight split IS `Matched_factor` (pinned);
(2) S <= 1 at a leaf root -- FREE via `Matched_dtCh_nonneg` + `Zopen_dt_pos`;
(3) R <= 4/3 -- one field_simp inequality;
(4) Z <= rhoB^n -- the raw-tree -> Branch seam has PRIOR ART: STEP4C_DESIGN.md
    (raw_amplitude_seam.py certificates S1/S2/V3/S3/limit ALL GREEN, ready-to-paste
    Lean statements mapped by the MR !68 fork session; the amplitude identity is
    finite and local -- no second limit) feeding the green `phi_le_one` +
    `exp_logPhi_mul_rhoB_pow`.
Construction order SHARPENED (2026-08-15, on inspection): `dtSub` ALREADY expands
cherries with litRealize's exact weights (a UTree 2-path child has udeg 2, weight
1/(2d), inner 1/2 -- and `dB (parse K) = udeg K` by arithmetic), so items (i)-(ii)
of STEP4C are NOT needed -- the green `exp_logPhi_mul_rhoB_pow` anchors directly.
Three files:
1. `R47Perm` -- Popen/Matched/Ztot/Zopen invariance under child-list permutation
   (List.Perm induction; swap = two-term leave-one-out ring);
2. `R47Parse` -- `parseB : UTree -> Branch` (countP cherry-children + parse the
   rest; termination via the filter-member sizeOf pattern), then the mutual
   value-equality induction `Ztot/Zopen (dtSub t) = Ztot/Zopen (litRealize
   (parseB t))` + `udeg t = dB (parseB t)` + `Vb (parseB t) = usize t`, using
   `List.filter_append_perm` to reorder cherries-first and R47Perm to transport;
3. `R47Rate` -- the leaf-rooted split `Aobj (node [K]) = A0 + A1`,
   `Ztot (dtSub (node [K])) = A0 + A1/2` (A0 = Ztot(dtSub K),
   A1 = Zopen(dtSub K)/udeg K), `A1 <= A0` (Zopen_le_Ztot_dt + udeg >= 1),
   R <= 4/3 by algebra, and `Z <= rhoB^n` via parse + exp_logPhi_mul_rhoB_pow +
   phi_le_one (exp(logPhi) <= 1) + Vb_parse:
   `pi_le_rate (K) : Aobj (UTree.node [K]) <= 4/3 * rhoB ^ usize (UTree.node [K])`
   -- every tree with >= 2 vertices via its leaf rooting; the rooting-choice seam
   stays at assembly (HypRatePort quantifies over a leaf rooting).

## FINAL LAYER: the stratum-(i) rate port (gate pinned 2026-08-15)

Ground truth: `rate_bound_fixed_n.py` — the four-step proof of
`pi(T) <= (4/3) rhoB^n` for EVERY tree: (1) the exact phantom-root identity
`pi(T) = Z(T^r) R(r)`; (2) `S <= 1` at a leaf root; (3) `R <= 4/3`; (4)
`Z <= rhoB^n` via `phi_le_one` + `exp_logPhi_mul_rhoB_pow` (both CI-green).
ALREADY-PINNED simplifications (R47_CAMPAIGN.md, mapped this session):
* the phantom-root weight `1/(d+1)` IS `dtSub`'s root convention, the true-root
  weight `1/d` is `dtRealize`'s — so (1) is the linear-in-root-weight comparison
  `Aobj t` vs `Ztot (dtSub t)` with the A0/A1 split ALREADY proven as
  `Matched_factor`;
* (2) is FREE: at a leaf root `S = z_c Zopen/Ztot <= 1` from `Matched_dtCh_nonneg`
  + `Zopen_dt_pos` — no matching-injection argument needed.
The one genuine seam: the raw-tree -> Branch parse
(`Ztot (dtSub t) = Ztot (litRealize (parse t))`, the cherry-folding direction —
BridgeStep2/STEP4C territory) feeding the Branch-model `phi_le_one`.  Payoff: the
campaign's objective is bounded by the certified rate for EVERY tree — the
stratum-(i) pillar under the whole R7' architecture.  After this: the R7' final
assembly + INDEPENDENT ADVERSARIAL REVIEW before any ledger change.
conjecture1_proved=False.

## TERMINAL GATE: the R7' final assembly (pinned 2026-08-15)

Compose the completed layers per R7_ARCHITECTURE's four stages into the honest
capstone.  The assembly's shape:
* stratum classification (rate < rhoB dies by the rate bound; rate = rhoB forces the
  hub-backbone family — the (L)/(B) layer's classification output);
* `chain_to_normalForm` walks any certified state to an ordered-merge normal form,
  monotonically in `per L/∏deg` (via `pi_utree` — the objective IS the real quantity);
* the normal-form characterization (single hub) + R5/R6 (de-loading to the 5-cherry
  star) + the near-star arithmetic theorem identify the end state;
* the capstone is stated CONDITIONALLY on whatever hypotheses remain unproven at
  assembly time, each NAMED — never asserted.  `conjecture1_status.py` is updated in
  the same commit, crediting exactly the machine-checked pieces.
THEN: dispatch an independent adversarial review (REVIEW_BRIEF pattern — statement/
definition-level audit, consumer/reduction spot-checks, `#print axioms`, the
`Prop := True` and unused-hypothesis traps from the 2026-08-09 audit).  Only a PASS
there can move `conjecture1_proved` — and only if NO named hypotheses remain, which
as of this writing is NOT the expectation: the assembly will be honest-conditional
first, closing hypothesis by hypothesis.

## PUBLICATION GATE: the paper write-up (pinned 2026-08-15; opens on review PASS)

A NEW paper FROM SCRATCH (not an edit of paper_laplacian_ratio_maximizer.tex — that
21pp document is the research log's companion; the new one is the result paper).
Operator's specification:
* full proof at appropriate depth; standard structure with a real INTRODUCTION
  (the 1984 Brualdi--Goldwasser problem, its history incl. the refuted Wu-Dong-Lai
  attempt, what is proven here and what remains), BACKGROUND (permanents of
  Laplacians, matching polynomials, the DEC/cavity picture, rho_B = (621/64)^{1/11}),
  and METHODS;
* METHODS must explicitly lay out the tech stack and the human-AI development
  process with Claude: the Python exact-rational validation layer (sympy/Fraction
  self-verifying modules, the 60/60-before-Lean discipline), the Lean 4 / Mathlib
  formalization (R3Cert, CI-only verification on GitLab runners, the no-sorry +
  no-Prop:=True + #print-axioms integrity gates), the generator pipeline for
  certificate tables, the adversarial review cadence (independent audits, the
  overclaim traps sprung and caught), and the honest-ledger protocol
  (conjecture1_status.py);
* STRUCTURED FOR FIGURES: standard dot-and-line tree drawings (TikZ) illustrating
  the proof's topology at each stage — the near-star tie family N(c,k) (c+k=5, the
  six Phi=1 gadgets), cherries/arms/hubs and the {4,5}-arm balanced family, the
  backbone-of-hubs stratum, the topped-up merge surgery (before/after with the
  borrow arrows), the Vee rooting and the one-step rotation across an edge, the
  edge-split matchings picture, and the de-loading path to the 5-cherry-bundle star;
  each key lemma section anchored to one figure;
* scope claims EXACTLY per the ledger at write-up time: machine-checked layers
  stated as such, named-conditional hypotheses displayed prominently, and the
  distinction between the Branch-model Phi<=1 theorem, the reduction layer, and the
  full Conjecture 1 kept explicit throughout.

## FIGURES GATE (pinned 2026-08-15; opens when the paper draft is done)

Produce the paper's figure set as standalone TikZ (dot-and-line trees: filled circles
for vertices, plain edges; loads drawn as literal cherry pairs, not annotations).
GENERATE the combinatorial ones programmatically from the validated Python harnesses
(a small tikz-emitter over the tuple-tree encoding) so every drawn tree IS an object
the certificates verified; hand-draw only the schematic overlays (borrow arrows,
rotation arcs, split shading).  The set, one per key-lemma section:
1. the six near-star ties N(c,k), c+k=5 (the Phi=1 variety);
2. cherry/arm/hub anatomy + the balanced {4,5}-arm family;
3. the backbone-of-hubs stratum (rate = rhoB shape);
4. the topped-up merge surgery, before/after, borrow arrows 5->4 and the donor
   landing as the [5]-arm;
5. the Vee rooting + one-step rotation across an edge (both rootings, the shared
   four component terms labelled);
6. the edge-split matchings picture (use-the-edge vs avoid-the-edge);
7. the de-loading path to the 5-cherry-bundle star (the R6 schedule);
8. the certificate-table heat/coverage schematic (36 cells x corners) — the one
   non-tree figure.
Captions carry the exact lemma names (directA0_cell, AobjV_shift, ...) so the paper
cross-links figures to machine-checked statements.

## OUTREACH GATE: contacting Brualdi & Goldwasser (pinned 2026-08-15)

Operator confirmed both problem-posers are active at their universities.  Decision:
appropriate IN PRINCIPLE (posers welcome serious progress; they are the strongest
adversarial reviewers for this problem), but GATED: only after (a) the internal chain
is green, (b) the dispatched independent review PASSES, (c) the paper draft exists
with its ledger-exact scope section.  The letter: exact claim boundary (machine-
checked vs conditional vs open), the CI-verifiable Lean artifact, an INVITATION TO
SCRUTINIZE — not a request for endorsement.  Restraint is the letter's strength.
EXCEPTION (allowed earlier, operator's call): a short factual inquiry about the 1984
formulation's intent or prior unpublished partial results — an inquiry, not an
announcement.  Drafted by Claude at the gate; sent by the operator.

## The anti-hubward direction (designed 2026-08-15 — NO new certificates needed)

When the donor's degree exceeds the absorber's (`db > da`), reverse the ROLES: the
larger hub absorbs the smaller (the Python dichotomy's rule).  With the rotation
machinery this needs nothing new:
* the MIRROR move on the encoding: `(a :: b :: rest) → (mergedAtB :: rest)` where b
  absorbs a — a's load tops up to 5 via `k' = 5 - cA` borrows from a's OWN arms
  (`armsA ~ replicate k' 5 ++ othersA`), and the merged hub keeps b's load `cb`;
* its monotonicity: root at b (`Aobj_eq_AobjV` with `pre = [a]` — the donor sits in
  the UP position), and the Vee identities apply with the roles swapped
  (`(dA, dB) := (deg_b, deg_a)`, σ-slots exchanged) — the dressed lemma is agnostic
  to which ts-block the donor occupies, so the SAME 36-cell table discharges the
  comparison at the swapped instantiation (ordering hypothesis `deg_a ≤ deg_b` now
  points the satisfiable way);
* consequence: EVERY adjacent hub pair admits a certified monotone merge (absorb into
  the larger; ties either way) — S5 closes entirely and the no-stuck-states property
  holds on the certified family without the ordering as a residual.
Phasing: after the corollary — (i) the mirror constructor + toStep lift; (ii) the
donor-in-up Vee instantiation (validate numerically first, same 60/60 harness);
(iii) the swapped dispatch (generator emits it); (iv) fold into OrderedStep/step_mono.
STATUS: (i) DONE (R47OrderedStep, both directions + lifted P2b layer); mirror
validated 59/59 exact + monotone.

## R47VeeId construction notes (pinned 2026-08-15)

* `qSum_append : qSum (l1 ++ l2) = qSum l1 + qSum l2` (simp [qSum]).
* Vee-before derivations reuse the HeadId haves verbatim (the donor block is
  unchanged); the endgame reuses `twohub_scalar` via an `hshape : LHS = (scalar-LHS
  instantiated) := by ring` bridge — ring reassociates the extra up-product into the
  PA slot and the up-cavity into the SA slot (the division subterm is a ring-atom, so
  pure reassociation suffices; no new scalar lemma).
* MIRROR-BEFORE: root at the absorber b — the donor sits in `ts = tailU rest ++
  [backboneU [(armsA,cA)]]`; the donor-expansion haves are the hZtB pattern with
  `rest := []`.
* MIRROR-AFTER is FREE: the merged state is head-form, so `Aobj_head_after` applies
  with roles renamed; its afterD instantiation differs from the mirror's only in the
  (sQ, sr) PARTITION of the same sum and the (da, db) split of the same total —
  `afterD` depends only on `da + db - 1` and `sQ + sr`, so a small
  `afterD_sum_invariance` ring lemma transports it.

Honest ledger: after P5, the remaining reduction gaps are the (L)/(B) normalization
layer (small structures), R5/R6 de-loading/rebalancing, and the stratum-(i) rate port —
per R7_ARCHITECTURE.  conjecture1_proved=False throughout.
