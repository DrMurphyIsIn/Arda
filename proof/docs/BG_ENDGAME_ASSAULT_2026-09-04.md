# BG conjecture1 endgame — multi-agent assault outcome (2026-09-04)

**Status: the endgame's TRACTABLE residuals are CLOSED and independently verified; the CORE is confirmed to be
Pant 2026's open interior-optimum, with every naive shortcut kernel-gate-refuted. `conjecture1_proved = False`.**
Branch `bg/conjecture1-attack`. Foundation: `bg_ceiling : ∀ b, bell b ≤ 0` is independently verified closed
(`telperion/docs/BG_CEILING_CLOSED_2026-09-04.md`, relay `BG_SESSION_RELAY_2026-09-04.md`).

The assault (plan `~/.claude/plans/quiet-singing-kahn.md`) ran Phase 0 (falsification gates) → Phase 1
(tractable Lean lemmas), both as multi-agent workflows, all outputs independently re-verified (lake build green,
AxiomGuard clean `[propext, Classical.choice, Quot.sound]`).

## Phase 0 — falsification gates (6 parallel exact-Python probes, n≤11–16)

| Gate | Verdict | Finding |
|---|---|---|
| G-R1 context-lift | **HOLDS** | 0/1,563,170 Aobj-decreases; child swap raises both `Ztot_sub`, `Zopen_sub` as udeg drops → Front 1 |
| G-R2 symmetric base | **HOLDS** | `Aobj(node[k*,k*]) = (4k+2)/(k+1)`, dAobj=0 → Front 2 |
| G-R3-gts coefficientwise | **REFUTED** | VDB-weighted `Z_k` vectors CROSS at n=6 (path `Z=(1,7/4,13/16,1/16)` vs star `(1,5/3,3/4,1/12)`); graded ladder dead |
| G-R3-perron uniform=rhoB | **REFUTED** | uniform cherry-caterpillar plateaus ~1.8e-3 BELOW `(621/64)^{1/11}`; extremal is a NON-uniform cherry-SPIDER; interior optimum a=7; cherry (length-2) arms essential; + a normalization mismatch to reconcile |
| G-R3-vdb Karamata-up | **REFUTED** | submodular weight `1/(d_ud_v)`: P4 path `5/2` → star `2` (drops 1/2). The Aobj-increasing direction is degree-EQUALIZING (Karamata-DOWN), matching the `a3_wellposed` SPR framing |
| G-R3-potential | **REFUTED** (single) / **HOLDS** (joint) | no monotone `Aobj↔strDefect` coupling (disagree 99.76%); BUT joint well-posedness holds **87062/87062** (∃ a strDefect↓ **and** Aobj↑ move); argmax-Aobj is always a strDefect=0 caterpillar/spider |

**Corrected probe** (degree-equalizing direction): 94% Aobj-nondecreasing; the 6% failures are interior-optimum
overshoots (`[4,3,2]→[3,3,3]`, Aobj `49/12→110/27`). **So NEITHER direction is monotone — the crux is
irreducibly the interior optimum.**

**Net:** every shortcut to the core (coefficientwise GTS, uniform Perron, monotone leaf-exchange either
direction, single potential) is REFUTED with a minimal exact counterexample (kernel-gate-ready). The core
reduces, with no surviving shortcut, to the **adaptive joint-descent existence lemma** = the interior-optimum
cherry-spider maximizer = **Pant 2026's open problem**.

## Phase 1 — tractable Lean lemmas CLOSED (multi-agent, independently verified)

**R1 — Case-A degree-changing Aobj context-lift** (`R3Cert/BGSCLRealOblACaseALift.lean`):
- `Aobj_child_replace_le_deg` — the GENERAL degree-CHANGING child-monotonicity (generalizes
  `node_Ztot_child_mono`'s equal-udeg restriction: udeg may drop while `Ztot_sub` AND `Zopen_sub` rise).
- `aobj_flp_context_lift_crest` — the CORRECT size-preserving context-lift (`node(leaf::leaf::crest)` →
  `node(stem::crest)`, any sibling context). **Closes Case A's residual.**
- `flp_context_lift_book_false` — an honest CORRECTION caught by independent verification: the Book's literal
  `Aobj_flp_context_lift` def was mis-stated (dropped the crest → a vertex), witness `node[node[leaf,leaf],leaf]`
  `Aobj=8/3 > node[stem,leaf]=5/2`. The crest form is the true statement.

**With R1, Case A (leaf-path-extension, 92% of defective trees) is analytically complete:** Aobj-increment
identity (`f2_increment_identity`) + root monotonicity (`f2_aobj_monotone`) + size (`usize_flp_move_eq`) +
piece-flip strDefect drop (`npCount_flp_flip`) + the embedded context-lift (`aobj_flp_context_lift_crest`).
Remaining for Case A is mechanical assembly (lift `npCount_flp_flip` to total `strDefect`, package the witness).

**R2 — Case-B symmetric base case** (`R3Cert/BGSCLRealOblBSymBase.lean`):
- `Aobj_before`/`Aobj_afterB` = `(4k+2)/(k+1)` exactly; `symmetric_star_neutral`/`symmetric_star_monotone`.
- **STRONGER (numeric):** the two-star straightening move is Aobj-INVARIANT for ALL (j,k) incl. j≠k (closed
  form `((2j+1)/(j+1))((2k+1)/(k+1))(1+½(1/(2j+1)+1/(2k+1)))`). **This move carries NO sign lever** — the core's
  sign-lever must come from a DIFFERENT move family (the cherry-arm structure, per G-R3-perron).

## Honest scope

CLOSED (kernel-verified, axiom-clean, AxiomGuard-guarded): R1, R2 — Case A's analytic core + context-lift, and
Case B's symmetric base. OPEN: the **Case-B asymmetric coupling ⊕ SharpRateNF near-encoding = the interior-
optimum cherry-spider maximizer** (Pant 2026). Phase 0 proved this is the irreducible crux and refuted every
naive attack. The full Phase-2 combinatorial assault (build `weighted_matching`/`vdb_exchange`/
`transfer_caterpillar`, attack the cherry-spider extremal) is a genuine research program, not a one-pass close.
`conjecture1_proved = False` — and stays there until the whole chain builds sorry-free.
