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
naive attack. `conjecture1_proved = False` — and stays there until the whole chain builds sorry-free.

## Phase 2 — the open core, attacked (multi-agent, independently verified)

**The extremal, characterized (C1/Front2):** the rooted-`Ztot_sub` extremal is the **single 5-cherry hub**
`node[cherry×5]` (n=11), `Ztot_sub = 621/64`, rate `rhoB=(621/64)^{1/11}` EXACTLY via **`(3/2)^5·(23/18) = 621/64`**
— the SAME `27·23=621` identity as the subaction ceiling's `tie_identity_d6`. `g(a)=log Z(a)/(2a+1)` strictly
unimodal, argmax **a=5** (the a≈7 was the caterpillar-*family* internal peak, a dominated family).

**The sign-lever (C3/Front1):** the Aobj-increasing straightening move = **cherry-forming = R1 itself**
(`f2_increment_identity` + `aobj_flp_context_lift_crest`, already kernel-proven `≥0`); arm-balancing/leg-splitting
strictly worse.

**The single-SPR obstruction — RESOLVED (C3/Front1, `BGSCLJointDescent2Step.lean`):** the maximally-symmetric
triple-3-star (`tripleStar`, `Aobj=49/8`, `strDefect=1`, n=13) has NO single-SPR move that is both strDefect-down
and Aobj-up (independently re-confirmed: 132 SPR moves, 0 joint witnesses). BUT it DOES admit a
`StraightStep_sized` witness — the *actual* Hnorm move (`R47R7Sized`: `usize= ∧ Aobj≤ ∧ strDefect<`, more
permissive than one SPR relocation): `straightStep_tripleStar_witness : StraightStep_sized tripleStar
cherrySpider6`, `cherrySpider6 = node[cherry×6]` (`Aobj=243/16`, `strDefect=0`). **So RealObligationA/joint-descent
must be stated at `StraightStep_sized` granularity, not single-SPR; the n=13 obstruction does not block the Lean
obligation.** (The general `StraightProgress_sized` ∀-obligation remains open — it is essentially maximizer
domination.)

**2-step de-risk (C3/Front1):** the correct existence formulation is `StraightProgress_sized` (any same-size
`t'`, non-strict Aobj). Where one keeps the descent inside the kernel-proven move family, a 2-step path
(Aobj-nondecrease detour → defect drop) covers **102/102** defective trees at n≤13, with the first step being
**cherry-forming (=R1) in 96%** — a positive de-risk of the correct formulation (no 2-step failure observed).

## Phase-2 HONEST-SCOPE GUARD — rooted `Ztot_sub` ≠ classical `Aobj` (independently verified)

Front2 surfaced, and I verified with the fast `Aobj_node` engine, a load-bearing distinction (confirming memory
`phi11_not_classical_bg_2026-08-29`): the **rooted `Ztot_sub`** (repo Φ¹¹, what the Lean rate bound
`Ztot_dtSub_le_rhoB_pow` bounds by `rhoB^n`) is a DIFFERENT quantity from the **classical `Aobj=per(L)/∏deg`**.
At the 5-cherry hub: `Ztot_sub=621/64` vs classical `Aobj=81/8`. The rates DIVERGE: rooted extremal → `rhoB=1.2295`;
classical spider → `ρ*≈1.2277` (Pant's classical-BG constant); cherry-caterpillars *decrease* → `√(3/2)=1.2247`.
The Lean `Aobj` is genuinely classical (root-invariant, engine self-checked), but the whole rate/tie machinery
(`rhoB`, `nearStarTie`, `SharpRateNF`) is anchored to the ROOTED `Ztot_sub` via `rooting_identity`
(`Aobj ≤ (d+1)/d·Ztot_sub ≤ (d+1)/d·rhoB^n`). **Consequence: closing the Lean rate layer gives a TRUE bound at the
rooted rate `rhoB`, NOT the tight classical BG maximizer (at `ρ*`, Pant OPEN). Do NOT overclaim closing classical
BG.** `conjecture1_proved = False`.

## Phase-2 characterization CONFIRMED against existing proven Lean (`R47ArmRate.lean`)

The campaign's empirical extremal finding (rooted rate maximized at arm-**load 5**, the `621 = 27·23` tie) is
**already formalized and kernel-proven, unconditionally** (`[propext, Classical.choice, Quot.sound]`):
- `armObj arms := armProd arms^11 / (621/64)^size` (the rate-normalized arm-block objective).
- `armObj_resize_up (j ≤ 4)` / `armObj_resize_dn (j ≥ 5)` — **unimodality, peak at load 5** (Front2's C2 target).
- `armObj_le_one : ∀ arms, armObj arms ≤ 1` — **the joint arm-block envelope, tight exactly when every arm is at
  load 5.** No arm-load configuration beats all-arms-at-5.

So the arm-block extremality is DONE, and this **sharpens the open frontier precisely**: the arm envelope covers
the ARM blocks; what remains for `SharpRateNF` is the **spine-rooting amplitude** — tightening the backbone
rooting factor from `(d+1)/d` (≤ 6/5) down to `(26/23)/rhoB ≈ 0.919` (the "a bad-rooting tree pays with low
`Ztot`" trade-off, Gap-1→Gap-2). That spine-rooting tightening + the general `StraightProgress_sized` (Hnorm) +
the classical maximizer at `ρ*` (Pant) are the residual — the arm piece is no longer part of it.
`conjecture1_proved = False`.

## The spine-rooting gap, characterized exactly (the open crux, located)

The proven `Aobj_backbone_le_rate` gives `Aobj(backbone) ≤ (6/5)·rhoB^n` via TWO loose steps: `(d+1)/d ≤ 6/5`
AND `Ztot(dtSub) ≤ rhoB^n`. The exact `rooting_identity` is `(d+1)·Ztot(dtSub) = d·Aobj + Zopen`, i.e.

  **`Aobj = (d+1)/d · Ztot(dtSub) − Zopen/d`.**

The `(6/5)` bound simply **drops the `−Zopen/d` term** (`Zopen ≥ 0`). The sharp target `(26/23)/rhoB ≈ 0.919·rhoB^n`
(tight at the tie) therefore requires BOTH: (i) keeping the `−Zopen/d` subtraction (a genuine lower bound on
`Zopen(dtSub backbone)`), and (ii) the STRICT off-tie amplitude `Ztot(dtSub) < rhoB^n` for non-tie backbones
(Gap-1, of which `master_ineq_strict`/`bell < 0` off deg-6 gives the *qualitative* strictness but not the
*quantitative* margin), transported to `Aobj` (Gap-2). Even for the near-star tie itself the rooting factor
`(d+1)/d → 1` as `d→∞`, so the `0.919 < 1` amplitude comes irreducibly from `−Zopen/d` — there is no
rooting-factor-only improvement. **This is the genuine open Hdom crux (the rooting/Ztot trade-off); it is now
characterized to the exact term (`−Zopen/d` + the quantitative Gap-1 margin), not just named.** `conjecture1_proved = False`.

**A shortcut class RULED OUT (verified at the tie family).** Tested whether the crux reduces to a pure `Zopen`
lower bound — i.e. keep `−Zopen/d` but use the loose `Ztot ≤ rhoB^n`. It does NOT: at every near-star tie point
the naive bound `(d+1)/d·rhoB^n − Zopen/d` **overshoots** the sharp `(26/23)/rhoB·rhoB^n` (K=2: 126.6 vs 106.4),
because the off-tie near-star has a substantial STRICT `Ztot` margin (`rhoB^n − Ztot(dtSub) = 13.4` at K=2) that
the loose step discards. Meanwhile `Aobj = (26/23)/rhoB·rhoB^n` EXACTLY at every tie K (SharpRateNF is tight
there). **Conclusion: the sharp bound cannot be obtained from `Ztot ≤ rhoB^n` + any `Zopen` lower bound; it
irreducibly requires the QUANTITATIVE strict-off-tie amplitude `rhoB^n − Ztot(dtSub)` (Gap-1) — of which
`master_ineq_strict` (`bell < 0` off deg-6) currently gives only the qualitative sign, not the quantity.** That
quantitative amplitude margin is the irreducible open crux, now isolated with a class of reframings excluded.
`conjecture1_proved = False`.

## Cross-route reconciliation with the parallel Kelmans lane (2026-09-05) — same wall, two routes

The parallel session (tree->hub/Kelmans lane) landed `R47R7KelmansGenEnvCert.lean` (100 theorems, self-contained
`R3Cert.+` leaf, INDEPENDENTLY re-verified kernel-green here): the adjacent hubward Kelmans MERGE step is
`per(L)/prod-deg` non-decreasing for 25 of 30 load cells, ALL N, ALL m -- the multi-hub-stuck elimination for Hdom
(Phi bilinear in the marginal environment sums -> box corner -> Positivstellensatz nonneg witnesses via
`emit_nonneg_orthant`). Complementary to the SharpRateNF rate-bound route; it partially sidesteps the rate amplitude.

BOTH routes hit the SAME irreducible residual (independent triangulation): my SharpRateNF route verified that
box/Zopen-only reframing is INSUFFICIENT (quantitative strict off-tie amplitude Gap-1 irreducible); the Kelmans
route finds the 5 cb-heavy cells {(0,5),(1,4),(1,5),(2,5),(3,5)} NOT box-certifiable, needing the exact recursive
z_C*rho_C hub-mover. Same phenomenon: the tie-adjacent configurations resist box relaxation and require the exact
sharp treatment. My Gap-1 == their z_C*rho_C residual. conjecture1_proved = False.
