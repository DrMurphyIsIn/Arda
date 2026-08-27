# Handoff — Hnorm/Hdom frontier: `{4,5}` arm-rate pinning (Step 1) + ordered attack

2026-08-27. For a parallel session to complete. `conjecture1_proved = False` throughout — nothing
here closes the conjecture; each step has a named honest boundary.

## Where we are (shipped this session)

The **balancing engine** is done and merged/queued:
- **#132 (MERGED, origin/main)** `R3Cert/R47R6BalanceTail.lean` — `Aobj_balance_le_tail` /
  `Aobj_transfer_le_tail` / `Aobj_balance_le_backbone`: balance the **top hub** of any multi-hub backbone.
- **#134 (OPEN PR, branch `feat/g7-hnorm-spinemono`, lean-verify GREEN, ready to merge)**
  `R3Cert/R47R6SpineMono.lean` — `Aobj_balance_le_deep` (balance the hub at **any** position),
  `spine_balance_pair`, `node_Ztot_child_mono` / `node_Zopen_child_mono` (child-replacement monotonicity),
  `hub_Ztot_balance_le` / `hub_Zopen_balance_le` (abstract-degree balance), `Ztot_node_snoc`. All axiom-clean.
- Work in worktree `~/repos/Arda-wt-hnorm` (tracks origin/main + #134). **Merge #134 first.**

Approved plan: `~/.claude/plans/whimsical-hatching-oasis.md`. Literature frame: Csikvári GTS poset
(path=min/star=max; per(L) is an immanant/Merris permanental polynomial), Heilmann–Lieb real-rootedness
⇒ log-concave arm profile, SOS→Lean pipeline (Telperion = such an engine).

## Step 1 — arm-rate unimodality (the exact spec; ~75% closable)

**New file `R3Cert/R47ArmRate.lean`**, re-instantiating `R47LegsRate.lean` on the arm-load axis `j`.

Arm value (`R47HubState.lean:86`): `A(j) := Ztot(dtSub(armU j)) = (3/2)^j·(1 + j/(3(j+1)))`  (rational).
Rate exponent (`R47StepSize.lean:67`): `usize(armU j) = 1+2j`; `rhoB^11 = 621/64` (`ExactCruxes.lean`).
Define `armRate(j) := A(j)/rhoB^(1+2j)`, so `armRate(j)^11 = A(j)^11 / (621/64)^(1+2j)` (rational — avoid rpow).

### CORRECTION to the plan (verified by exact rational computation)

The marginal peak is at **load 5, NOT `{4,5}`**. Exact facts:
- `A(5) = 621/64 = rhoB^11` **exactly** ⇒ `armRate(5) = 1`.
- `armRate(j)^11 = A(j)^11/(621/64)^(1+2j)` is **strictly unimodal, peak at j=5, value exactly 1**:
  `< 1` for all `j ≠ 5`. Sequence `armRate^11 − 1`: j0 −0.897, j1 −0.484, j2 −0.209, j3 −0.070,
  j4 −0.011, **j5 = 0**, j6 −0.017, j7 −0.049, …
- Successor ratio `r(j) := armRate(j+1)^11/armRate(j)^11 = (A(j+1)/A(j))^11/(621/64)^2`:
  r0 5.007, r1 1.533, r2 1.176, r3 1.063, **r4 1.0114 (>1)**, **r5 0.9835 (<1)**, r6 0.967, … → strictly
  increasing to 5, strictly decreasing after.

**Consequence:** `armRate(j) ≤ 1` is exactly `Ztot_dtSub_le_rhoB_pow (armU j)` — ALREADY PROVEN
(`R47RateZBound.lean:44`). So the genuinely-NEW deliverable is the **unimodality / monotone-resize**:
resizing an arm toward load 5 does not decrease the rate-normalized objective. This pins arms toward **5**,
not `{4,5}`. **`{4,5}` (allowing 4) is a JOINT/integrality effect** (fixed total size / coupling forces
some arms to 4) — a separate, harder argument. Step 1 delivers the marginal resize (peak-5); flag the
`{4,5}` joint pinning as the open follow-on.

### Lemmas to write (mirror `R47LegsRate.lean`)

1. `armRate_succ_up (j) (h : j ≤ 4) : A(j)^11 · (621/64)^2 < A(j+1)^11`  — the r(j)>1 climb; finite,
   `interval_cases j <;> norm_num [A]`. (Equivalently `armRate(j) < armRate(j+1)` for j<5.)
2. `armRate_succ_dn (j) (h : 5 ≤ j) : A(j+1)^11 ≤ A(j)^11 · (621/64)^2`  — the r(j)<1 tail. This is the
   `armBase_rate_tail` analog (`R47LegsRate.lean` tail): `(A(j+1)/A(j))^11 = (3/2)^11·(abRratio)^11` and
   `(3/2)^11/(621/64)^2 = Romval < 1` (`Sweep.lean:111`); the `abR`-ratio `(4j+7)/(3j+6) · (3j+3)/(4j+3)`
   tends to 1 from above, so a single telescoping/Pólya bound closes `j ≥ 5`. Use `Nat.le_induction` like
   `tail_rat` (`R47LegsRate.lean:121`).
3. `armRate_unimodal : ∀ j, A(j)^11 · (621/64)^(11 − (1+2j))-style ≤ A(5)^11` — i.e. `armRate(j) ≤ armRate(5) = 1`
   — assemble climb+tail via the proven prelude `Telperion.unimodal_peak` (peak `sstar = 5`, `s0 = 0`).
   (Or state directly as the monotone-resize toward 5.)
4. **Lift to `armProd`** (the useful move): `usizeList` is additive, so `armRate` is multiplicative across
   arms; combine per-arm resize with the merged `node_Ztot_child_mono` (#134) to get: resizing any single
   arm toward 5 does not decrease the rate-normalized hub objective. Honest boundary: marginal (coupling
   fixed), not joint.

**Template to copy:** `R47LegsRate.lean` — `armBase`(:42), `armBase_lt`(:48), `armBase_pow11_le`(:93),
`beta11_lt`(:112, `(483/400)^11 < 621/64` by norm_num), `tail_rat`(:121, Nat.le_induction),
`legs_rate_ge3`(:157, `interval_cases … <;> norm_num`). The arm story is the SAME shape on a simpler axis.

## Step 2 — Telperion emitter (instantiate `unimodal_max_family`)

`laplacian_ratio/armrate_resize_family.py`: thin instance of `unimodal_max_family`
(`telperion/src/telperion/emit_unimodal.py:183`; proven prelude `Telperion.unimodal_peak` at `:50`).
Emits `_dec` (Pólya, `by positivity`), `_cross_hi`/`_cross_lo` (`by norm_num`) for the successor-ratio
`r(j)` with peak `sstar=5`. Mirror the merged `stardom_template_family.py` emit workflow. These leaves
feed Step 1's `armRate_unimodal`. Reusable for Steps 3–4 rational leaves.

## Steps 3–4 (lower probability; honest)

- **Capped ≥5 arms (~55%)**: extend `sum_zw_arms_ge_floor` (`R47Capped.lean:100`) to a rate-normalized
  split/merge floor across `cb∈0..5` (per-cell norm_num, Telperion-emittable). Residual = merge-
  applicability classification (structural, `R47Capped.lean:21`).
- **Hdom (~40%)**: merge layer DONE (`step_mono`, `chain_to_normalForm`, `vee_merge_le` green). **VERIFIED
  OBSTRUCTION**: `normalForm_is_single_hub` is FALSE — a Balanced+Capped 2-hub state with both hubs
  all-load-4 and `c=0` is OrderedStep-stuck (`merge`/`mergeRev` `hsplit` needs `(5−c)` load-5 arms; none
  exist). So the normal form is a multi-hub `{4,5}`-caterpillar; Hdom must compare THAT to the tie.
- **Tree→hub via GTS (~10%, multi-paper-open)**: root-invariance ALGEBRA done (`R47RootInvariance.lean`,
  `Aobj_root_invariant` takes the transport `Equiv` as a typed hyp). Open = the combinatorial GTS
  induction (every tree → hub-backbone by GTS moves, each move's Aobj-effect = Kelmans corner Pólya certs
  `R47R4Kelmans*Cert`, well-founded termination) + the canonical-rooting transport `Equiv`
  (`R47RootInvariance.lean:34-41` named-open seam). Do NOT promise closure.

## Verification per step

`lake build R3Cert.R47ArmRate`; `#print axioms armRate_unimodal` clean `[propext, Classical.choice,
Quot.sound]`; PR off origin/main (fresh branch), proof-lean.yml green. Warm-prime a worktree by
`cp -r .lake` from a built one. FOOTGUN: local `origin/main` ref goes stale fast (parallel merges) —
always `git fetch` + rebase onto real origin/main before a PR; fresh branch per PR.
