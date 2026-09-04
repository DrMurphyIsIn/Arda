# BG conjecture1 — the RealObligationA (Hnorm) frontier, mapped (2026-09-04)

**Status: research note picking up the interrupted `a3` Phase-0 investigation of `RealObligationA`.
No new Lean; a precise empirical map of the frontier + the durable positive certificate `a3` found.
`conjecture1_proved = False`.** Branch `bg/conjecture1-attack`.

## Where this sits in the conjecture1 reduction

Wave-2 (`d57be40`) reduced conjecture1 to **Hnorm + SharpRateNF + the re-rooting iso**. Hnorm — every
tree's `Aobj` is ≤ that of a straightened (Balanced+Capped hub) form — is discharged by a straightening
descent whose per-step obligation is `RealObligationA` (`R3Cert/BGSCLObligationA.lean`):

```
RealObligationA (f : UTree → UTree) : Prop :=
  ∀ t, strDefect t ≠ 0 → usize (f t) = usize t ∧ strDefect (f t) < strDefect t ∧ Aobj t ≤ Aobj (f t)
```

i.e. a size-preserving move that strictly lowers the (root-fixed) straightening defect `strDefect`
without lowering the objective `Aobj = per(L)/∏deg`. The earlier `pushInto`/debranch encoding was
**kernel-REFUTED** (`deephub_obligationA_false`, `direct_obligationA_false`): it CONCENTRATES degree, and
`Aobj` is maximized *toward the path* (degree-equalizing raises `Aobj`, concentrating lowers it). So the
real move is degree-EQUALIZING.

## What `a3` established (recovered from `telperion/scratch/a3_*.py`)

1. **Existence / well-posedness — 100% (n ≤ 12).** Every genuine tree (root-fixed `strDefect > 0`; 19099
   of them) has SOME SPR relocation that is both `strDefect`-down and `Aobj`-non-decreasing
   (`a3_wellposed.py`). So `RealObligationA` is not vacuous — a witness move always exists.
2. **`debranchLocal` (deterministic) is insufficient — 26%** (4978/19099). Confirmed dead as a universal
   move (it is the concentrating direction).
3. **The single-leaf "higher→lower degree" move is NOT unconditionally `Aobj`-up.** It goes *negative* at
   small degree gaps (`a3_singleleaf.py`: gap `du−dv=1` → 4512 negatives; worst `du=3,dv=2`). Only large
   gaps (≥6) are reliably positive. So "move a leaf to any lower-degree vertex" fails.
4. **POSITIVE, DURABLE: the leaf-onto-leaf PATH-EXTENSION move is unconditionally `Aobj`-up.** Moving a
   pendant leaf onto another leaf (`a3_leafmove.py`, `B_is_leaf=True`): **30000 tests, 0 negatives**, with
   the exact closed form (`a3_F2_closed.py`, verified vs the exact cavity engine on 2000 blocks):

   ```
   ΔAobj = P · (n² + n·Q + 4·Q) / (2(n+1)(n+2)),   with  P, Q, n ≥ 0   ⟹   ΔAobj ≥ 0.
   ```

   `P = ∏ Ztot(child)` (>0), `Q` a `qSum` term (≥0), `n` a child count (≥0). This is a **clean, Lean-ready
   rational-positivity certificate** (`n² + nQ + 4Q ≥ 0`) — the load-bearing positive result.

## What this session (`a4`) added — the frontier is precisely located

`a4_pathext_covers.py`, `a4_miss_move.py` (exact, n ≤ 12/11):

5. **Leaf-path-extension straightens 93%** (17773/19099): for these, a leaf-path-extension is BOTH
   `strDefect`-down AND `Aobj`-up (the `Aobj` clause free from the F2 certificate #4).
6. **The 7% it misses are SYMMETRIC MULTI-HUB trees** — e.g. `node[node[l,l,l], node[l,l,l]]`
   (`strDefect = 1`): the two equal hubs cannot be straightened by relocating a single leaf (any leaf move
   leaves two non-piece children at the root, `strDefect` unchanged). 1326 such trees at n ≤ 12.
7. **The misses' winning move is a WHOLE-HUB relocation** (`a4_miss_move.py`, all 177 misses at n≤11 are
   well-posed): moved-subtree size **2–6, mostly non-piece (a sub-hub)**, regrafted onto a strictly-lower
   degree vertex. This second family does NOT enjoy the single-parameter F2 certificate (whole-subtree
   moves onto leaves DO have negatives — `a3_leafmove.py` `B_is_leaf=False`: 598 neg), so it needs its own
   `Aobj`-monotonicity argument.

## The honest frontier (what remains for `RealObligationA`)

`RealObligationA` is **NOT** reducible to one clean move. It needs a case split:

- **Case A (leaf-path-extension, 93%):** `Aobj` clause = the F2 certificate `n²+nQ+4Q ≥ 0` (Lean-ready);
  `strDefect` clause = a finite combinatorial check that the extension removes a non-piece child.
- **Case B (symmetric multi-hub, 7%):** a whole-hub degree-equalizing relocation; the `Aobj`-monotonicity
  here is the genuine remaining analytic content (no closed-form certificate yet — the next target).

### Case B, stress-tested (`a5_caseB_candidates.py`, `a5b_kernel_gate_refutation.py`, exact n ≤ 11)

Tested deterministic Case-B move-rules against the 177 miss trees (n≤11). Result:
- **`R_greedy_aobj` (among strDefect-down moves, pick argmax `Aobj`) is UNIVERSAL — 177/177.** So a
  deterministic Case-B witness EXISTS, but it is a **search** (argmax), not a clean structural move.
- **Every simple structural rule is REFUTED**: `R_maxgap` 164/177, `R_hub_to_leaf` 171/177, `R_min_child`
  151/177 — each has miss trees where it DROPS `Aobj`. Concrete refutation for `R_maxgap`: at
  `((),(((((),),),),((((),),),)))` it moves `Aobj 901/96 → 1189/128` (down). **This refutation is
  kernel-gated** via the AXLE `negative_control` primitive (`a5b`): `assert_kernel_rejects` confirms the
  Lean kernel rejects the false monotonicity `901/96 ≤ 1189/128`, and the real drop `1189/128 < 901/96`
  verifies clean.

**Consequence for the Lean proof:** Case B must be discharged as an **EXISTENCE** statement — `∀ t` (Case-B
defective) `∃ move`, strDefect-down ∧ `Aobj`-non-decreasing — backed by the well-posedness lemma (#1), NOT
by proving a clean structural move (those are dead, now kernel-gated). The remaining analytic content is the
existence/well-posedness lemma itself. Do not spend effort proving `R_maxgap`/`R_hub_to_leaf` monotone.

Existence (#1) guarantees a witness always exists; a Lean proof can define `f` by a canonical search and
prove the two cases cover all defective trees. **Recommended next unit:** formalize Case A — emit the F2
rational-positivity atom via the (now-merged) Telperion `emit_transcendental_enclosure` / rational-cone
route, kernel-gate with `verify.py` + `negative_control.py`, and wire it as the `Aobj` clause of a
leaf-path-extension `straightStep`. Case B (the whole-hub move certificate) is the deeper residual.

## Files
- Investigation: `telperion/scratch/a3_*.py` (a3, interrupted), `telperion/scratch/a4_pathext_covers.py`,
  `a4_miss_move.py` (this session).
- Lean obligation: `R3Cert/BGSCLObligationA.lean` (`RealObligationA` Prop + the refutation witnesses).
- Reduction: `R3Cert/R47TopCapstone.lean` (`conjecture1_of_layers`), `R3Cert/BGSCLHnormPort.lean`.

Do NOT claim Hnorm or conjecture1 closed. `conjecture1_proved = False`.
