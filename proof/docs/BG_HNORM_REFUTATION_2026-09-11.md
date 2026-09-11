# BG Hnorm / `hwh` REFUTED at aligned n=52 — exact multi-hub counterexample

**Date:** 2026-09-11  **Branch:** `bg/multihub-hnorm`  **Status:** `conjecture1_proved = False` (unchanged).

## Headline

`hwh` (the adaptive de-branch Aobj-monotonicity, `R47CoverRelation.lean:114-118`) — the sole remaining
open input to `Hnorm`, which with the proven `Hdom` discharges the capstone
`conjecture1_of_layers_fixedN` (`R47TopCapstoneFixedN.lean:48`) — is **FALSE**. It cannot be proven
because the statement it feeds is false: there is an explicit tree whose `Aobj` strictly exceeds *every*
Balanced+Capped hub-state of its size, so no such state can dominate it.

**The counterexample (exact `fractions.Fraction`, root-invariant):**

```
T(6,6,6,6)  = 4 core vertices in a path, each carrying 6 length-2 pendant paths (cherries); n = 52 (aligned, >= 46).
Aobj(T(6,6,6,6)) = 1180837892027061 / 26306674688      ~= 44887.387
tieArgmax(52)    = 4695479375868117 / 104857600000      ~= 44779.581   (best Balanced+Capped hub-state, at (a,b,c)=(0,5,3))
Aobj(T) - tie    = +8862581903961897 / 82208358400000    ~= +107.806   (STRICTLY POSITIVE)
```

`T(6,6,6,6)` is NOT Balanced+Capped (each hub has 0 arms + 6 cherries; `Balanced` needs arms in {4,5},
`Capped` needs >= 5 arms, and `c <= 5` fails). By the min-hub-size bound (`capped_state_size_ge_46`,
`R47AlignedMinSize.lean`), every Balanced+Capped hub has size >= 46, so two hubs give size >= 92 > 52 —
hence the entire Balanced+Capped class at size 52 is EXACTLY the four single hubs
`(0,5,3),(1,4,2),(2,3,1),(3,2,0)` (the only solutions of `11a+9b+2c=51, a+b>=5, c<=5`), and `Hdom`
(`pairCollapse6` + `mhub_le_single_of_pairCollapse6`, `R47WPair6.lean:336`) guarantees `tieArgmax(52)` is
their max. `T(6,6,6,6)` beats that max. Therefore `Hnorm` (an unrestricted `forall t : UTree`,
`R47TieArgmax.lean:120`) is false at `t = T(6,6,6,6)`, and by modus tollens `hwh` is unprovable.

## Verification: 4 independent engines + adversarial skeptic (all exact `Fraction`)

Consensus **CONFIRMED**, skeptic **AIRTIGHT** (multi-agent workflow, 7 agents). All engines reproduce the
three rationals EXACTLY:

| Engine | Method | Result |
|---|---|---|
| **A** — repo Ztot cavity (ground truth) | self-contained verbatim port of `Ztot/Zopen/Popen/Matched` (CavityTree.lean:38-49) + `dtRealize/dtSub/dtChildren/udeg` (R47Tree.lean:33-57), NO repo imports (`_engineA_ztot_oracle.py`) | MATCH, T>tie |
| **B** — unrooted per(L)/prod(deg) | `perL_tree` matching-DP (reused) + from-scratch linear tree-DP, validated vs Ryser permanent (`_engineB_independent.py`) | MATCH, T>tie; **root-invariance confirmed** across all 52 rerootings |
| **C** — closed-form / broadened family | 4 independent routes incl. an explicit 4-core caterpillar-spine transfer-matrix (`_engineC_indep_verify.py`); arm atoms Ztot(armL5)=621/64, armL4=513/80, cherry=3/2 match `broadened_tie_family.py` | MATCH, T>tie |
| **D** — Balanced+Capped envelope | repo cavity + Lean predicate reconstruction (`indep_verify_engineD.py`) | MATCH; confirms class-at-52 = 4 single hubs, `T` outside class |

**Skeptic (all five failure modes CLOSED):**
- **Rooting** — repo `Aobj := Ztot(dtRealize t)` is root-dependent in general (R47Tree.lean:17 scope note;
  root-invariance in `R47RootInvariance.lean` is conditional), BUT the target concludes an UNRESTRICTED
  `forall t : UTree`, and `T(6,6,6,6)`'s Aobj is in fact identical under all 3 tested rootings — the
  counterexample survives every rooting; both sides use the same `Aobj`.
- **Size** — `usize(T)=52 = stateSize` of the tie hub; no off-by-one (`11a+9b+2c=n-1=51`).
- **Class** — min hub size 46 => no multi-hub Balanced+Capped state fits in 52; `hubTriples(52)` = exactly
  the 4 triples; argmax (0,5,3).
- **Aobj definition** — used the repo's OWN cavity engine on both sides, so the `phi11`-vs-classical
  distinction cannot flip the sign; near-star closed form `(26/23)(621/64)^K` matches at K=1,2,3.
- **Scoping** — `conjecture1_of_layers_fixedN`, `conjecture1_of_Hnorm`, and `Hnorm` are all unrestricted
  `forall t`; no `sorry`/`admit` in the load-bearing files. Refuting the conclusion refutes `Hnorm`.

## Characterization (the finding is broader than a single point)

- `T(6,6,6,6)` is not even the best caterpillar at n=52. The non-uniform legs `(5,7,7,5)` give
  `1507692271149/33554432 ~= 44932.73`; an SPR global search finds a 4-hub caterpillar (hub degrees
  10,7,7,6, mixed cherry + load-5 arms) `pi = 370829981399553/8220835840 ~= 45108.55` — the true (or
  near-true) n=52 maximizer, a mixed multi-hub caterpillar, NOT a single hub.
- **The winning set is NOT a finite window and NOT contiguous — it interleaves.** Multi-hub beats the
  best hub at n = 46,48,50,52,54,55,60,64,68,79,90,…; the single hub wins only when its cherry count hits
  the cap `c=5` with a favorable arm mix (n = 56, 58, 84). Sharpest clean transition: n=54 (multihub wins)
  -> n=56 (hub is a strict SPR local max, margin 0).
- **Novelty vs the repo:** `exhaustive_maximizer_check.py` is exhaustive only to n<=20; the broadened-tie
  work (`BG_BROADENED_TIE_FAMILY`, `BG_TIE_CORRECTION_RELAY`) is hub-vs-hub only. No prior repo artifact
  exhibits a non-hub tree beating the best Balanced+Capped hub at an aligned n>=46. This counterexample
  lives squarely in the repo's unverified `n in (20, infty)` gap and is genuinely new.

## Architecture verdict

- **`Hnorm` (Balanced+Capped single-hub tree->hub normal form) is FALSE at aligned sizes** — densely and
  recurringly, not marginally. The tree->hub reduction (`StraightProgress_sized` / single-hub-domination
  chain) cannot hold as stated. This is exactly the "m>=3 multi-hub" obstruction the repo already flags as
  the open real-BG frontier — now with explicit exact refuting witnesses at aligned n, which the repo lacked.
- The single-hub `Hdom` lane (kernel-verified) is not wrong; it correctly characterizes the best *single
  hub*. It answers the wrong question at these n, because the global maximizer is not a single hub.
- **conjecture1 is salvageable only** by replacing the single-hub tie with a per-size **multi-hub
  caterpillar** tie family and proving multi-hub extremality — the m>=3 frontier with no Positivstellensatz
  cert. The current normal form is fundamentally inadequate at aligned n. `conjecture1_proved = False` stands.

## Next: kernel-checked formalization

`proof/formalization/R3Cert/R47HnormFalse52.lean` (in progress): `r47_hnorm_false_at_52` proving
`Not (exists s, Balanced s /\ Capped s /\ stateSize s = 52 /\ Aobj T52 <= Aobj (backboneU s))`, via
multi-hub exclusion (two hubs >= 92 > 52) + `singleHub_le_tieArgmax` + a `tieArgmax_52_lt_T52` enumeration
over the 4 feasible triples (`hub_Aobj_eq` closed form) against the exact `aobj_T52_eq`. Hardest piece:
`aobj_T52_eq` — the 4-deep, 6-cherry-per-core backbone cavity value in closed rational form (no reusable
lemma for this tree shape). To be added to `AxiomGuard.lean` + `.github/workflows/proof-lean.yml`.

## Reproduce

```
# ground-truth oracle (self-contained, verbatim Lean port):
python3 proof/verification/_engineA_ztot_oracle.py
# independent engines:
python3 proof/verification/_engineB_independent.py
python3 proof/verification/_engineC_indep_verify.py
python3 telperion/scratch/indep_verify_engineD.py   # run from telperion/scratch
```
NOTE: `_verify52.py`'s `unrooted_Aobj(T)` call is exponential and hangs at n=52 — use `Aobj_node` / the
polynomial engines only.
