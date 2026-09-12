# BG salvage: broadened capstone to a multi-hub cherry-backbone tie family

**Date:** 2026-09-11  **Branch:** `bg/hnorm-multi-reformulation`  **Status:** `conjecture1_proved = False`.

## Context

`R47HnormFalse52.r47_hnorm_false_at_52` refuted the single-hub `Hnorm` at aligned n=52 (see
`BG_HNORM_REFUTATION_2026-09-11.md`). This file salvages the reduction framework by broadening the
normal-form class from *Balanced+Capped single hub* to *arbitrary multi-hub cherry-backbone*, under
which the refutation dissolves. The sole remaining obligation becomes the tree->backbone straightening
= the open Brualdi-Goldwasser structural core.

## The true maximizer family (exact, `proof/verification/bg_maximizer_family.py`)

`Aobj = per(L)/prod(deg)` via a monomer-dimer tree-DP (self-checked `aobj == brute` matching enumeration).
Exhaustive for n<=14; multi-start SPR hill-climb for larger aligned n.

| n | Aobj | hubs | hub degrees |
|---|---|---|---|
| 7-14 | -- | 1-2 | cherry-spider / two-hub (matches repo n<=20 exhaustive) |
| 46 | 13170.84 | 4 | [9,6,6,6] |
| 52 | 45108.55 | 4 | [10,7,7,6] |
| 55 | 83738.62 | 5 | [10,6,6,6,5] |
| 56 | 102559.69 | 6 | [10,5,5,5,5,5] |
| 58 | 154846.88 | 6 | [10,6,5,5,5,5] |
| 67 | 986784.05 | 7 | [11,6,5,5,5,5,5] |
| 68 | 1215947.47 | 6 | [11,6,6,6,6,6] |
| 78 | 9507246.95 | 8 | [12,6,6,5,5,5,5,5] |
| 84 | 32758844.91 | 8 | [13,6,6,6,6,5,5,5] |
| 90 | 112911671.03 | 8 | [13,6,6,6,6,6,6,6] |

**The maximizer is always a multi-hub cherry-backbone** -- a path of cherry-loaded hubs, body hubs of
degree ~5-6 plus one larger head hub (degree ~n/7), hub count growing ~linearly. This is `backboneU` of a
multi-hub state -- the repo's own encoding -- not a single hub.

## The reformulation (`proof/formalization/R3Cert/R47HnormMulti.lean`, kernel-clean)

Broaden the class; the tie becomes the per-size multi-hub backbone argmax:

- `conjecture1_of_HnormMulti (tie)` -- the `Balanced+Capped`-free analogue of
  `conjecture1_of_layers_fixedN`: `HnormMulti + HdomMulti => forall t, Aobj t <= Aobj (tie (usize t))`.
  - `HnormMulti : forall t, exists s : List Hub, stateSize s = usize t /\ Aobj t <= Aobj (backboneU s)`
    (the tree->backbone straightening -- drops `Balanced /\ Capped`).
  - `HdomMulti : forall s, Aobj (backboneU s) <= Aobj (tie (stateSize s))` (tie dominates every backbone
    of its size -- tautological for the multi-hub argmax, analogous to `tieArgmax`/`tie_ge_of_mem`; a
    hypothesis here, dischargeable by a finite multi-hub argmax construction).
- `hnormMulti_of_hnorm` -- `HnormMulti` is a strict WEAKENING of the single-hub `Hnorm`, so broadening
  loses nothing that was provable.
- `hnormMulti_holds_at_T52` -- **the refutation dissolves**: `T52 = backboneU [([],6),([],6),([],6),([],6)]`
  witnesses its OWN `HnormMulti` clause (take `s` = its four-core hub-state; `Aobj T52 <= Aobj T52`).
- `singleHub_refuted_but_multiHub_open` -- pairs both facts: no Balanced+Capped state of size 52 dominates
  `T52` (single-hub target unprovable), yet `T52` satisfies the multi-hub clause.

All axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`. Wired into `AxiomGuard.lean` +
`proof-lean.yml`.

## `HnormMulti` is discharged by the pre-existing `hwh` -- and `hwh` was NOT refuted

**Clarification / correction of framing.**  `hnorm_of_wholehub` (R47CoverRelation.lean:114) already reduces
the whole-hub obligation `hwh` to the GENERAL-backbone Hnorm (`exists s : List Hub, usize (backboneU s) =
usize t /\ ...`) -- with NO `Balanced /\ Capped`.  That is exactly `HnormMulti`.  So:

- `usize_backboneU_of_ne_nil`, `hnormMulti_of_wholehub` -- `hwh => HnormMulti` (realization seam +
  single-leaf edge case).
- `conjecture1_of_HnormMulti_of_wholehub` -- `hwh + HdomMulti => forall t, Aobj t <= Aobj (tie (usize t))`.

Consequently the n=52 refutation did **not** kill `hwh`.  `hwh` feeds only the tree->general-backbone
straightening; what `r47_hnorm_false_at_52` refuted is the SEPARATE general->Balanced+Capped normalization
(the extra step the single-hub `tieArgmax` capstone needed): `T52` is a general backbone with no
Balanced+Capped dominator of its size.  Earlier phrasing that called `hwh` "false / unprovable" was
imprecise -- the refuted statement is the Balanced+Capped normalization, not `hwh`.  `hwh` (the original
"adaptive de-branch" object) survives as the sole open mathematical obligation for the salvaged capstone,
and is plausibly true (all n<=90 maximizers are backbones).

## Honest verdict

The FRAMEWORK salvages cleanly: broaden `Hnorm`'s target to multi-hub backbones, define the tie as the
multi-hub backbone argmax (making `HdomMulti` tautological), and the n=52 refutation no longer bites.  The
sole open mathematical obligation is `hwh` (= `HnormMulti`, the tree->backbone straightening), unrefuted.

There is no free lunch.  `HnormMulti`/`hwh` is equivalently the claim that the per-size `Aobj`-maximizer
over all trees IS a multi-hub cherry-backbone -- strongly supported by the data above (all n<=90), but it
is the open Brualdi-Goldwasser core (Pant 2026).  The refutation corrected the target and revived `hwh` as
the right obligation; it did not make BG tractable.  `conjecture1_proved = False` stands.

## Reproduce

```
python3 proof/verification/bg_maximizer_family.py 14     # exhaustive n<=14 + SPR for larger aligned n
cd proof/formalization && lake build R3Cert.R47HnormMulti
```
