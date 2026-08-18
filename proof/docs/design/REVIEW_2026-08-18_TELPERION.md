# Independent review — end-to-end, Telperion verdict lens (2026-08-18)

Reviewed with the eight crux-campaign honesty patterns now shipped as Telperion
modules (`telperion/`): every component closed with one verdict from
`VALIDATED / OBSTRUCTED_AND_LOCATED / NULL / RE_DERIVATION`, exact-rational, no
floats at decision points. Method: three parallel stratum-reviewers + direct
crux inspection + independent re-verification of the exact cruxes with
Telperion's `decide` + the super-solution branching caveat run on the folded
potential. NOT run locally: the 20-40 min `verify.py` and `lake build` (the CI
`proof-lean` job owns the compile). `conjecture1_proved = False` — unchallenged.

## Verdicts by stratum

| Stratum | Verdict | Evidence |
|---|---|---|
| Φ≤1 crux (Lean) | **VALIDATED** | `phi_le_one` genuine unconditional term (`← deficitNonneg_holds ← deficitNonneg_of_star(StarBound)`); 0 `sorry`, 0 `axiom`, 0 `Prop:=True`; folded potential `(11/50)(y−T0)₊` by convexity; tie facts `64·243·23=621·576`, `3^317·2^81≤23^129` re-verified with `decide`. |
| Permanent–matching bridge | **VALIDATED** | `pi_litHub'`, `amplitude_bridge_real'` unconditional; acyclicity proved. |
| Faithfulness spine | **VALIDATED** (1 soft spot) | 3 permanent engines + `π(T(3,3,3))=19683/256`; 6/6 tests. Soft spot below. |
| Smooth-certificate route | **OBSTRUCTED_AND_LOCATED** (correctly refuted) | 19 no-go modules; continuous relaxation exceeds 1 at s*≈4.82 (+4.17e-5); `near_star_arithmetic_proof.proof_complete=True` in pure `Fraction`. The crux is arithmetic — consistent with `phi_le_one` being `decide`-closed. |
| No circularity | **VALIDATED** | One-directional dependency (rate→floors→hub-cap→dominations→merge→schedule→template); Lean consumes only `phi_le_one`+`BridgeStep4c`; concurs with REVIEW_2026-08-14 Check E. |
| Reduction layer (R47 / R7′) | **OBSTRUCTED_AND_LOCATED** | Honest-conditional; located frontier below. |
| Status ledger | **VALIDATED** | `conjecture1_status.py` calls its certificates; `conjecture1_proved=False` held. |

## Located frontier (why `conjecture1_proved=False` is accurate)

R7′ composes 10 named `Prop`s: 2 Lean-green (`HypMergeCapstone` =
`chain_to_normalForm`, terminating WF induction; `HypSchedule` lemmas), 8
unformalized — each with a named exact-Python artifact and a designed Lean path,
none axiomatic, none hidden. In ascending difficulty:

1. **`R47Rate.lean` absent — but MECHANICAL.** `R47Perm`/`R47Parse` green; the
   missing file is ~60–100 lines of ring algebra + 3 `le_trans` through green
   lemmas (`P5_SEAM_DESIGN`). Cheapest real gap.
2. **(L)/(B) classification seam** — arbitrary tree → `Balanced∧Capped`. Designed
   (`LB_LAYER_DESIGN`), zero Lean.
3. **Depth≥3 domination sliver** (`g34_deep.py`) — finite sampling + an unproven
   monotonicity; self-labeled the honest sampling sliver. (Two-hub 442,800-case +
   depth-2 star-of-hubs 972-cert are exact/symbolic and solid.)
4. **G1 floor hardening + amortized-hub cap** — critical family symbolic, mixed
   layer grid/float; `DELTA_AMORT=0.0235` survives on the true infimum with
   ~9e-5 margin (Amendment 2).

## Findings

Applied here (this commit):
- **Doc overclaim** — `R7_ARCHITECTURE.md` G3+G4 row said "Stage II … is CLOSED";
  its own Amendment 1 corrects it. Row now reads "REDUCED TO A NAMED G1 SLIVER".
- **Undocumented rigor limit** — the two-engine faithfulness guard uses
  `round(ryser_float)`, sound only while the float error < 0.5 (n<10 here). Noted
  in `test_lr.py`.

Corroborated, left to the owning session:
- **Amortized-hub terminology contradiction** — already logged as Amendment 2
  ("reconcile the status contradiction"); `slack_ledger_dichotomy.py`
  (CONJECTURAL, 0.08/hub) vs `amortized_hub_bound.py` (numeric-certificate
  rigor, 0.0235/hub). Needs the owner's reconciliation, not a reviewer's guess.
- **Soft float-at-decision spots** in `slack_ledger_dichotomy.py` /
  `g34_deep.py` — measurement/assessment layer only; the certificate layer
  (`g1_floor_certificates.py`) is fully exact; none gate `conjecture1_proved`.

Verified NOT a defect (already correct):
- `C_1` docstring — `rate_bound_fixed_n.py:9` already reads the correct
  `0.919446`; no `0.881` remains. (Verified before "fixing"; not touched.)

## Bottom line — review verdict: **VALIDATED**

The honest-conditional framing is faithful to the artifacts. The Φ≤1 crux is
genuinely machine-checked and unconditional; the reduction is a coherent
architecture with every gap named, located, and none hidden as `sorry`/axiom/
`Prop:=True`; there is no circularity; the faithfulness and no-go discipline is
load-bearing. Nothing here overturns a machine-checked claim. The cheapest
closable gap is `R47Rate.lean` (mechanical); the true frontier is the (L)/(B)
classification seam + the depth≥3 sampling sliver. `conjecture1_proved=False`
is the correct description of the current state.
