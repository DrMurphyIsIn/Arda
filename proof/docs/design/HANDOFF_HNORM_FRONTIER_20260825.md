# Handoff — `Hnorm` frontier after the single-hub balancing line (2026-08-25)

**For parallel sessions.** This maps exactly what is DONE, what is MECHANICAL/tractable, and
what is RESEARCH-OPEN toward the `Hnorm` layer of `conjecture1_of_layers`, so you don't
re-derive it or accidentally try to `sorry` the hard core (CI now rejects that — see #119).

## The target

`R3Cert/R47TopCapstone.lean:29` `conjecture1_of_layers` is conditional on two open Props:

```
Hnorm : ∀ t : UTree, ∃ s : List Hub, Balanced s ∧ Capped s ∧ Aobj t ≤ Aobj (backboneU s)
Hdom  : ∀ s, Balanced s → Capped s → (∀ u, ¬ OrderedStep s u) → Aobj (backboneU s) ≤ Aobj tieU
```

with (all in `R3Cert.Step3`):
- `Balanced s := ∀ h ∈ s, BalancedArms h.1 ∧ h.2 ≤ 5`  (`R47Step.lean:45`)
- `BalancedArms arms := ∀ j ∈ arms, j = 4 ∨ j = 5`     (`R47Step.lean:41`) — arms pinned to **{4,5}**
- `Capped s := ∀ h ∈ s, 5 ≤ h.1.length`               (`R47Capped.lean:39`) — **≥5 arms per hub**
- `Aobj t = per(L(realize t))/∏deg` via `pi_utree` (`R47Tree.lean:158`)

## What landed this session (all merged to main, kernel-clean, no sorry)

The **single-hub within-one balancing line** (PRs #120,#123,#124,#125,#126,#127 + this
link module):

- `R47R6BalanceInduction.lean` — `BalanceStep` (first-two-arms transfer) + `Aobj_balanceStar_le`.
- `R47ArmPerm.lean` — `Aobj_node_perm`, `Aobj_backbone_arm_perm` (arm-permutation invariance of `Aobj`).
- `R47R6TransferArb.lean` — `TransferStep` (arbitrary-pair transfer, up to arm reordering) +
  `Aobj_transferStep_le` + `Aobj_transferStar_le` (the monotone engine).
- `R47R6BalanceTermination.lean` — `sq_transfer_lt`, `balanceStep_measure_lt`, `balanceStep_wf`,
  `balanceStep_preserves_floor` (Σarm² termination + floor, for `BalanceStep`).
- `R47R6TransferProgress.lean` — `ArmBalanced arms := ∀ x y ∈ arms, x ≤ y+1` (within-1) +
  `transferStep_progress` (unbalanced all-arms≥3 hub ⇒ a `TransferStep` fires).
- `R47R6HnormSingleHub.lean` — `single_hub_Hnorm`: a single hub `[(arms,c)]` with all arms ≥3
  (regime `6 ≤ |arms|+c`) is `Aobj`-dominated by the SAME arms rebalanced to **within one**.
- `R47R6BalancedArmsLink.lean` (this handoff's PR) — `BalancedArms.armBalanced`
  ({4,5} ⇒ within-1), `BalancedArms.floor` ({4,5} ⇒ ≥3), `balancedArms_terminal`
  (capstone-`Balanced` single hubs are transfer-terminal).

## ⚠️ The gap between `single_hub_Hnorm` and `Hnorm` is large

`single_hub_Hnorm` produces `ArmBalanced` (**within-one at any level**), NOT `BalancedArms`
(**exactly {4,5}**). The converse `ArmBalanced ⇒ BalancedArms` is **FALSE** (within-one at
value 10 is `ArmBalanced` but not `{4,5}`). Four independent gaps remain:

### Classification (be honest; do NOT `sorry` category C)

| Sub-goal for `Hnorm` | Class | Notes |
|---|---|---|
| single-hub within-one balancing | **DONE** | this session |
| `BalancedArms ⇒ ArmBalanced` / terminal link | **DONE** | `R47R6BalancedArmsLink` |
| per-hub balancing inside a fixed-length `List Hub` | **B — mechanical** | transfer lemmas are hub-local; lift is glue given fixed hub count |
| pin arms to **{4,5}** (rate-optimality: why 5) | **C — research** | needs the arm-rate argument assembled into a monotone "resize toward 4/5" transform; certs exist only as isolated `norm_num` facts (`R47R6ArmRateCert`, spider crux `(377/250)¹¹<(621/64)²`) |
| establish **`Capped`** (≥5 arms) + hub cap (`h.2 ≤ 5`) | **C — research** | only preservation lemmas + isolated deload certs exist; no establishment transform |
| **arbitrary `UTree` → hub-state** domination | **C — research** | the R4/Kelmans reduction; NO theorem maps an arbitrary tree to `≤ Aobj(backboneU s)`. Hardest missing half. |
| **multi-hub → fewer-hub** extremality (R2) | **C — research / not formalizable** | docs (`MASTER_INEQUALITY.md`, `R7_ASSEMBLY_DESIGN.md`) flag OPEN, verified n≤13 only; tight master inequality `F(C) ≤ env★(μ_C)` is the obstruction. Lands mostly in `Hdom`. |

## Recommended next honest increments (category B, sorry-free)

1. **Per-hub lift**: generalize `single_hub_Hnorm` from `[(arms,c)]` to each hub of a
   `List Hub` independently (fixed hub count), producing a per-hub `ArmBalanced` state. The
   transfer machinery is hub-local, so this is mechanical. Does NOT need the {4,5} pinning.
2. Keep `ArmBalanced` vs `BalancedArms` strictly separated — don't conflate within-one with
   {4,5}. Any lemma claiming to reach `Balanced` must go through the (open) rate argument.

## Do NOT attempt to fake

The {4,5} pinning, `Capped` establishment, the `UTree`→hub reduction, and multi-hub
extremality are genuine open mathematics. Closing `Hnorm` (or `Hdom`) by asserting these is
fabrication and CI (#119 axiom guard + orphan guard + gating sorry-scan) will not stop a
VACUOUS-but-true statement — so the burden is on the author to keep `conjecture1_proved =
False` honest. The capstone deliberately keeps `Hnorm`/`Hdom` as explicit hypotheses for this
reason.

## Build/CI notes for parallel sessions

- Leaf certs must be root-imported into `R3Cert.lean` OR named in a `proof-lean.yml` build
  step, else the **orphan guard** (added #122) fails CI.
- The **axiom guard** (`AxiomGuard.lean`, #119) runs `#print axioms` on the anchor theorems;
  a hidden `sorry` surfaces as `sorryAx` and fails the build.
- Warm-build a fresh worktree by `cp -r .lake` from a built worktree (mathlib `cache get`
  ≈ 38s decompress; olean path = `.lake/build/lib/lean/`).
- `main` requires unrelated status checks (`unit (sympy)`, `toy-compiles`, …) that never run
  on `proof/formalization/**`; `enforce_admins=false`, so merge proof PRs with
  `gh pr merge --merge --admin`.
