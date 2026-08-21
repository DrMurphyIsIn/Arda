/-
  Telperion backend tactic — cloud-verified frontend (needs Lean + Mathlib).

  `telperion_discharge` hands the current goal `0 ≤ e` to Telperion's
  deterministic certificate backend (`telperion.tactic.discharge`) and closes
  the goal with the returned auxiliary lemma.

  This file is a SCAFFOLD: the goal-reflection (step 1) and lemma-splice
  (step 3) are Lean metaprogramming that must compile against a pinned
  Lean+Mathlib (this repo builds Lean only in CI, never locally — see
  memory: "System crashes = SoC watchdog panics"). The Python bridge it drives
  is fully unit-tested in `tests/test_tactic_bridge.py`. Do NOT claim this
  compiles until CI is green; it is intentionally committed as the integration
  contract, not a finished tactic.
-/
import Mathlib
import Lean

open Lean Elab Tactic Meta

/-- Run the Telperion bridge on a serialized goal, returning the JSON response.
    In CI this shells to `telperion prove --json` (or an MCP tool); the exact
    transport is deployment-specific and stubbed here. -/
def telperionDischarge (targetExpr : String) (symbols : String) (auxName : String)
    : IO String := do
  -- e.g. IO.Process.run { cmd := "telperion", args := #["prove", targetExpr,
  --        "--symbols", symbols, "--name", auxName, "--json"] }
  -- The response is the JSON contract documented in the example README.
  throw (IO.userError "telperionDischarge: wire transport is deployment-specific")

/--
  `telperion_discharge` :
    1. reflect the goal `0 ≤ e` into (targetExpr, symbols),
    2. call `telperionDischarge`,
    3. on `proved`, splice `aux_lemma` and `exact`/`apply` it
       (with the `0 ≤ x` hypotheses when `over_all_reals = false`),
       else surface the FALSE/NOT_POLYA triage as a tactic error.

  Steps 1 and 3 are `elab`-level metaprogramming filled in against the pinned
  Mathlib; the goal here is to document the contract, not to hide the work.
-/
syntax (name := telperionDischargeTac) "telperion_discharge" : tactic

@[tactic telperionDischargeTac]
def evalTelperionDischarge : Tactic := fun _stx => do
  throwError "telperion_discharge: frontend scaffold — implement goal reflection \
    + splice against the pinned Mathlib, then verify in CI"
