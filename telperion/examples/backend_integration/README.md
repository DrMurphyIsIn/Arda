# Telperion as a certificate backend for an LLM prover

This example shows how an LLM/RL theorem prover (Goedel-Prover-V2, Seed-Prover,
Kimina-Prover, ...) can call Telperion to **discharge a certificate-shaped
subgoal deterministically**, instead of sampling a tactic proof.

Every frontier prover as of 2026 runs a Lean-verifier-in-the-loop but has **no
deterministic certificate backend** (the niche the comparison in
`docs/COMPARISON_ALPHAPROOF_DEEPSEEK_PROVER_V2_2026-08-20.md` found still empty).
When such a prover's search reaches a goal of the shape `0 ≤ <expr>` — a
polynomial or rational inequality — it can hand that goal to Telperion:

- **sound by construction** — Telperion emits a certificate the Lean kernel
  re-checks; a wrong certificate is a compile error, never a false theorem;
- **deterministic** — same goal, same proof, no sampling budget;
- **cheap** — CPU-seconds on a laptop vs pass@N on a GPU cluster;
- **honest on failure** — a goal outside its shapes returns an exact triage
  (FALSE + rational counterexample / NOT_POLYA + hints), which is itself useful
  signal for the prover's search.

## The bridge protocol (`telperion.tactic`)

The integration seam is one JSON request/response call — see
`src/telperion/tactic.py::discharge` / `discharge_json`:

```json
request  = {"target": "(1 + u)/(u + 1) - 1/(u + 2)", "symbols": "u", "aux_name": "tel_aux_1"}
response = {
  "proved": true,
  "verdict": "PROVED",
  "aux_lemma": "theorem tel_aux_1 (u : ℝ) (hu : 0 ≤ u) : 0 ≤ … := by …",
  "emitter": "DirectPolyaEmitter",
  "over_all_reals": false,
  "counterexample": null,
  "hints": [],
  "detail": "certified and emitted via DirectPolyaEmitter"
}
```

`over_all_reals` tells the frontend the binder shape of `aux_lemma`:

- `false` — a Pólya lemma `theorem … (x : ℝ) (hx : 0 ≤ x) : 0 ≤ …`; apply it as
  `tel_aux_1 x hx` (pass the nonnegativity hypotheses in scope);
- `true` — an SOS lemma `theorem … : ∀ x : ℝ, 0 ≤ …`; apply it as `tel_aux_1 x`
  (the stronger over-all-reals claim needs no hypothesis).

## The Lean frontend (`Telperion/Backend.lean`)

`Backend.lean` sketches a `telperion_discharge` tactic that:

1. reflects the current goal `0 ≤ e` into a `target` string + symbol list,
2. shells out to `telperion prove` / the bridge (or an MCP tool call),
3. splices the returned `aux_lemma` and closes the goal by applying it.

Step 1 (goal reflection) and step 3 (splicing) are Lean metaprogramming; this
file is the **cloud-verified frontend** — it needs a Lean+Mathlib toolchain to
compile (this repo builds Lean only in CI, never locally). The Python bridge it
calls is fully unit-tested (`tests/test_tactic_bridge.py`).

## Measuring the lift

`src/telperion/backend_lift.py` is the harness that quantifies what this backend
adds: run the prover alone over a suite of certificate-shaped goals, then
prover + `discharge`, and diff the solved sets (`lift_report`). The prover side
is a pluggable name-set seam (a stub in tests; a real Goedel-Prover-V2 run in a
cloud session). The published lift number is the cloud deliverable; the harness,
protocol, and Lean scaffold are done and tested here.
