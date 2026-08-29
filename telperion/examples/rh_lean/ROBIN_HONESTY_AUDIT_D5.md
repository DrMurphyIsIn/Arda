# D5: honesty audit of the Robin -> RH program

Adversarial review of every artifact produced under the "extend Robin to RH" program, against
the one non-negotiable: **nothing here proves RH, approaches proving RH, or is evidence FOR RH.**
"Robin's inequality for all n >= 5041" IS the Riemann Hypothesis; a finite/partial/reduction
result is not a step toward it.

## Mechanical checks (all pass)

- **`conjecture1_proved` is never set True.** It appears only as `= False` in module docstrings.
- **No `sorry`, `native_decide`, or `admit` in any `RH/*.lean` module.** Every landed theorem is a
  genuine Lean-kernel proof through the `telperion-rh-lean` gate (the actual kernel arbiter, not the
  `|| true` probe sandbox).
- **Every kernel module docstring states its RH scope** ("proves nothing about RH" / "NOT itself
  RH-equivalent" / finite-instance). The three prose docs (D1 map, D2 triage, D3 reduction) each
  carry an explicit "does NOT prove RH" / "What this does not prove" section and the Wall.

## Per-artifact honesty ledger

| Artifact | What it is | Honest scope (audited) |
|---|---|---|
| `Robin.lean` (comfortable n) | `sigma(n) < e^gamma n loglog n`, n in {5041,5042,8192,65537} | Finite instances of an RH-EQUIVALENT inequality; a violator would disprove RH, but passing is only *consistency*, not evidence. |
| `Robin.lean` (13 SA numbers) | Same, for every superabundant n in (5040, 2e6] | Finite; the RH-tight regime, kernel-exact (vs Briggs/Morrill-Platt floating point). Still finite. |
| `RobinReduction.lean` | `robin_G_monotone` (least counterexample is SA) | A reduction LEMMA. Reduces "Robin at all n" to "Robin at abundancy records"; proves nothing itself. |
| `NicolasBridge.lean` | `phi(n) sigma(n) < n^2` at primorials 6,30,210 | UNCONDITIONALLY-true elementary connector (Nicolas => Robin); NOT itself RH-equivalent; finite instances. |
| `ROBIN_RH_MAP.md` (D1) | Source-grounded terrain map (46 theorems) | Explicit "does NOT prove" header + Wall + "consistent with, not evidence FOR" footer. |
| `ROBIN_FORMALIZATION_TRIAGE.md` (D2) | Lean-feasibility triage | "none of these formalizations prove RH"; not-now tier = the infinite CA tail (= RH). |
| `ROBIN_REDUCTION_D3.md` (D3) | Reduction scope note | States precisely what is NOT done (SA-completeness + the (5040,10080) boundary) and why none approaches RH. |

## Residual honest caveats (named, not hidden)

- The D1 map's cluster grounding was recovered from the research-workflow agent transcripts after a
  `pipeline` extraction bug discarded the deep-read outputs (the workflow's own auditor caught the
  resulting fabrication risk and refused to invent grounding; the 46 theorems are genuine agent
  deep-reads, not model-knowledge fallback). Citations should still be spot-checked against primaries
  before any external use.
- `NicolasBridge` proves the bridge at 3 small primorials only; `decide` hits max recursion by
  n=2310. The general theorem (all n) and the RH-EQUIVALENT Nicolas primorial inequality
  (`n/phi(n) < e^gamma loglog n`, needing the tight transcendental brackets) are scoped, not shipped.
- The tight SA certificates depend on Mathlib's `eulerMascheroniSeq`/`log_two_gt_d9`/`log_three_gt_d9`
  and the exact d9 constants; a wrong constant (`log 3` off by 1 ulp) was caught by the kernel, which
  is the point of gating on it.

## The one-line verdict

This program **maps and kernel-formalizes the KNOWN structure between Robin-type criteria and RH** --
a reduction lemma, finitely many tight superabundant checks, an equivalence bridge, and a sourced
terrain map with a precise statement of the Wall (controlling `G` on all colossally-abundant numbers
= RH, governed by the zeta zero-free region, with no known elementary bypass). It does **not** prove
RH, does not narrow the gap to it, and every artifact says so. `conjecture1_proved = False`.
