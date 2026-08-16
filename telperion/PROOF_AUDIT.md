# PROOF AUDIT — the Brualdi-Goldwasser campaign, by verification stratum

Generated 2026-08-16 by `examples/proof_audit/generate_audit.py`; executable rows were EXECUTED (frozen manifests read, exports recheck-verified live).  Do not edit; regenerate.

| stratum | method | state |
|---|---|---|
| Lean core: bridge + phi_le_one + merge layer + parse (90 R3Cert modules) | Lean kernel (origin CI) | KERNEL-CHECKED — origin pipeline 2762803858 @ b2996c79; reviewed PASS 2026-08-14/15 |
| G1Kernel + Real.log bridges + 103 hinge-dead classes | Lean kernel (origin CI) | KERNEL-CHECKED origin-side (parallel session; trio round in flight) |
| 36-cell unified merge table (HypStar seam) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 216 theorems frozen [5645431aded2]; sampled recheck GREEN (4 cell(s)) |
| G1 floors: dichotomy/tax/below-window + anchors (HypFloors) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 3260 theorems frozen [dc72d7c87c2f, 0ace82300c53]; sampled recheck GREEN (2 cell(s)) — COMPILE-GATED green @6758e88; handoff ACCEPTED (origin bf2f0747); 1 fragile cell tripwired ((2,0,1) @0.59 width) |
| R6 shedding lemmas (de-loading schedule) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 55 theorems frozen [022ea4f8feb5]; sampled recheck GREEN (2 cell(s)) |
| 972 star-of-hubs dominations (HypStarSymbolic) | Telperion re-derivation + stdlib recheck | IN FLIGHT — freeze not yet landed |
| Legs certificates (42) + 726-digit bignum | planned | PLANNED — origin Lean green (R47Legs); re-derivation next in queue |
| Interpolation lemma: sign dichotomy + 212 endpoint checks | planned | PLANNED — dichotomy glue + interval symbols ready; encoding queued |
| G34 residual sweep (442,800 cases) | planned | PLANNED — as interchange export + stdlib recheck (not per-theorem Lean) |
| Two-hub residual tails (per-residue comparators) | planned | PLANNED — witness API + varmap machinery ready; encoding queued |
| Hunt-attack sweep over all certified families | planned | PLANNED — three-mode adversarial minimization; queued |
| Structural inductions (telescoping, termination, acyclicity); R7' assembly correctness | Lean kernel + independent review ONLY | OUT OF TELPERION SCOPE by design — the kernel and the honest-conditional review are the arbiters |

Reading rule (inherited from conjecture1_status.py): a green row verifies THAT stratum; no combination of rows proves the surrounding conjecture.  conjecture1_proved = False until the R7' assembly and its independent review complete.
