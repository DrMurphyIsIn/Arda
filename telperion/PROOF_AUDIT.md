# PROOF AUDIT — the Brualdi-Goldwasser campaign, by verification stratum

Generated 2026-08-16 by `examples/proof_audit/generate_audit.py`; executable rows were EXECUTED (frozen manifests read, exports recheck-verified live).  Do not edit; regenerate.

| stratum | method | state |
|---|---|---|
| Lean core: bridge + phi_le_one + merge layer + parse (90 R3Cert modules) | Lean kernel (origin CI) | KERNEL-CHECKED — origin pipeline 2762803858 @ b2996c79; reviewed PASS 2026-08-14/15 |
| G1Kernel + Real.log bridges + 103 hinge-dead classes | Lean kernel (origin CI) | KERNEL-CHECKED origin-side (parallel session; trio round in flight) |
| 36-cell unified merge table (HypStar seam) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 216 theorems frozen [5645431aded2]; sampled recheck GREEN (4 cell(s)) |
| G1 floors: dichotomy/tax/below-window + anchors (HypFloors) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 3260 theorems frozen [dc72d7c87c2f, 0ace82300c53]; RECHECK ERROR: TypeError — COMPILE-GATED green @6758e88; handoff ACCEPTED (origin bf2f0747); 1 fragile cell tripwired ((2,0,1) @0.59 width) |
| R6 shedding lemmas (de-loading schedule) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 55 theorems frozen [022ea4f8feb5]; sampled recheck GREEN (2 cell(s)) |
| Legs certificates + the 726-digit bignum ((L) layer) | Telperion re-derivation + stdlib recheck | RE-DERIVED: 48 theorems frozen [1d128764a53d]; sampled recheck GREEN (2 cell(s)) |
| Interpolation lemma: I1 UPGRADED TO SYMBOLIC (vs origin's 199 point checks) + I2 + 212 light-top facts with witness table | Telperion re-derivation + stdlib recheck | RE-DERIVED: 215 theorems frozen [3a6852dde1a0, 3e75efae2723, fcd5c1a23daa]; sampled recheck GREEN (5 cell(s)) — heavy-top sup + DELTA sweep are float-guarded in origin; exact counterparts routed to g1_endpoint_certificates (origin G1FIX arc) |
| 972 star-of-hubs dominations (HypStarSymbolic) | Telperion re-derivation + stdlib recheck | IN FLIGHT — freeze not yet landed |
| Two-hub residual tails: T1/T2/T3a symbolic + T3b small-donor per-residue witness certificates | Telperion re-derivation + stdlib recheck | IN FLIGHT — freeze not yet landed — witnesses_complete (residue-dependent comparator phenomenon recorded: some odd residues need the load-6 hub, not the defect template) |
| G34 residual sweep (442,800 cases) | independent Fraction port + SHA-256 fingerprint + stdlib recheck | RE-DERIVED: 442800 cases exact, fingerprint 8351f230f2dacf49; sampled recheck GREEN (500 cases, third engine); tightest margin 6.7175% at ('B', 'arm2', 4, 1, 1, 2) — where the two-hub family comes closest to the single-hub bound |
| Hunt-attack sweep over all certified families | planned | PLANNED — three-mode adversarial minimization; queued |
| Structural inductions (telescoping, termination, acyclicity); R7' assembly correctness | Lean kernel + independent review ONLY | OUT OF TELPERION SCOPE by design — the kernel and the honest-conditional review are the arbiters |

Reading rule (inherited from conjecture1_status.py): a green row verifies THAT stratum; no combination of rows proves the surrounding conjecture.  conjecture1_proved = False until the R7' assembly and its independent review complete.
