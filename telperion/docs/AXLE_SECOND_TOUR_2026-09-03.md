# AXLE — second tour: further lessons for Telperion (2026-09-03)

A systematic pass over Axiom Math's AXLE endpoints (`/v1/docs/all.json`) beyond the
two already adopted (`verify_lean` ← `verify_proof`/`check`; `gap_fill` ←
`sorry2lemma` + persistent `environment`; `repair.py` ← `repair_proofs`). For each
remaining capability: the Telperion lesson, and a priority/effort call. AXLE ships
*orthogonal, typed, single-purpose primitives and leaves the proving LOOP to the
caller* — that composition discipline is itself the frame here.

## Map: AXLE capability → Telperion lesson

| AXLE | Telperion lesson | value | effort | status |
|---|---|---|---|---|
| `verify_proof` / `check` | structured verify; compile vs trusted(sorry-reject) split | — | — | **done** (`verify.py`) |
| `sorry2lemma` + `environment` | gap-driven fill against a persistent env | — | — | **done** (`gap_fill.py`) |
| `repair_proofs` | mechanical Mathlib-drift repair, fallback + re-verify | — | — | **done** (`repair.py`) |
| `disprove` (prove the negation) | **kernel-gated negative control** | HIGH (trust) | MED | proposed |
| `extract_proof_states` + `have2lemma` | goal extraction from a real `sorry`/`have` INSIDE a proof | MED | MED-HIGH | proposed |
| `extract_decls` (type_hash, heartbeats, tactic_counts, deps) | structured proof metadata + content-addressed cert index | MED | MED | proposed |
| `merge` (+ `merge_duplicates`) | cert-bundle assembly with dedup of shared atoms | MED | LOW-MED | proposed |
| `normalize` | canonical form for emitted Lean → robust drift-diffs | LOW-MED | LOW | proposed |
| `simplify_theorems` | proof minimization (shorter/cheaper emitted proofs) | LOW | MED | note |
| `theorem2sorry` | re-attack blanking (blank → regenerate → diff, regression) | LOW-MED | LOW | note |
| `rename` | mechanical rename utility | LOW | LOW | skip |

## The high-value ones, in detail

### 1. Kernel-gated negative control (`disprove`) — TOP recommendation
Telperion's negative control is currently a Python `ValueError` in the sympy
self-check — **untrusted**. The whole Telperion thesis is "untrusted generator,
trusted kernel"; the negative control is the one place that thesis leaks, because a
buggy self-check could pass a false instance (caught only later, when the emitted
proof fails to compile). AXLE's `disprove` certifies falsity *in the kernel*. The
Telperion analog: for a KNOWN-FALSE spec, run the emitter and confirm via
`verify_lean` that the emitted "proof" does **not** compile — i.e. certify the
meta-property *the generator cannot forge a compiling proof of a false claim*. That
turns the negative control from a sympy assertion into a kernel-checked fact.
Buildable now on `verify.py`; hardens Telperion's raison d'être. **Build this next.**

### 2. Goal extraction from a real `sorry`/`have` (`extract_proof_states`, `have2lemma`)
`gap_fill` today matches STANDALONE `:= by sorry` lemmas. That already covers the BG
pattern (enclosure atoms ARE standalone lemmas — `log79_add_fstar` etc.), so this is
a *generalization, not a current blocker*. It matters when an enclosure lives as an
inline `have h : … := by sorry` mid-proof: extracting that goal needs the actual
tactic state, which is Lean introspection (a small metaprogram or a `lean --server`
call), not regex. Worth it if the decouple cells start inlining enclosures; until
then, keep enclosures as standalone lemmas and `gap_fill` suffices.

### 3. Structured proof metadata + content-addressed cert index (`extract_decls`)
Telperion carries only a provenance input-hash. AXLE's `extract_decls` returns
`type_hash`, `unfolded_type_hash`, `term_depth`, `tactic_counts`, `heartbeats`,
`proof_length`, and dependencies. Emitting per-cert metadata gives: **regression**
(flag when a Mathlib bump balloons an emitter's heartbeats/proof length) and a
**dedup'd cert graph** (type_hash keys shared atoms — e.g. `log54_sub_fstar_le`
reused across cells — so `merge` can dedup). This is the "cert-sensitivity registry"
idea with real infrastructure behind it.

### 4. Cert-bundle merge + dedup (`merge`)
The BG cell family is many cells sharing enclosure atoms. `merge` assembles a bundle
into one file and dedups shared lemmas (by name / type_hash from #3). Practical
housekeeping as the family grows; low effort, mostly text assembly.

## Meta-lessons (the deepest takeaways)

- **Sharp primitives, thin composition.** AXLE ships no proving loop — orthogonal
  tools, composed by the caller. Keep Telperion's infra primitives single-purpose
  and composable (`verify` / `fill` / `repair` are); build the loop as thin
  composition (the round-trip), never a monolith.
- **A trusted-infra-as-a-typed-service LAYER.** AXLE's value is the coherent,
  typed, verified-Lean utility layer with the AI at a higher layer. Telperion had
  the kernel boundary but ad-hoc infra around it; `verify`+`gap_fill`+`repair` are
  the start of that layer — continue it (metadata, merge, negative-control).
- **Structured envelopes make tools composable.** AXLE's uniform result envelope is
  why its tools chain. `VerifyResult`/`FillResult` adopted this; hold the line —
  every new primitive returns a typed result, not a printed string.

## Recommendation

Build order: **(1) kernel-gated negative control** (hardens the trust story, buildable
now) → **(3) proof metadata + cert index** + **(4) merge/dedup** (practical for the
growing BG family) → **(2) real-sorry goal extraction** only if enclosures start being
inlined. `simplify`/`normalize`/`theorem2sorry`/`rename` are polish, deferrable.
conjecture1_proved = False.
