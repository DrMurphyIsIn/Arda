# AXLE - third tour: SYSTEM-design lessons for Telperion (2026-09-04)

Rounds 1-2 mined AXLE's *endpoint list* (`/v1/docs/all.json`) and adopted the utility
layer: `verify` (<- `verify_proof`/`check`), `gap_fill` (<- `sorry2lemma` + persistent
`environment`), `repair` (<- `repair_proofs`), the kernel-gated negative control
(<- `disprove`), `cert_meta` (<- `extract_decls`), `bundle` (<- `merge`), `normalize`,
`theorem2sorry`. This third tour is grounded in AXLE's actual system now public:
the arXiv paper (2606.26442, "Axle: A Cloud Infrastructure for Lean 4 Theorem Proving
Utilities"), the live docs (`axle.axiommath.ai/v1/docs`), and the MCP server
(`AxiomMath/axle-mcp-server`). The new material is the **system design** the endpoint
list does not expose - the trust model, the fast verify path, the environment model,
and the structural (not textual) versions of merge/extract - plus the one deferred
endpoint (`simplify_theorems`) seen in a new light.

## The headline: AXLE's fast verify is a TRUST-TIER, and Telperion's generator is cooperating

AXLE's `verify_proof` hits **0.97s median** vs SafeVerify 10.1s and Comparator 95.7s -
100x - by ONE move: it *assumes every declaration in the loaded environment was added
via Lean's normal kernel-checked path and does not re-verify the environment from
scratch*. It then accepts/rejects a candidate on four cheap checks only:

1. no `sorry`;
2. axioms subset {`propext`, `Quot.sound`, `Classical.choice`} (+ per-deployment allow);
3. the candidate's type **signature matches the claimed formal statement** (no reduction, `use_def_eq=False` - catches a weakened/restated theorem);
4. no `unsafe` declarations.

It explicitly *declines* to defend against environment-manipulation attacks
(`Environment.addDeclCore (doCheck := false)`), because its clients COOPERATE (AI
training workloads), not attack. Result: 500M+ requests served, 100% success, 100%
verdict-agreement vs Comparator on conclusive pairs.

**The Telperion lesson.** Telperion's generator is *itself* - a cooperating client. So
Telperion can run the same fast trusted-path check in its inner loop and reserve the
full cold `lake env lean` + `#print axioms` for the final gate. This reframes the whole
verify story as **two tiers**:

- **fast inner tier** (dev / gap-fill / negative-control loop): elaborate the candidate
  against a *warm, already-loaded* environment; check sorry + axiom-whitelist +
  signature-match. Target: sub-second, like AXLE.
- **full outer tier** (final certificate): the current cold build + Comparator
  independent judge (Telperion already ships this, PR #129 / `reference_comparator_integration`)
  - which is literally the 95.7s "Comparator" AXLE benchmarks against.

Telperion already has the slow independent judge; round 3 says *add the fast path as the
inner loop*, not replace the judge.

## Map: new AXLE lesson -> Telperion, prioritized

| AXLE mechanism | Telperion lesson | value | effort | status |
|---|---|---|---|---|
| `verify_proof` standard-path trust (0.97s) | fast warm-env verify tier (sorry+axioms+signature), full build only at the gate | HIGH (latency) | MED-HIGH | sharpens the #5 warm-server spike (currently fallback-only) |
| signature/statement match (`use_def_eq=False`) | **assert the emitted theorem states the INTENDED proposition**, not just that it compiles | HIGH (trust) | LOW-MED | **GAP** - verify.py checks compile+axioms, NOT statement identity |
| named `environment` (version + Mathlib snapshot + deps) | first-class `Environment` registry (name -> built Lake project), multi-version | MED | LOW-MED | GAP - env is ad-hoc `env_dir` paths today |
| `merge`: alpha-equiv dedup + topological dependency sort + mangled-name | bundle.py: topo-sort blocks by inter-ref + dedup by `type_hash` (structural, not text) | MED | LOW-MED | GAP - bundle is name+normalized-text dedup, first-wins, no ordering |
| `extract_decls`: 3-level deps (type/value/syntactic) + self-contained snippets | per-cert dependency set -> dead-atom detect, minimal-snippet emit, impact analysis | MED | MED | GAP - cert_meta has type/proof hash, tactics, heartbeats, NO deps |
| `simplify_theorems`: mechanical prune + fixed-point + rollback | mechanical proof minimizer for emitted Lean (drop unused have/hyps, re-verify, rollback) | LOW-MED | MED | round 2 DEFERRED as "needs proof search" - RECONSIDER: AXLE's is mechanical + verify-guarded, not search |
| `have2lemma`/`have2sorry` (inline-have extraction w/ callsite rewrite) | goal extraction from an inline `have := by sorry` | LOW-MED | MED-HIGH | still deferred (round 2) - only if decouple cells start inlining enclosures |
| `theorem2lemma` (keyword swap), `extract_theorems` | trivial / already covered by cert_meta + normalize | LOW | LOW | skip |

## The high-value ones, in detail

### 1. Signature / statement-match gate - the missing half of the trust boundary (build FIRST)
The negative control proves *a forged FALSE instance is kernel-rejected*. It does NOT
prove *the TRUE instance states the RIGHT proposition*. A buggy emitter can emit a
theorem that compiles, has clean axioms, and is STILL the wrong (weaker) claim - e.g.
`0 <= x^2 + 1` when the certificate targets `0 <= x^2 + x + 1`. AXLE's `verify_proof`
catches exactly this by comparing the candidate's type signature to the claimed formal
statement with `use_def_eq=False`. Telperion analog: extend `verify_lean` with an
`expected` map `{decl_name -> intended Prop}`; after elaboration, elaborate each intended
Prop in the same environment and assert the checked decl's type is (defeq, or exactly)
that Prop. Cheap (`#check`/`isDefEq` on already-elaborated terms), and it closes the
positive half of the untrusted-generator/trusted-kernel boundary. This is the single
highest-trust, lowest-effort round-3 item - build it first. It also strengthens every
negative-control POSITIVE twin (today "true twin compiles"; with this, "true twin
compiles AND states the intended claim").

### 2. Fast warm-env verify tier (the real #5)
The #5 warm-server was shipped as a fallback-guarded spike because the persistent-server
protocol was unvalidated on 4.32.0. The paper gives the actual design that makes it worth
finishing: keep Mathlib resident in a warm worker; per candidate, run only the four cheap
checks against the loaded environment (no environment replay). AXLE trades ~150ms for
per-request process isolation (1.05s vs 0.75s) - Telperion single-user does not even need
that isolation. Concretely: a long-lived `lake env lean --server`-style worker with the
example env preloaded, driven over stdio, returning the same `VerifyResult`. This is what
takes `gap_fill.py`'s per-cell loop from ~4-9s/verify to sub-second - the dominant cost in
the BG per-cell round-trip.

### 3. First-class Environment registry
AXLE: `each request carries an environment field selecting a Lean version + Mathlib
snapshot + project deps; one deployment serves many concurrently`. Telperion targets
`env_dir` paths scattered across `examples/*/lean` and BG worktrees. A small
`Environment(name, project_dir, toolchain)` registry - `verify_lean(..., env="log_combination")`,
`env="bg_r3cert"` - removes the path sprawl, makes multi-version explicit (the repo is
pinned 4.32.0 today but the BG and RH projects differ), and is the natural home for the
warm-worker pool (one warm process per named env).

### 4. bundle.py: topological + structural merge
Today `bundle.merge_bundle` dedups by name and normalized-statement TEXT, first-occurrence
wins, and emits blocks in first-seen order. Two AXLE upgrades: (a) **topological sort** by
inter-block reference so a bundle where one cell's proof uses another cell's atom
elaborates in dependency order (today it can fail if ordered wrong); (b) dedup by
`cert_meta.type_hash` (structural / alpha-equivalent) instead of text, catching
cosmetically-different-but-identical atoms the text compare misses. Both reuse machinery
Telperion already has (`cert_meta.type_hash`); low effort, real payoff as the BG cell
family grows.

### 5. Per-cert dependency extraction
`extract_decls` returns each decl's transitive dependencies at three levels. cert_meta
today stops at type_hash/proof_hash/tactics/heartbeats. Adding a dependency set per emitted
theorem (the constants/other-certs it references) buys: dead-atom detection (an atom no
cert uses), minimal self-contained snippet emission (emit only what a cert needs to
elaborate standalone), and impact analysis (when a shared atom like `log54_sub_fstar_le`
changes, exactly which certs to re-verify). This is the cert-graph the round-2 doc
gestured at, now with the AXLE mechanism behind it.

## Meta-lessons (the deepest round-3 takeaways)

- **Two trust tiers, not one.** AXLE's whole speed story is "trust the kernel-checked
  environment; check only the delta." Telperion conflates the fast dev loop and the final
  gate into one cold full build. Splitting them (fast inner, full+Comparator outer) is the
  unifying frame for the warm server AND the signature gate.
- **Structural beats textual.** merge/extract/dedup in AXLE are alpha-equivalence and
  dependency based; Telperion's are still text (normalized statements, name dedup).
  cert_meta's `type_hash` is the bridge already in-tree - wire it into bundle and deps.
- **The generator is a cooperating client.** Telperion need not defend its *own* emitter
  output against adversarial environment manipulation; it can take AXLE's fast-path shortcut
  internally and keep the paranoid full check only where an external artifact is claimed.

## Recommendation

Build order: **(1) signature/statement-match gate** (highest trust, lowest effort, closes
the positive half of the boundary - build first) -> **(2) fast warm-env verify tier**
(finish #5 with the paper's design; biggest latency win for the BG loop) -> **(4) bundle
topo+type_hash** and **(5) per-cert deps** (both reuse `cert_meta.type_hash`, practical for
the growing family) -> **(3) Environment registry** (the home for the warm workers) ->
**(6) mechanical simplify** (reconsider the round-2 deferral; verify-guarded, not search).
`have2lemma` stays deferred until enclosures inline. conjecture1_proved = False.
