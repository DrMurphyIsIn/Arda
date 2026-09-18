# MIRRORMERE team run -- integration report, 2026-09-18

conjecture1_proved = False

Scope note, stated once and binding on every line below: **no RH progress is claimed here.**
Nothing in this run proves, or moves materially toward, the Riemann Hypothesis. What the run
produced is (a) a handful of small unconditional lemmas inside an already-existing instrument
library, (b) seven new certificate-emitter kinds, and (c) three registry statements, one of
which is RH-equivalent and therefore registered permanently as a wall (section 5). Every
delivered theorem is sorry-free; everything unproved sits in a `draft` registry statement or a
clearly named WIP/Probe file, never inside a `defaultTargets` build or an axiom guard.

Report author ran no proofs of its own; all verdicts below are the paired verifiers' and are
reproduced with their polarity intact. Where a verifier said "unverified", this report says
unverified.

---

## 0. Run shape

Three parallel survey waves proposed 25 work items. Skeptics dropped 8 before execution.
12 ran to a closed state. 5 were neither dropped nor run (section 6.3).

Branch/base topology, re-derived here with `git merge-base --is-ancestor`, not taken from the
worker reports:

| base the branch actually sits on | items |
| --- | --- |
| `origin/rh/e8-proof` (tip `b448f1b3d`) | w2c-assembly, w3c-goal-weil-membership, tool-interval-gram-inertia, d2-weil-gram-trace, tool-weil-form-enclosure, mm-d3-certified-height-weil-bound |
| `origin/rh/million-turing` @ `0bac3e608` | twofreq-offline-emitter, recurrence-deficit, exp-enclosure-emitter, mm-euler-factor-offline, offline-disjoint-discs, torus-ladder-t1 |

Two facts the integrator needs before anything else:

1. **`origin/rh/e8-proof` is already fully contained in `origin/main`.** `merge-base(main,
   e8-proof) == b448f1b3d == e8-proof tip`; `main` is 71 commits ahead of it. So the six
   e8-based branches are *behind* main but not divergent from it, and each can be rebased onto
   `origin/main` directly.
2. **`origin/rh/million-turing` has moved** since these six branches were cut: `0bac3e608 ->
   3b31737b5`. Those branches must be rebased onto the new tip before any PR, and they are
   genuinely divergent from main (merge-base `10d52ac67`, 97 commits of main not in them).

No branch was pushed. `git ls-remote --heads origin mm/*` is empty for all twelve. No PRs exist.

---

## 1. Per-item ledger

Format: delivered / verdict / where / integrator actions.

### 1.1 mm-w2c-assembly -- VERIFIED

* **Delivered.** `W2cAssembly.lean` on the rvm_bridge island: the unconditional W2c form,
  `RvMBridge.zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density`, assembled across
  islands from the already-proved `MM_rvm_unbounded_mean_density` (E6 bridge). Sorry-free, no WIP
  file. Also new: `telperion/src/telperion/port_match.py` + tests (statement-port matching across
  toolchain islands).
* **Verdict.** VERIFIED. Verifier re-ran `lake build` ("8827 jobs", exit 0) and re-ran
  `AxiomGuardRvMBridge.lean` standalone: 51 `#print axioms` anchors, every one exactly
  `[propext, Classical.choice, Quot.sound]`, `sorryAx` count 0. Statement is the node's claim
  verbatim, not weakened.
* **Where.** branch `mm/w2c-assembly`, commit `d0c18a682e36b9f8e50e8ba809ff5cc6815f6b2a`,
  worktree `/Users/peterwmurphy/arda-mm-w2c-assembly`. 10 files.
* **Integrator.** PR against `origin/main` (e8 content is already in main). Registry: node
  `MM_zeta_ordinates_not_uniformly_discrete` is proof-linked with a `Stalled` attempt and stays
  `open` on purpose; run `telperion mission grant MM_zeta_ordinates_not_uniformly_discrete`
  only after CI `rvm-bridge-compiles` is green post-merge (the E6 precedent). No telperion.toml
  or CI change. Touches `examples/rvm_bridge/generate.py` -- see conflict C3.

### 1.2 mm-recurrence-deficit -- VERIFIED

* **Delivered.** `RecurrenceDeficit.lean` + `ExpLaurentDeficit.lean` on the zeta_zero_localization
  island (zzl_aux block): `recurrenceDeficit (1/10) = excess` and `0 < recurrenceDeficit d` for
  `d > 0`. New emitter kind **`exp_laurent_identity`** (`emit_exp_laurent_identity.py`, negctrl
  adapter, tests, `examples/exp_laurent_deficit/generate.py`).
* **Verdict.** VERIFIED. Verifier re-ran `lake build` in zzl_aux ("8775 jobs"), and defeated the
  shared-`.lake` staleness risk by re-elaborating both sources from source with `lake env lean`
  (exit 0 each). Axiom guard re-run as CI runs it.
* **Where.** branch `mm/recurrence-deficit`, commit `a5e46cbbf87b068bdf63db9b7406393376f540ab`,
  worktree `/Users/peterwmurphy/arda-mm-recurrence-deficit`. 17 files.
* **Integrator.** Rebase onto the new `origin/rh/million-turing` tip `3b31737b5`, PR there.
  Registry: node `MM_recurrence_deficit_eq_excess` linked, grant deferred to the
  million-turing -> main reconcile; the statement gate was pre-flighted
  (`statement_matches` True). telperion.toml: adds `[[check]] name="exp_laurent_deficit"`,
  group `quick`. No CI job added. Touches `certify.py`, `emitter_sensitivity.py`,
  `src/telperion/__init__.py`, `negctrl_adapters/__init__.py`, `telperion/README.md` -- conflicts
  C1, C2.
* **Caveat carried forward.** A *second, independent* copy of this node's obligation exists as a
  by-design `sorry` in `missions/mirrormere/lean/Statements/MM_recurrence_deficit_eq_excess.lean`
  (noted by the exp-enclosure verifier). Registry statement files are draft mirrors, not
  deliverables -- but the integrator should confirm the mirror is retired or reconciled at grant.

### 1.3 mm-euler-factor-offline -- VERIFIED

* **Delivered.** `EulerFactorOffline.lean` + `SelfInversiveOfflineInstances.lean` on the
  quasicrystal island; a new **offline certificate mode on the existing
  `emit_selfinversive_rigidity` emitter** (this is where the surveyed but unrun
  `tool-selfinversive-offline-mode` item actually landed).
* **Verdict.** VERIFIED. `lake build` "8672 jobs"; `AxiomGuardQC.lean` re-run, all 60
  declarations exactly the three standard axioms, 0 `sorryAx`/`native_decide`/`ofReduceBool`.
  Statement verbatim, non-vacuous.
* **Where.** branch `mm/mm-euler-factor-offline`, commit `b73ad6cb93fcdbf7d06169882ef3fa4bebd66654`,
  worktree `/Users/peterwmurphy/arda-mm-mm-euler-factor-offline`. 13 files.
* **Integrator.** Rebase onto new million-turing tip, PR there. Registry: `MM_euler_factor_section_offline`
  linked, grant deferred. Touches `.github/workflows/telperion-lean-e2e.yml` and
  `emitter_sensitivity.py` -- conflicts C1, C2.
* **HARD CONFLICT.** This item and `twofreq-offline-emitter` **both proof-link the same node**
  `MM_euler_factor_section_offline`, to *different* Lean modules
  (`EulerFactorOffline.lean` vs `EulerFactorSectionOffline.lean`). See C4 -- the integrator must
  choose one proof link.

### 1.4 mm-offline-disjoint-discs -- VERIFIED

* **Delivered.** `OfflineDiscs.lean` + `OfflineDiscsInstances.lean` (quasicrystal island): the
  E4b isolation lemma, a finite strip point set admits a positive radius with pairwise disjoint
  closed balls. New emitter kind **`disjoint_discs`** with negctrl adapter, tests, generate.py,
  CI job `disjoint-discs-compiles`.
* **Verdict.** VERIFIED. Verifier exported the campaign from `origin/main` and re-ran the
  statement-containment gate with the gate's own functions; theorem is the node's claim verbatim.
  Three cosmetic/process discrepancies, none load-bearing.
* **Where.** branch `mm/offline-disjoint-discs`, commit `b2303c63f259d470a8587e71e6783a48b19f9ea9`,
  worktree `/Users/peterwmurphy/arda-mm-offline-disjoint-discs`. 18 files.
* **Integrator.** Rebase onto new million-turing tip. Registry: `MM_offline_disjoint_discs`
  linked + `Stalled` attempt, grant belongs on main after reconcile. telperion.toml adds
  `[[check]] name="disjoint_discs"` (quick); CI adds `disjoint-discs-compiles`. Conflicts C1, C2.
* **Note on scope.** The skeptics dropped `tool-disjoint-discs-instance`; the emitter was minted
  anyway inside this prove item. That is a defensible fold (the instance emitter is what proves
  the node), but it means the dropped-item list understates the tool surface that landed.

### 1.5 mm-torus-ladder-t1 -- VERIFIED

* **Delivered.** `TorusSectionLadder.lean` (quasicrystal island): `torus_section_dictionary`
  (`twoFreq = linearTorusForm 2` on `torusOrbit 2`) and `torus_section_n2_rigidity` (the N=2
  rung in ladder vocabulary, reduced to `twoFreq_realRooted_iff`). Both simp-grade, sorry-free.
  Smallest and cheapest win of the run.
* **Verdict.** VERIFIED. `lake build` rebuilt `TorusSectionLadder` under the verifier's own run
  (olean mtime checked, so the axiom guard read the verifier's olean, not a sibling's);
  `AxiomGuardQC.lean` 45 declarations, all three-axiom clean. Two of the worker's *process*
  claims were corrected by the verifier; no math defect.
* **Where.** branch `mm/torus-ladder-t1`, commit `48780b578960c7af12771075d6ef98149593f98f`,
  worktree `/Users/peterwmurphy/arda-mm-torus-ladder-t1`. 7 files, registry-only outside Lean.
* **Integrator.** Rebase onto new million-turing tip. Registry: both `MM_torus_section_dictionary`
  and `MM_torus_section_n2_rigidity` proof-linked. `MM_torus_section_dictionary` is
  `status = "draft"` and **cannot be granted** until it is promoted draft -> open, which the
  unrun `mm-dictionary-reaudit` item was supposed to do (section 6.3). No telperion.toml, no CI.
  Lowest-conflict item in the run.

### 1.6 twofreq-offline-emitter -- VERIFIED

* **Delivered.** New emitter kind **`twofreq_offline`** (exact off-line displacement certificates,
  registered as the exact complement of `SelfInversiveRigidityEmitter`), negctrl adapter, two
  test files, `examples/twofreq_offline/generate.py`, and the dogfood artifact
  `EulerFactorSectionOffline.lean` on the quasicrystal island (8 theorems, all proved).
* **Verdict.** VERIFIED. 20 python tests re-run; `generate.py --check` byte-for-byte OK; the
  `MANIFEST INCOMPLETE` rule re-implemented independently against telperion.toml (`unlisted: []`);
  `lake build EulerFactorSectionOffline` green.
* **Where.** branch `mm/twofreq-offline-emitter`, commit `1ee27551d7bfbab34b3c0dffc98f26c04b9a6c9a`,
  worktree `/Users/peterwmurphy/arda-mm-twofreq-offline-emitter`. 17 files.
* **Integrator.** Rebase onto new million-turing tip. telperion.toml adds
  `[[check]] name="twofreq_offline"` (quick); CI adds `twofreq-offline-compiles`. The new lean_lib
  is deliberately **out of `defaultTargets`** until that CI job is green on a real runner -- do
  not "fix" that before the job runs. Registry: links `MM_euler_factor_section_offline` --
  **collides with 1.3, see C4.**

### 1.7 exp-enclosure-emitter -- VERIFIED

* **Delivered.** New emitter kind **`exp_enclosure`** (exact rational brackets of `Real.exp` from
  `Real.exp_bound`, `|x| <= 1`; the halving extension is documented and deliberately not
  implemented), adapter, 29 tests, `ExpEnclosureInstances.lean` on zzl_aux, CI job
  `exp-enclosure-compiles`.
* **Verdict.** VERIFIED. All python counts reproduced; `generate.py --check` and the drift guard
  re-run; classification gates confirmed to have *run* rather than skipped. One cosmetic
  attribution deviation and one count discrepancy caused by the verifier's own machine filling
  its disk.
* **Where.** branch `mm/exp-enclosure-emitter`, commit `d29a35c725259674c9e7d9e9804ebce4b125a7b3`,
  worktree `/Users/peterwmurphy/arda-mm-exp-enclosure-emitter`. 16 files.
* **Integrator.** Rebase onto new million-turing tip. telperion.toml adds
  `[[check]] name="exp_enclosure"` (quick); CI adds `exp-enclosure-compiles`. Conflicts C1, C2.

### 1.8 tool-interval-gram-inertia -- VERIFIED

* **Delivered.** New emitter kind **`interval_gram_inertia`**: exact signature (posIndex, defect)
  of every Hermitian matrix in an interval box, with a `RHInertia.lean` prelude, four shipped
  certificates, `AxiomGuardGramInertia.lean`, a full example island
  (`examples/gram_inertia/`), CI job `gram-inertia-compiles`, catalog + README rows.
  The largest single tool of the run (36.9 KB emitter).
* **Verdict.** VERIFIED. 29 emitter tests, 179 registry tests, 12 sensitivity tests re-run and
  matched exactly. The verifier went further than the worker and **tested kernel-sensitivity on
  the production emission path itself**, because the shipped negative control does not. Nothing
  faked, no sorry, theorems non-vacuous.
* **Where.** branch `mm/tool-interval-gram-inertia`, commit `34a574592c6c9018166b081d91e2806c9a86974d`,
  worktree `/Users/peterwmurphy/arda-mm-tool-interval-gram-inertia`. 19 files, +2457/-1.
* **Integrator.** PR against `origin/main`. telperion.toml adds `[[check]] name="gram_inertia"`
  (quick); CI adds `gram-inertia-compiles`. No registry touch at all -- this is the cleanest tool
  branch to land first. Conflicts C1, C2 and, importantly, **C5** (d2 ships a second, different
  `emit_interval_gram_inertia.py`).
* **Refused by design, not faked:** complex-Hermitian instances (needs a `posIndex_realEmbed`
  prelude lemma, stated in the item's remaining-work note, written nowhere) and definite boxes
  (`p=0` or `q=0`, which have no `Fin 0` matrix literal) are *rejected at certification time*.

### 1.9 tool-weil-form-enclosure -- UNVERIFIED (environment, no defect found)

* **Delivered.** New emitter kind **`weil_form_enclosure`**: Arb-evaluated enclosures of the E8
  Weil pairing `archSide - primeSide` on two compactly supported bump test functions plus their
  2x2 Gram block; `weil_form_eval.py` backend, adapter, tests, an example island with
  `WeilFormDefs.lean` / `WeilFormEnclosure.lean` / `AxiomGuardWeilForm.lean`, CI job
  `weil-form-enclosure-compiles`, catalog row.
* **Verdict.** **UNVERIFIED.** The verifier states plainly: `verified=false` for one reason only
  -- `generate.py --check` could not be run because the machine filled its disk mid-verification.
  Kernel verification *did* pass (`lake build` 8660 jobs; `AxiomGuardWeilForm.lean` re-elaborated
  fresh, three-axiom clean). No defect was found; several worker claims were actively attacked
  and survived. Treat as "very likely good, one gate unrun".
* **Where.** branch `mm/tool-weil-form-enclosure`, commit `55c3a655343946d50905567b815aba58ee60226b`,
  worktree `/Users/peterwmurphy/arda-mm-tool-weil-form-enclosure`. 20 files, +2189/-1.
* **Integrator.** **Re-run `python3 examples/weil_form_enclosure/generate.py --check` before
  merging.** PR against `origin/main`. telperion.toml adds `[[check]] name="weil_form_enclosure"`
  in group **`flint`** (needs python-flint; archimedean quadrature to `|r| <= 1024`, ~4 min).
  CI adds `weil-form-enclosure-compiles`. **C6: a second, different `weil_form_enclosure` check
  entry and example island ship on the w3c branch in group `quick`.**
* **Honest open item the tool itself names.** The emitted theorems take `IsWeilTest g` as a
  *hypothesis*; no Lean witness yet says the concrete bump family the Arb backend measures is in
  that class. The needed statement (`exists_measured_weil_test`) is written out in the item's
  remaining-work note and is proved nowhere. Until it exists, no emitted instance can be composed
  with `limit_explicit_formula` at a concrete test function. Separately, the dogfood island is
  v4.32.0 while `RvMBridge4.limit_explicit_formula` is v4.33.0-rc2, so they cannot share a file.

### 1.10 mm-w3c-goal-weil-membership -- UNVERIFIED (audit could not run; three trust-surface gaps)

* **Delivered.** The W3c goal statement, replacing the flagged placeholder. `MM_zeta_comb_membership`
  now reads, in the program's own vocabulary, as Weil positivity of `weilForm` on Hermitian
  autocorrelations over the `IsWeilTest` class -- the Guinand-Weil regularized triple made
  concrete by `RvMBridge4.limit_explicit_formula`. Plus `weil_gauss.py`, a
  `weil_form_enclosure` emitter + adapter + tests + example island, a WIP probe file, a 92-line
  `MMDefs.lean` vocabulary extension, and a design memo. Node stays `kind=goal`,
  `status=draft`, never attempted, decomposition refused.
* **Verdict.** **UNVERIFIED.** The auditor's every Bash call failed with ENOSPC (root volume at
  0 bytes); the entire dynamic half of the audit -- `lake build`, `#print axioms`, `mission
  verify`, pytest, negative-control harness, even `git diff` -- was impossible. The audit that
  *was* performed (file reads plus independent mathematics) found **no mathematical defect**:
  statement, vocabulary and numerics check out under independent re-derivation. `verified=false`
  additionally cites three undisclosed trust-surface gaps in the new tooling.
* **Where.** branch `mm/w3c-goal-weil-membership`, commit `289c68c8062527f665fe81c1abea862b30589af3`,
  worktree `/Users/peterwmurphy/arda-mm-w3c-goal-weil-membership`. 20 files.
* **Integrator.** **Do not merge until the full dynamic gate set is re-run on a machine with
  disk.** Then PR against `origin/main`. The registry writer path was used (node + mission.toml
  updated through the CLI). Known deviations carried by the worker:
  1. `depends_on` was deliberately *not* extended to the D2/D3 nodes, because they were not yet
     registered and a dangling dependency fails `mission verify`. Add `MM_weil_gram_trace` and
     `MM_weil_form_certified_height` once 1.11 and 1.12 land.
  2. The `autocorr`/`crossCorr` normalisation constraint for D2 is recorded in the memo but not
     encoded.
  3. `build_mmdefs.py` (the second-copy guard for `MMDefs.lean`) remains a grant-pass deliverable;
     the interim guard is check (7) in `examples/rvm_bridge/generate.py`.
  4. The registry test suite `tests/test_missions_*.py` was **never run to completion** (ENOSPC).
* **Disk.** This item's `lake exe cache get` for the mirrormere island added **7.8 GB** at
  `/Users/peterwmurphy/arda-mm-w3c-goal-weil-membership/telperion/missions/mirrormere/lean/.lake`.
  It still exists and is still 7.8 GB. Per standing rule it was not deleted; the root volume has
  since recovered (106 GB free at the time of writing). Freeing it is a human call.

### 1.11 mm-d2-weil-gram-trace -- UNVERIFIED (one wrong causal claim, committed into the registry)

* **Delivered.** A new registry node `MM_weil_gram_trace` (D2): the Weil Gram matrix is
  Hermitian, its entries are the zero-side sums, and its Hermitian form reads as
  `(archSide - primeSide).re` of the cross-correlation. Registered `status=draft` with a
  by-design `sorry`. Plus probe files with certified samples, `regen_samples.py`, a
  `MMDefs.lean` extension, and **second copies** of both `emit_weil_form_enclosure.py` and
  `emit_interval_gram_inertia.py`.
* **Verdict.** **UNVERIFIED.** The blind auditor is explicit: the *statement is clean* --
  faithful, non-vacuous, not weakened, and its two nontrivial mathematical claims were
  re-derived by hand and confirmed numerically. `verified=false` for exactly two reasons:
  (a) the worker's "lake build Probes clean" claim became un-rerunnable when the disk filled;
  (b) **one causal claim is wrong, and it is baked into the committed node TOML title as well as
  the memo**, where it contradicts the same files' own conjunct-1 rationale.
* **Where.** branch `mm/d2-weil-gram-trace`, commit `7b80d8dd5d27e31cffe2f918f176eb8c50285868`,
  worktree `/Users/peterwmurphy/arda-mm-d2-weil-gram-trace`. 18 files.
* **Integrator.** **Fix the node TOML title before merging** -- a wrong causal claim inside a
  hash-locked registry artifact is exactly the kind of thing that outlives the memo it came from.
  Then re-run the Probes build. No `mission audit` was run; the node stays draft. The two new
  emitter kinds here ship with **no** `examples/<name>/generate.py`, **no** telperion.toml
  `[[check]]` entry, **no** CI job, **no** README row and **no** negctrl adapter -- both are
  declared `NEG_CONTROL_DECLARED_UNWIRED` / not-applicable-with-reason rather than claiming a
  control. That is honest, but it means this branch's tooling is *not* CI-gated.
* **Conflicts C5, C6 (both severe):** the emitter files here are byte-different from the
  standalone tool branches -- `emit_weil_form_enclosure.py` 12446 B here vs 19148 B on
  tool-weil-form-enclosure vs 12516 B on w3c; `emit_interval_gram_inertia.py` 20267 B here vs
  36898 B on tool-interval-gram-inertia. The registry stances also disagree: this branch
  registers `WeilFormEnclosureEmitter` as `CERTIFICATE_SENSITIVE` with no adapter, w3c registers
  it `STRUCTURALLY_NONVACUOUS` with an adapter, tool-weil registers it `CERTIFICATE_SENSITIVE`
  with an adapter.

### 1.12 mm-d3-certified-height-weil-bound -- UNVERIFIED (one factual inaccuracy in a committed artifact)

* **Delivered.** A new registry node `MM_weil_form_certified_height` (D3, reformulated): an
  explicit-formula truncation at height T with an `O(log T / T^3)` remainder, plus a conditional
  on-line positivity clause. Registered `status=draft`, by-design `sorry`. New emitter kind
  **`bounded_hypothesis_collapse`** (a statement-*shape* audit: kernel-checkable witness that a
  decaying-error + height-indexed-hypothesis + T-independent-conclusion shape collapses under an
  explicit constant), with `examples/shape_audit/`. This is the run's most interesting tool idea:
  it is a certificate about the *shape of a statement*, minted precisely because the authoring
  pass found no existing certificate type that could catch a silently-collapsing hypothesis.
* **Verdict.** **UNVERIFIED.** The blind auditor honored the protocol (node -> statement ->
  MMDefs -> own derivation -> elaboration -> probes -> vacuity hunt -> memo last) and reports:
  "the mathematics, vocabulary, build, certificates and gates all check." `verified=false` for
  **one factual inaccuracy baked into a committed, hash-locked registry artifact** (their finding
  D1). Nothing mathematical is weakened; no fake proof; no RH claim.
* **Where.** branch `mm/mm-d3-certified-height-weil-bound`, commit
  `016246ca23a0a4e0528f01045ceb57f2323e7b1b`, worktree
  `/Users/peterwmurphy/arda-mm-mm-d3-certified-height-weil-bound`. 15 files.
* **Integrator.** **Correct finding D1 in the committed artifact, then re-hash, then merge.**
  PR against `origin/main`. telperion.toml adds `[[check]] name="shape_audit"` (quick).
  Two of the listed artifacts are scratchpad probe files under `/private/tmp/...` and are *not*
  in the commit -- do not go looking for them in the tree.
* **Named sub-obligations a later prover owes** (none registered): the autocorrelation kernel
  factorisation; the `|H_g(rho)| <= C_g/|rho - 1/2|^2` decay; the tail sum bound from
  `RH_rvm_unconditional`; `riemannZeta (conj s) = conj (riemannZeta s)` (available in Mathlib
  v4.32 `ZetaAsymp.lean:458`); `riemannZeta sigma != 0` on real `sigma in (0,1)` (**not** in
  Mathlib v4.32); and `IsWeilTest (autocorr g)` (carried as a hypothesis, not proved).

---

## 2. Verification scoreboard

| item | verified | why not |
| --- | --- | --- |
| mm-w2c-assembly | yes | -- |
| mm-recurrence-deficit | yes | -- |
| mm-euler-factor-offline | yes | -- |
| mm-offline-disjoint-discs | yes | -- |
| mm-torus-ladder-t1 | yes | -- |
| twofreq-offline-emitter | yes | -- |
| exp-enclosure-emitter | yes | -- |
| tool-interval-gram-inertia | yes | -- |
| tool-weil-form-enclosure | **no** | `generate.py --check` unrun (disk full). No defect found. |
| mm-w3c-goal-weil-membership | **no** | Entire dynamic audit unrun (ENOSPC) + 3 undisclosed trust-surface gaps. No math defect found. |
| mm-d2-weil-gram-trace | **no** | Probes build unrerunnable + wrong causal claim committed in the node TOML title. Statement itself clean. |
| mm-d3-certified-height-weil-bound | **no** | One factual inaccuracy in a committed hash-locked registry artifact. Math/build/certs check out. |

8 verified, 4 unverified. Every one of the four unverified items is unverified for *process or
environment* reasons plus, in two cases, **prose inaccuracies committed into registry artifacts**
-- not for a mathematical defect. No verifier found a faked proof, a weakened statement, or a
vacuous theorem anywhere in the run.

---

## 3. Cross-cutting integration hazards

Ranked by how much damage a careless merge does.

**C4 (blocking). Two items proof-link the same node to different artifacts.**
`MM_euler_factor_section_offline` is linked to `examples/quasicrystal/lean/EulerFactorOffline.lean`
by mm-euler-factor-offline and to `examples/quasicrystal/lean/EulerFactorSectionOffline.lean` by
twofreq-offline-emitter. Both are on the quasicrystal island, both proved and axiom-clean, both
`via = "direct"`. The integrator must pick one proof link (keeping both Lean modules is fine).
Recommendation: keep the `twofreq_offline`-generated `EulerFactorSectionOffline.lean` as the
proof link, because it is the emitter-generated, drift-gated artifact, and demote the other to a
hand-written companion -- but verify which one the node's statement gate actually matches before
deciding.

**C5/C6 (blocking). Three divergent copies of `emit_weil_form_enclosure.py`, two of
`emit_interval_gram_inertia.py`, three divergent `MMDefs.lean` edits.**
Blob sizes: `emit_weil_form_enclosure.py` = 12516 (w3c) / 19148 (tool-weil) / 12446 (d2);
`emit_interval_gram_inertia.py` = 36898 (tool) / 20267 (d2); `MMDefs.lean` = 7497 (main) / 13797
(w3c) / 13268 (d2) / 12875 (d3). Additionally there are **two different `[[check]]
name="weil_form_enclosure"` entries** with different groups (`quick` on w3c, `flint` on
tool-weil) pointing at different example islands. These are add/add conflicts that git will not
resolve sensibly. Merge order matters: land `tool-interval-gram-inertia` and
`tool-weil-form-enclosure` (the dedicated, CI-gated tool branches) FIRST, then rebase w3c and d2
onto them and delete their private copies, reconciling the registry stance to a single value per
emitter.

**C1 (mechanical). Eight branches all edit the same four registry files.**
`src/telperion/certify.py`, `src/telperion/emitter_sensitivity.py`,
`src/telperion/__init__.py`, `src/telperion/negctrl_adapters/__init__.py`. Each adds its own
kind. Conflicts are textual and resolvable by taking all additions; after resolution, re-run
`pytest tests/test_emitter_registry.py tests/test_certificate_sensitivity.py`, which is the
gate that actually checks the merged registry is coherent.

**C2 (mechanical). `telperion/telperion.toml` and `.github/workflows/telperion-lean-e2e.yml`.**
Six new `[[check]]` entries land: `twofreq_offline`, `exp_laurent_deficit`, `exp_enclosure`,
`disjoint_discs`, `gram_inertia`, `shape_audit`, plus the contested `weil_form_enclosure`.
Five new CI jobs land: `twofreq-offline-compiles`, `exp-enclosure-compiles`,
`disjoint-discs-compiles`, `gram-inertia-compiles`, `weil-form-enclosure-compiles`.
Remember the `MANIFEST INCOMPLETE` rule: a new `generate.py` that is not listed fails CI.
Also `telperion/README.md`, `docs/NEW_EMITTERS_SUMMARY.md` and
`docs/SECOND_PASS_EMITTER_CATALOG.md` are each touched by two or three branches.

**C3 (mechanical). `examples/rvm_bridge/generate.py`** is edited by both w2c-assembly and
w3c-goal-weil-membership (the latter for the MMDefs second-copy guard, check (7)).

**C7 (mechanical). `missions/mirrormere/attempts.jsonl`** gets one appended line from each of
nine branches (two from torus-ladder-t1), all at end-of-file. Ten trivial append conflicts.
Resolve by concatenation in merge order, then run `telperion mission verify mirrormere`.

**C8 (process). Attribution trailers are inconsistent** and this was verified from git, not
inferred: four commits end `Co-Authored-By: Claude Fable 5.1` (twofreq-offline-emitter,
w3c-goal-weil-membership, tool-interval-gram-inertia, d2-weil-gram-trace) and eight end
`Co-Authored-By: Claude Opus 5 (1M context)` (the rest, including this report's own commit).
The campaign brief mandated the Fable line; the live harness reminder mandated the Opus line and
changed mid-run. This is a harness-level change, not worker error. Decide one line at reconcile;
do not rewrite history over it.

**C9 (environment). Disk.** The run filled the root volume to 0 bytes, which is the direct cause
of three of the four unverified verdicts. The 7.8 GB `.lake` at
`.../arda-mm-w3c-goal-weil-membership/telperion/missions/mirrormere/lean/.lake` is the single
biggest addition and still exists. Root is back to 106 GB free. **The three disk-blocked gates
(w3c full dynamic audit, tool-weil-form-enclosure `generate.py --check`, d2 Probes build) should
simply be re-run now that there is space** -- that alone would likely move two or three items to
verified.

---

## 4. Recommended merge order

1. `mm/tool-interval-gram-inertia` -> `origin/main`. Zero registry touch, fully verified.
2. `mm/tool-weil-form-enclosure` -> `origin/main`, **after** re-running its drift check.
3. `mm/w2c-assembly` -> `origin/main`; grant `MM_zeta_ordinates_not_uniformly_discrete` once
   `rvm-bridge-compiles` is green post-merge.
4. `mm/mm-d3-certified-height-weil-bound` -> `origin/main`, after correcting finding D1.
5. `mm/d2-weil-gram-trace` -> `origin/main`, after correcting the node title and dropping its
   private emitter copies in favour of steps 1 and 2.
6. `mm/w3c-goal-weil-membership` -> `origin/main`, after the full dynamic gate re-run, dropping
   its private `weil_form_enclosure` copy, and adding the now-registered D2/D3 nodes to
   `depends_on`.
7. The six million-turing branches: rebase each onto `3b31737b5`, resolve C4 first, then land
   `torus-ladder-t1`, `offline-disjoint-discs`, `recurrence-deficit`, `exp-enclosure-emitter`,
   `twofreq-offline-emitter`, `mm-euler-factor-offline` in that order (cheapest conflict surface
   first). All their grants are deferred to the million-turing -> main reconcile.

---

## 5. THE WALL -- stated separately, as required

`MM_zeta_comb_membership`, as re-authored by item 1.10, is **RH-equivalent** (Weil 1952;
Bombieri 2000, who states the criterion on exactly `C_c^infinity`). Its open obligation is:

```
theorem zeta_comb_membership :
    forall g : R -> C, WeilExplicit.IsWeilTest g ->
      0 <= (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by sorry
```

This node is registered `kind = goal`, `status = draft`, **permanently**: it is never attempted,
never decomposed, and no amount of progress on the nodes below it constitutes progress on it.
Nothing in this run reduces it, weakens it, or brings it closer. It is registered so that the
program has an honest name for what it is not doing. Two further known walls are recorded as
prose only and deliberately left unregistered: the Selberg-class / B-mult-twisted growth-carrier
form of the same membership clause (substrate-blocked -- Mathlib has no Fourier transform of
measures, no almost-periodicity predicate, no `prod_p S^1` restriction), and `W_temp`, which the
literature review grades as a program conjecture in its own right.

Everything in section 6 below is instrument-building *beneath* this wall. conjecture1_proved = False.

---

## 6. What Mirrormere still needs, ranked

### 6.1 Ranked (highest value first)

1. **Re-run the three disk-blocked verification gates.** Cheapest possible upgrade: it plausibly
   converts tool-weil-form-enclosure, w3c and d2 from unverified to verified without touching a
   line of mathematics. (C9.)
2. **Resolve C4, C5, C6 and land the tool branches.** Seven new emitter kinds are stranded across
   twelve un-pushed branches with three-way duplicate files. Until this is done the campaign has
   no single coherent emitter registry, and `tests/test_emitter_registry.py` has never run
   against the merged result.
3. **The million-turing -> main reconcile, and the grant pass behind it.** Nine nodes are
   proof-linked-but-open purely because their artifacts live on the climb branch. This is the
   single largest gap between what is actually proved and what the registry says. It was already
   pending before this run; this run added to it rather than reducing it.
4. **`mm-dictionary-reaudit`** (surveyed, not run). `MM_torus_section_dictionary` is stuck at
   `status = "draft"` and therefore ungrantable, blocking the T1 rung that is otherwise proved.
   A blind re-audit promoting draft -> open is a small, well-scoped item.
5. **`exists_measured_weil_test`** -- the bridge from Mathlib's `ContDiffBump` to the exact bump
   profile the Arb backend evaluates. Without it the whole `weil_form_enclosure` numeric channel
   is hypothesis-gated and cannot be composed with `limit_explicit_formula` at any concrete test
   function. This is the load-bearing gap in the run's most ambitious tool.
6. **The D2 proof-side lemma pack** (five named lemmas on the rvm_bridge island: `crossCorr`
   preserves `IsWeilTest`, `crossCorr_swap`, `weilKernel_crossCorr`, `weilForm_conj_reflect`,
   bilinearity of `archSide`/`primeSide`). D2 is authored but entirely unproved; these five are
   the whole route.
7. **The D3 sub-obligations**, of which exactly one is a genuine Mathlib gap:
   `riemannZeta sigma != 0` for real `sigma in (0,1)` is **not** in Mathlib v4.32 and needs the
   classical `eta(s)/(1 - 2^{1-s})` argument. The other five are Fubini/integration-by-parts work
   or already available.
8. **Toolchain unification.** The campaign now spans v4.32.0 (quasicrystal, zeta_zero_localization),
   v4.33.0-rc2 (rvm_bridge) and v4.34 (li_positivity, rh statements). W2c was closed only by a
   cross-toolchain assembly and `port_match.py` was written to cope. This is accumulating
   interest.
9. **`mm-speiser-box-reauthor`** (surveyed, not run). `MM_speiser_box_probe` remains UNLINKED and
   un-reauthored.
10. **Negative-control wiring for the two d2-minted emitter kinds**, currently
    `NEG_CONTROL_DECLARED_UNWIRED` / not-applicable-with-reason. Honest, but it leaves two kinds
    outside the harness that the rest of the registry is held to.
11. **`build_mmdefs.py`**, the structural guard against `MMDefs.lean` drifting from its island
    sources. Three branches edited `MMDefs.lean` independently in one day, which is exactly the
    failure mode it prevents.
12. **Complex-Hermitian `interval_gram_inertia`** via the `posIndex_realEmbed` doubling lemma,
    and the `|x| > 1` halving extension for `exp_enclosure`. Both are refused-by-design today;
    both are small.

### 6.2 Structurally blocked, do not queue

* The Selberg-class growth-carrier membership form (no Mathlib substrate; see section 5).
* Definite boxes (`p=0`/`q=0`) in `interval_gram_inertia` -- needs an `n x 0` matrix literal
  convention, which is a Lean ergonomics problem, not mathematics.

### 6.3 Surveyed but never run, for the record

25 items were surveyed, 8 dropped by skeptics, 12 executed. The remaining 5:
`mm-goal-w3c-statement` (superseded by the sharper `mm-w3c-goal-weil-membership`),
`tool-exp-laurent-identity` (folded into `mm-recurrence-deficit`, which built the emitter),
`tool-selfinversive-offline-mode` (folded into `mm-euler-factor-offline`, which built the cert
mode), **`mm-dictionary-reaudit`** (genuinely not done -- see rank 4) and
**`mm-speiser-box-reauthor`** (genuinely not done -- see rank 9).

The 8 dropped items were `tool-disjoint-discs-instance`, `tool-deriv-empty-band`,
`mm-t3-section-defect-rungs`, `tool-section-defect-rung-emitter`, `tool-hermite-biehler-pair`,
`tool-pair-correlation-count`, `gram-inertia-emitter`, `lee-yang-circle-emitter`. Two of the
eight came back anyway by another route: the disjoint-discs instance emitter was minted inside
the prove item, and the Gram-inertia capability landed as the richer `interval_gram_inertia`.
The remaining six -- notably the T3 defect-instrumentation rungs and the Hermite-Biehler pair
certificate -- are still unbuilt and are the natural next tool wave.

---

## 7. Standing hygiene facts

* No branch pushed, no PR opened, all twelve worktrees intact under `/Users/peterwmurphy/arda-mm-*`.
* No `.lake` deleted; no `lake exe cache get` run in a symlinked island. The one legitimate
  `cache get` (mirrormere statements island, where no cache existed) is the 7.8 GB in C9.
* No file under `telperion/missions/` was hand-edited; every registry change went through the
  mission CLI.
* No emoji in any Lean or Python file delivered by this run (checked by at least two verifiers
  over their own branches).
* Every delivered theorem is sorry-free. Every `sorry` that exists is in a registry `draft`
  statement file or a `Probes/*_WIP_PROBE.lean`, outside `defaultTargets` and outside every
  axiom guard.

conjecture1_proved = False
