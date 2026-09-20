# Telperion Missions — end-to-end architectural audit, 2026-09-19

*`conjecture1_proved = False`. This audit proves no mathematics. It asks one question of the
registry that records what the RH campaigns have proved: **what does `status = "proved"`
actually mean, mechanically, end to end, and where can it be wrong?** Findings are from
execution against the real code, not inspection. Every attack below was run in a throwaway
campaign; nothing under `telperion/missions/` was touched during the audit.*

**Headline: the live corpus is clean.** All 47 proved nodes and the one refuted node were
scanned against every mechanism found. No false claim exists today. What follows is about
what was *possible*, and what is no longer.

---

## 1. The trust chain, link by link

A node reaching `proved` rests on seven links. The audit's job is to ask what enforces each.

| # | Link | Enforced by | Status |
|---|---|---|---|
| 1 | The registered statement is well-formed Lean | `mission-statements-compile`, matrix over all four campaigns | **CODE** |
| 2 | The statement file still matches the node | `regen_diff`, in the battery and (new) at the gate | **CODE** |
| 3 | The statement says what its title claims | nothing | **PROSE** (§4) |
| 4 | An artifact declares that statement and proves it | `statement_matches`, hardened §3 | **CODE** |
| 5 | The artifact is finished Lean | incompleteness markers: `sorry`, `admit`, `native_decide`, and now `axiom`/`unsafe` | **CODE** |
| 6 | Something compiles the artifact | `coverage.py`, island-level | **CODE** (§5 for the theorem-level gap) |
| 7 | The compiled theorem has clean axioms | each island's own axiom guard | **CODE where the guard names it** (§5) |

Links 1, 2 and 7 predate this audit. Links 4, 5 and 6 were materially weaker than the
documents claimed and are the subject of §2 and §3. Link 3 is, and probably must remain,
human judgement — which is why §4 matters more than any single code fix.

---

## 2. What the gate did not ask (2026-09-18, closed)

Before this week the gate checked three things: the artifact exists, the artifact's text
contains the node's statement, and nothing else. It did not ask whether the artifact *proves*
the statement, nor whether anything *compiles* it. Two incidents followed directly:

* **Two rh nodes proved against Lean nothing had ever compiled.** `ZeroFreePolylog` and
  `ZeroFreeElementary` were imported by nothing, absent from `defaultTargets`, and outside
  every axiom guard's closure. Three independently built worktrees had no `.olean` for
  either. Both compile fine — the theorems were real, simply never verified by the pipeline.
* **All six proved anduril nodes in an island no workflow built.** The entire
  `zeta_reflection` island was referenced by no CI job at all.

Closed by: the incompleteness scan (`sorry`/`admit`/`native_decide` in code, comments and
strings stripped), and `coverage.py`, which asks whether some CI job runs `lake build` in the
island the artifact lives in, wired into **both** the gate and the battery that runs in the
required `unit` job.

---

## 3. The nine false-`proved` paths (2026-09-19, eight closed)

Driven against the real gate. All nine were confirmed by execution; none was exploited.

| # | Path | Closed |
|---|---|---|
| 1 | **Suffix extension.** Containment was a prefix match on the conclusion, so `NoZero s ∨ True` satisfied a node claiming `NoZero s`, and `RH → RH` satisfied `RH` | yes — a match must be followed by the proof body |
| 2 | **Self-supplied axioms, name shadowing.** `axiom cheat : …` then `theorem hard := cheat n` | yes — `axiom`/`unsafe` in declaration position are markers |
| 3 | **Coverage bypass by path string.** `../examples/wired/lean/../../unbuilt/lean/U.lean` credited to the built island | yes — attribution uses the resolved path |
| 4 | **The refutation branch paid none of the checks the proof branch gained** | yes — both hoisted above the branch |
| 5 | **Statement drift at grant.** `regen_diff` ran only in the battery; a hand-edited statement with a re-forged hash was grantable | yes — the gate calls it |
| 6 | **No readback at grant.** A node set `open` by hand could be granted with none on record | yes |
| 7 | **Granting destroyed data.** `save_node` dropped `proof.fidelity_note`, the field recording where a node was actually verified | yes — modelled |
| 8 | **A disabled `lake build` vouched for an island** | yes — literal-false `if:` skipped |
| 9 | **Vacuity.** `theorem p : True` is grantable, as is a one-token statement | **NO — see §4** |

Finding 3 was introduced by the coverage fix itself, hours earlier. Finding 8 is the same
shape: a check that counts evidence which does not exist.

**A note on the two self-inflicted bugs.** The coverage checker also shipped, briefly, with a
worse defect than any it was written to find: it swallowed a missing PyYAML and answered
"nothing is built", failing every proved node at once. The required `unit` job is exactly such
an environment. The repair was not just the dependency — a checker that degrades into a
confident wrong answer is worse than one that admits it cannot parse, so there is now a
dependency-free fallback that a test holds equal to the precise path, and a guard that raises
rather than reporting a catastrophe. Its first version then misfired on a repo whose build
steps are all legitimately disabled, which is the same over-eagerness in the opposite
direction. Both are recorded here because the pattern is the lesson.

---

## 4. What the machine cannot check, and who is checking it

Vacuity (path 9) cannot be closed by code. Nothing can decide whether
`theorem RH_conjecture : RiemannHypothesis` is the statement its title claims, or whether a
registered proposition is trivial. The project's answer is the **read-back**: an independent
session renders the formal statement into prose, and that testimony promotes a node from
`draft` to `open`.

That ceremony is real and it works — the testimony documents in `telperion/docs/` are
substantive, and one of them caught a statement that was definitionally `rfl`. But:

* `promote_to_open` raises only if a readback is **absent**. Nothing checks who wrote it.
* `--auditor` is free text taken straight from the command line into the stored record.
* Across 58 readbacks there are 14 self-declared auditor labels, and across every node commit
  in the repository there are three git identities.
* The independence requirement ("the renderer must not be the statement's author") lives in
  `MISSIONS_DESIGN_2026-09-11.md` §8 **only**. It is absent from the how-to that sessions
  actually read, and enforced nowhere. See §4d.

So the single strongest link in the chain is the one with no mechanism behind it. This is not
a hypothetical worry in a project where the authors, the auditors and the integrators are all
autonomous sessions, and where a session can spawn the subagent that audits its own work.

**Recommended, not implemented here** (it needs a decision, not just code): record the grant's
provenance — a `[grant]` block carrying the artifact digest, the date and the identity the gate
actually saw — and record the statement's author at creation so the gate can refuse a readback
whose auditor matches it. Neither makes self-certification impossible; both make it *visible*,
which is the achievable goal.

---

## 4b. The data layer: three ways to corrupt the registry, all closed

Driven with real concurrent processes, not inspection.

**Writes were not atomic, and a torn file could read back as a valid node.** `save_node`
truncated in place. Under two writers and two readers, 1325 of 8000 reads saw an empty file
and 399 saw torn TOML. Most torn reads fail loudly — but an exhaustive byte-prefix scan of
all 66 live node files found **201 truncation points that load as a VALID node with a field
silently missing**, `readback` among them in 64 of the 66. Because the registry reads,
replaces one field and writes back, a session reading a torn file mid-write permanently
erased the read-back, which is the record gating promotion. All seven writers now use temp
file plus `os.replace`.

**Claims did not exclude.** Six racing processes each returned a claim naming themselves in
one of thirty trials, and a racing stale-steal left a torn claim file that broke every claim
operation in the campaign. Now created `O_CREAT|O_EXCL`; re-probed with eight processes over
twelve trials, exactly one winner every time.

**Granting destroyed hand-written evidence.** Any key the schema did not model was dropped on
save. A live node carries a `[nonvacuity]` table and a `proof.fidelity_note` recording that
its proof is kernel-verified *locally and not on main CI* — precisely the kind of honesty
field whose loss matters — and any mutation erased 1978 characters of it without a word.

**Two parsers meant two truths.** `loads_toml` fell back to a hand-rolled subset parser when
`tomllib` was absent, so CI and an older developer machine could read the same file
differently, silently: extra spaces around `=` produced a key with a trailing space so the
field vanished; a dotted key became a top-level key so the proof was absent; a duplicated
`[proof]` table from a botched merge was last-wins locally while CI rejected the file
outright. `tomli` is now a dependency and the fallback refuses the shapes it used to guess
at. All 74 live files parse identically under both today, so nothing on disk is corrupt.

The healthy part: `attempts.jsonl` appends are atomic even at 300 KB lines. Its weakness was
swallowing malformed lines anywhere in the file, so recorded work vanished from every digest;
skipped lines are now counted and surfaced.

---

## 4c. The operator surface: what an agent can actually do

Seven mutating subcommands. Only `grant` carried a real gate.

| Command | Was validated by | Now |
|---|---|---|
| `claim` / `release` | node open, TTL staleness | plus exclusive creation |
| `add` | slug uniqueness, kind enum, non-empty statement | unchanged — §4 |
| `audit` | status is draft, readback non-None | plus non-empty text and auditor |
| `link` | two enums | plus artifact must exist, and refuses to repoint a proved node without `--force` |
| `attempt` | verdict enum | plus malformed lines surfaced |
| `grant` | the full gate | §2, §3 |

The MCP surface is clean and is the one surface with no finding against it: only
`mission_status` and `mission_open_leaves` are exposed, both read-only. An agent must use the
CLI or edit files by hand.

**`open-leaves` would have crashed on the cross-campaign dependency form introduced this
week** — the command the how-to tells every session to run first. No live node uses a
qualified reference yet, so it was latent. Fixed.

---

## 4d. The self-certification measurement

§4 said the read-back is the link with no mechanism. The data says it is also, already, the
normal case:

* Of 47 proved nodes, **37 carry a read-back whose declared auditor is the same migration or
  catch-up session that registered them**, many self-describing as "verbatim-extract
  precedent" in the auditor string itself.
* **Ten** have a `blind-auditor` read-back backed by a testimony document.
* The distinct auditor values are self-assigned labels. Git authorship carries no signal:
  every commit touching the registry belongs to one of two identities of the same person.

And the likely reason is a documentation gap rather than shortcutting. The independence rule
lives in `MISSIONS_DESIGN_2026-09-11.md` §8. The document a session actually reads first is
`MISSIONS_HOWTO.md`, whose entire treatment of the ceremony is one line that never mentions
independence or blindness. **A session that reads the how-to and audits its own node has
followed the instructions it was given.**

The cheapest repair is to copy that sentence into the how-to. Beyond that, two non-blocking
changes make self-certification visible rather than impossible: a `--testimony PATH` flag on
`mission audit` that must resolve and is hashed into the read-back, and a battery warning
when a node's auditor string matches a session that logged attempts against that same node.
Real independence is not enforceable in code here — any identity an agent can supply for
itself it can supply for another — so visibility is the achievable goal.

---

## 5. Seams that remain open

**Guard coverage is island-level, not theorem-level.** `coverage.py` asks whether the island
is built, not whether *this theorem* is among its guard's `#print axioms` anchors. Measured:
36 of 47 proved nodes have their theorem named in a guard. `MM_bragg_defect_witness` and
`MM_recurrence_deficit_eq_excess` are named in **no guard anywhere**. Nine more are in
`proof/formalization/`, covered by `proof-lean` — which has been red since 2026-09-12 (§6).

**Mirrored definitions are unprotected.** 17 of 47 proved nodes have statements whose meaning
depends on a definition the artifact declares locally, and only 2 of 94 islands verify that
copy against the registry's vocabulary. I compared every one: **no drift exists today.** A
generic checker is harder than it looks — a first naive comparator produced two false alarms,
both from namespace resolution rather than divergence (`archSide` exists in two namespaces;
`checkLine` differed only by an `open`). Any real checker must be namespace-aware, which is
why the one island that does this does verbatim block comparison.

**Non-Lean artifacts skip every content check.** A `.json` frozen certificate is granted on
existence and containment alone.

**The `via = "reduction"` machinery has never run on a real node.** All proof links are
`via = "direct"`. The closure fixpoint and the new anti-cascade rule are untested against live
data, not because they are wrong but because nothing uses them.

---

## 6. Operational findings

**`proof-lean` has been red since 2026-09-12** and a previous fix did not work. The runner is
*killed*, not failed: `if: always()` does not run when a shutdown signal arrives, so the cache
save is skipped, so the next run starts cold. The build reaches 8,914 of 8,924 modules and dies
inside `R7Hyps.StarOfHubs.Cells*`, where single modules take up to 17 minutes. Those modules
date from 2026-08-21, so the trigger was the cache expiring, not new code. The fix that would
work is a time-boxed first pass that saves the cache *before* the danger zone, or moving those
cells to their own job. Nine proved bg nodes depend on this layer.

**The six anduril nodes are verified WEEKLY, not per-PR.** Wiring `zeta_reflection` into the
per-PR workflow was the first attempt and it failed: that island path-requires
`zeta_zero_localization/lean`, whose lakefile is the 54,280-line monolith the B2 migration
deliberately moved off the per-PR path, and the island genuinely uses it. It now has its own
scheduled workflow, on the same footing as the legacy box certificates. `coverage.py` counts
an island as built when any workflow builds it, so the nodes are covered — on a weekly
cadence, which is the honest description of that evidence and worth stating wherever those
six nodes are cited.

**Ten orphan islands remain** — Lean in the tree that no workflow builds. Down from 13. They
carry no node, which is why the battery reports them as a warning: erroring would turn the
check into an allowlist that rots. Surfacing them is what stops one quietly acquiring six
granted nodes, which is exactly what `zeta_reflection` did.

**Two wall-analysis islands** shipped 2026-09-19 with no CI job, one with no lakefile at all,
while a plan document cited their contents as kernel-checked. Both are now built and
axiom-guarded. Neither pins mathlib, so those builds are verified-at-run rather than
reproducible.

---

## 7. What to do next, in order

1. **Decide the identity question** (§4, §4d). Everything else is a smaller risk than a
   self-certified read-back, and no amount of gate hardening touches it. The one-line
   documentation fix — copying the independence sentence into the how-to — costs nothing and
   addresses the measured cause.
2. **Fix `proof-lean`** (§6). Nine proved nodes currently rest on a verification that has not
   completed in a week.
3. **Theorem-level guard coverage** (§5). Two nodes are guarded by nothing; the check is a
   natural extension of `coverage.py` but needs the artifact-outside-`examples` case handled.
4. **Generalize the mirrored-definition check** (§5) from the one island that has it. Latent,
   not live, and must be namespace-aware.
5. **Give non-Lean artifacts their own required check** (§5).
