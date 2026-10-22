# Closure audit (T4) and frozen-tree manifest (T5): design note (2026-10-22)

Two pipeline tools, not emitters. They come from the second phase of the CN-1 emitter survey,
where they ranked second after the root-bracket table: every Lean island in this repository
makes a "closure clean" claim of some kind, and until now nothing in Telperion could check
one at the level of the kernel environment. `telperion/audit.py` reads Lean *source* for
`sorry`, a smuggled `axiom`, an empty tactic block, a reflexive statement; the missions
registry's `closure_clean` flag is a *recorded* boolean about the dependency graph between
nodes. Neither looks at what a proof term actually reaches. The closure audit does. The
manifest is the thing that makes an audit, a build and an independent check describe the
same tree.

The templates were the hand-written tools of the CN-1 verdict-of-record chain: a 100-line
`CoreM` metaprogram that walked the main theorem's closure, and a shell manifest of md5s with
a before/after diff around the chain. Both are generalised here, parameterised, tested, and
given a CLI. Nothing in this note is a claim about any theorem; `conjecture1_proved = False`
stays where it is.

## What was built

| Piece | Where |
| --- | --- |
| Lean audit template + renderer + output parser + runner | `src/telperion/closure_audit.py` |
| Manifest builder, verifier, text rendering | `src/telperion/freeze_manifest.py` |
| CLI | `telperion audit-closure`, `telperion freeze-manifest`, `telperion verify-manifest` (`src/telperion/cli.py`) |
| Worked example (a target library + a negative control) | `examples/closure_audit/` |
| Tests on fixtures (real audit outputs from v4.32.0 and v4.34.1; a tmp git project for the manifest) | `tests/test_closure_audit.py`, `tests/test_freeze_manifest.py` |
| CI | `closure-audit-compiles` in `.github/workflows/telperion-lean-e2e.yml` |

## The closure audit

### What it does

`render_audit_script(AuditSpec)` produces one Lean file. Its parameters are baked in as Lean
definitions, so the file is self-contained and can be committed next to the project it
audits (the example commits two). Run with `lake env lean <file>` inside a *built* Lake
project, it prints a human listing interleaved with machine-readable lines prefixed `@@`;
`parse_audit_output` turns those into an `AuditResult`, and `run_closure_audit` does the
whole round trip, with an optional command prefix for a build lock or a sandbox.

The spec:

- `imports`: the modules to import so the targets exist. Import the negative-control module
  too, when there is one: that is what makes the absence check below non-vacuous.
- `targets`: the theorems (or definitions) whose closure is taken. Several targets give the
  closure of their union; axioms are reported per target.
- `library_roots`: root modules whose constants are *counted*, not listed. Default: `Init`,
  `Lean`, `Std`, `Batteries`, `Mathlib`, `Aesop`, `Qq`, `ProofWidgets`, `Plausible`,
  `LeanSearchClient`, `ImportGraph`, `Lake`, `Cli`. Everything else is listed constant by
  constant, grouped by module.
- `scan_patterns`: lower-cased substrings searched in every closure constant's name and
  module, and separately in every module name of the whole environment. Hits are reported
  and never fail the audit on their own (the CN-1 run had eleven hits, all its own names plus
  a Mathlib PID criterion); the CLI's `--fail-on-scan-hit` turns them into a failure when a
  project wants that.
- `absent_constants` (default `sorryAx`) and `absent_module_prefixes`: must not be in the
  closure. A present one is a failure.
- `allowed_axioms` (default `propext`, `Quot.sound`, `Classical.choice`, the same
  `CLEAN_AXIOMS` the Comparator bridge uses): `collectAxioms` per target, any other axiom is
  a failure. `native_decide` shows up here as an axiom outside the set (on v4.32.0 a
  generated per-theorem axiom named `<theorem>._native.native_decide.ax_1_1`, as the example's
  negative control records; on later toolchains `Lean.ofReduceBool`); a smuggled `axiom`
  shows up by name.
- `include_recursors`: see below.
- `closure_out`: optionally write the full `module<TAB>constant` listing to a file.

The walk is the CN-1 one, written out explicitly rather than through `value?`: for every
constant reached, its type; for a theorem, definition or opaque, its value; for an
inductive, its constructors and its `.rec`. The verdict is `PASS` or `FAIL`; a missing target
is a failure (and the walk still runs over the targets that exist, so the report is useful).

Two extras the CN-1 script did not have:

- a census of the *whole environment's* modules by root, and the list of non-library modules
  that are imported but contribute nothing to the closure (`unused_nonlib_modules`). This is
  open check 8 of the survey ("should the audit also walk module imports?") answered in the
  cheap form: it does not walk the import graph, but it tells you which imported non-library
  modules the closure never touched. In the example, `ClosureAuditExample.Tainted` appears
  there: imported, absent from the closure.
- the Lean version string and the protocol version in the output, so a stored JSON says what
  produced it.

### The recursor option

An independent reviewer re-walked the CN-1 closure with Lean's own
`ConstantInfo.getUsedConstantsAsSet` and got a count that differed from ours only by the
`*.rec` constants our walk adds for every inductive. That walk is `type + value?
(allowOpaque := true)`, plus constructors for an inductive, plus `all` for a recursor it
happens to reach; it adds no recursor on its own. Both walks are rendered into every script
and `include_recursors` chooses at run time (`--no-recursors` on the CLI). Measured on the
same one-theorem Mathlib target:

| Lean | recursors on | recursors off |
| --- | --- | --- |
| v4.32.0 | 629 (three-target run; two targets missing) | 571 |
| v4.34.1 | 630 | 573 |

Same verdict, same axioms, smaller count without the recursors. The default keeps them: a
recursor is a kernel constant the inductive brings along, and the larger number is the
honest size of what the kernel has to trust. Use the other mode to compare with a reviewer
who used `getUsedConstantsAsSet`.

### Version range

The script uses `Expr.getUsedConstants`, `ConstantInfo.getUsedConstantsAsSet`,
`collectAxioms`, `Environment.header.moduleNames`, `getModuleIdxFor?`, `Std.HashMap` and
`NameSet` (a `Std.TreeSet`), all present in the toolchain sources of v4.32.0, v4.34.1 and
v4.35.0 (checked by grep). It was run on v4.32.0 (the Telperion example pin, through an
existing built Mathlib) and on v4.34.1 (an existing built project). It has not been run on
v4.35.

### What it guarantees, and does not

Guarantees, for the environment it ran in:

- the closure count and census by root are exact for the walk described;
- every constant outside the library roots is listed by name and module;
- a listed absent constant or module prefix is genuinely not reachable from the targets
  through types and values;
- the per-target axiom list is what `#print axioms` would print, compared mechanically to
  the allowed list.

Not guaranteed:

- **It audits the elaborated environment of this build, not an exporter's or a second
  kernel's view.** Comparator and `lean4export` read the same `.olean` files only if the
  tree did not change between the two runs. That is a *condition*, and the manifest below is
  how you record that it held; the audit alone cannot know.
- **Import-level hygiene beyond names.** The module scan is over names; the unused-module
  list says what the closure did not reach, not why the import is there.
- **The content of library constants.** A census counts Mathlib; it does not re-verify it.
  Under the CN-1 rules as amended, constants from the vendored OpenAI packages were admitted
  on the same footing: the audit lists them, it does not vouch for them.
- **A renamed argument.** The scan is a substring match. A proof that reaches a forbidden
  result through a constant named something else is invisible to it. The closure *listing*
  (`closure_out`) is there so a reader can look at every non-library constant by hand.
- **Compiled code.** `implemented_by` and `extern` bodies are not inspected; `native_decide`
  is caught only because it leaves an axiom.
- **That the targets say what you meant.** Statement review is a different job
  (`port_match.statement_match`, the Comparator's challenge module). The audit prints each
  target's type so that review has the text in front of it.

## The frozen-tree manifest

### What it records

`freeze_manifest(project_dir, ManifestOptions)` returns a JSON document:

- `files`: every source matching the include globs (default `**/*.lean`, with `.lake/` and
  `.git/` always excluded), each with sha256, md5 and size. A symlink is recorded as a
  symlink (its target string) and hashed through to the target's bytes, which is what the
  CN-1 manifest did by hand for its one symlinked file.
- `lake_files`: `lakefile.lean` / `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.
- `toolchain`: the `lean-toolchain` string and, when the named elan toolchain is installed,
  the sha256 of its `lean` binary. The CN-1 manifest hashed only the file; its review noted
  that the binary was unpinned. Off with `--no-toolchain-binary`.
- `dependencies`: every package in `lake-manifest.json` (type, url, rev, inputRev) and, for
  each package directory present: git HEAD; whether tracked files are modified; the sha256 of
  `git diff HEAD` when they are; every untracked file (`git ls-files --others
  --exclude-standard`) with its hash; optionally every git-ignored file outside `.lake/`
  (`--include-ignored`, because the review noted the default misses them); and, when a patch
  is supplied for the package (`--patch PKG=FILE`), the patch's hash, the result of `git
  apply --check -R` ("tracked tree equals HEAD + patch"), and for each untracked file
  whether the patch creates it (a `+++ b/<path>` header whose `---` side is `/dev/null`).
  This is the v2 addendum of the CN-1 manifest, generalised.
- `tools` and `extras`: anything else the caller names by label (`--tool nanoda=PATH`,
  `--extra real_cfg=PATH`): the checker binary, the exporter, the second kernel, the sandbox
  shim, the Comparator JSON configs. The review found the configs and the shim missing from
  the CN-1 manifest; here they are first-class.
- `options`: the parameters, recorded so `verify` recomputes with the same ones.
- `digest`: sha256 of the canonical JSON of everything except the timestamp. Two manifests
  of the same state compare equal by one string; `load_manifest` refuses a file whose digest
  does not match its content.

`verify_manifest(manifest, project_dir)` re-freezes with the recorded options and returns a
diff (added / removed / changed entries, old and new digest). The CLI exits 1 on any change.
`--tool LABEL=PATH` re-points a tool whose binary moved; content is still compared.

The pattern this supports is the one the CN-1 chain used: freeze, run (build, independent
check, closure audit), verify, keep all three. The CI job for the example does exactly that
around its own build and audits.

### What it guarantees, and does not

Guarantees: the hashes are of the bytes present at freeze time, by the named algorithms;
`verify` reports any byte change in anything the manifest covers.

Not guaranteed:

- **Behaviour.** A tool with the same hash is the same bytes; the manifest says nothing
  about what it does, or about whether a sandbox was in force.
- **Build products.** `.olean` files are not hashed. A tampered olean that `lake` considers
  up to date is outside the manifest; rebuild from clean if that is the threat.
- **Dependency history and remotes.** A package is pinned by HEAD, diff and untracked files,
  not by re-fetching anything.
- **Ignored files by default.** `--include-ignored` exists because the default follows git's
  own notion of "other" files.
- **Path hygiene.** Paths are recorded as given. Use relative paths or labels for anything
  that will be committed; the tool does not scrub a home directory out of a path.
- **What ran in between.** `verify` says the tree is the same; the logs of the chain say what
  happened on it.

## The example and its negative control

`examples/closure_audit/lean/ClosureAuditExample/Example.lean` has four honest theorems
(`norm_num` primality of 101, `Nat.Prime.two_le`, an additive inequality, `decide` over a
four-element prime list). `Tainted.lean` is the negative control: a false `axiom fake_fact :
Nat.Prime 1001`, a theorem through it, a `sorry`, and a `native_decide`. `generate.py`
renders two specs and two scripts:

- `Audit.lean`: the honest theorems, with **Tainted imported into the environment** and
  `ClosureAuditExample.Tainted` declared absent. Must PASS, with the tainted module listed as
  imported-but-unused.
- `AuditTainted.lean`: the three tainted theorems. Must FAIL on three independent counts:
  `sorryAx` in the closure, constants from the forbidden module in the closure, and axioms
  `fake_fact`, `sorryAx` and the `native_decide` axiom outside the allowed list.

Run locally on v4.32.0 (the log is kept with the PR notes): the clean audit PASSED with
3228 constants (Init 2775, Mathlib 447, Batteries 1, ClosureAuditExample 5), `sorryAx`
absent, 0 Tainted constants, Tainted listed as imported-but-unused; the tainted audit
FAILED with five failure lines (`sorryAx` present; 5 Tainted constants; `via_axiom` uses
`fake_fact`; `via_sorry` uses `sorryAx`; `via_native` uses
`via_native._native.native_decide.ax_1_1`); the manifest taken before the chain verified
UNCHANGED after it.

Locally the library was built against an existing v4.32.0 Mathlib through a local-only
symlink of `.lake/packages` (never committed); the committed `lake-manifest.json` pins the
same revisions every other example pins, so CI's `lake exe cache get` resolves identically.

## Integration with `closure_clean`

REVIEW_E G3 is right that the missions `closure_clean` flag is a recorded boolean, not a
computed one. Reading `missions/verify.py` shows why it cannot simply be *replaced* by this
audit: for a reduction node the flag is a fixpoint over the node dependency graph (every
`depends_on` target proved and itself clean), and for a direct node the stored flag is
authoritative on purpose, because a controller ruling can leave it `False` for an artifact
whose kernel authority lives on another island. The code comments mark changing that
semantics as an owner's decision (ascent-plan ops F1-3/F1-4). So this PR does not touch it.

What fits the existing registry shape is a **sidecar record**, like `[comparator]` and
`[ci_record]`: a `[closure_audit]` table on a node holding the artifact sha256 at audit
time, the targets, the Lean version, the closure size, the verdict, the absent lists and
scan patterns used, the allowed axioms, and the sha256 of the stored JSON result. `verify`
would then warn (or, under `--strict-provenance`, fail) when the artifact on disk no longer
has the hash the audit saw, exactly as `comparator_staleness` does today, and
`provenance-report` would show which proved nodes have no kernel-level census. Writing it
would be `telperion mission closure-audit-record SLUG --result audit.json`. This is proposed,
not built: it adds a table to the public registry schema, and the governance notes in
`verify.py` make that a decision for the owner, not for a tooling PR.

## Open items

- Run the template on a v4.35 toolchain once an island pins one; the API grep says it will
  compile, the run has not been done.
- A `--compare` mode that takes two JSON results (ours and a reviewer's) and reports the
  set difference of constants, so the recursor-only discrepancy can be shown constant by
  constant rather than by count.
- The sidecar record above, if the owner wants it.
