# AUDIT TESTIMONY -- MM_torus_section_dictionary (mirrormere), 2026-09-22, auditor A1

**conjecture1_proved = False.** Nothing in this document, and nothing in the audited
artifact, proves the Riemann Hypothesis or makes progress on it. The RH-equivalent
nodes (`RH_conjecture`, `MM_zeta_comb_membership`) are out of scope and are mentioned
below only as DAG neighbours.

Blind audit, auditor 1 of 2, independent (no coordination with auditor 2). Worktree
`/Users/peterwmurphy/arda-goal-weil`, branch `mm/gauss-window`. No git commands were run,
no registry mutation was made (`mission status` and `mission verify` only, both read-only),
and no file under the worktree was changed except the creation of this testimony.

## 0. Verdict

The artifact is TRUE, PROVED, KERNEL-CLEAN, and byte-for-byte the registry statement.
It is also NOTATION ONLY: the theorem says that a two-term exponential sum written with
a plus sign equals the same sum written with a summation sign over `Fin 2`. It carries
zero mathematical content, uses no hypothesis, and uses nothing about a torus. The
2026-09-19 blind read-back verdict (HELD AT DRAFT, NOT to be granted as a rung) is
confirmed on every point that matters and is corrected on one immaterial detail
(section 5). The correct lead action is a policy decision, not a build: deprecate with
reason per WALL_BACKLOG_MAP R5, or hold at draft as plumbing; do NOT promote and grant.

Structured fields: `pass = true` (the artifact passes every mechanical and mathematical
check asked of it), `axioms_clean = true`, `statement_byte_identical = true`. `pass`
refers to the correctness of the proof artifact, NOT to grant-worthiness of the node.

## 1. What was audited

| Item | Path |
|---|---|
| Node | `telperion/missions/mirrormere/nodes/MM_torus_section_dictionary.toml` (status `draft`, kind `lemma`, `depends_on = []`, `[proof] via = "direct"`, `closure_clean = false`, readback recorded 2026-09-19) |
| Statement | `telperion/missions/mirrormere/lean/Statements/MM_torus_section_dictionary.lean` (sentinel sha256 `88b005abb1ab77e0`) |
| Vocabulary | `telperion/missions/mirrormere/lean/Statements/MMDefs.lean` (`twoFreq` verbatim from the island; `torusOrbit`, `linearTorusForm`, `expSum` AUTHORED) |
| Artifact | `telperion/examples/quasicrystal/lean/TorusSectionLadder.lean`, theorem `Quasicrystal.torus_section_dictionary` |
| Island | `telperion/examples/quasicrystal/lean` (toolchain `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0` = `81a5d257c8e410db227a6665ed08f64fea08e997`) |
| Guard | `telperion/examples/quasicrystal/lean/AxiomGuardQC.lean` line 88 (`#print axioms Quasicrystal.torus_section_dictionary`) |

## 2. Statement comparison (byte for byte)

The theorem block `theorem torus_section_dictionary ... :=` was extracted from both
files and compared raw and whitespace-normalized:

```
theorem torus_section_dictionary (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) :=
```

* raw bytes identical: **True** (200 bytes in each file, including indentation)
* whitespace-normalized identical: **True**
* the artifact's proof after `:=` is `by simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]`;
  the statement file's is `by` followed by the stub marker (as every statement file is).

The four definitions the statement depends on were compared the same way:

| Definition | MMDefs.lean vs artifact | MMDefs.lean vs island source |
|---|---|---|
| `torusOrbit` | raw identical | (authored; not in island source) |
| `linearTorusForm` | raw identical | (authored) |
| `expSum` | raw identical | (authored) |
| `twoFreq` | (artifact imports it) | raw identical to `TwoFreqRigidity.lean:40-42` |

So the statement, the artifact theorem, and every symbol in it denote the same terms
in the registry and on the island. The artifact's `namespace Quasicrystal` matches the
statement file's `open Quasicrystal`.

## 3. Mechanical gate predicates, re-run read-only through the library

Using `telperion.missions.verify` directly (pure functions, nothing written):

```
status: draft | via: direct | depends_on: () | readback recorded: True
artifact exists: True
normalized statement: theorem torus_section_dictionary (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) : twoFreq c₁ c₂ lam₁ lam₂ x = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x)
statement_matches: True
incompleteness markers: []
```

`mission verify mirrormere` (read-only battery): `verify [mirrormere]: OK`.

The only failing gate is the status gate: `grant_status` (`src/telperion/missions/verify.py:400`)
refuses any node whose status is not `open`, and the node is `draft`. `promote_to_open`
(`src/telperion/missions/registry.py:375`) would mechanically succeed (status is `draft`
and a readback IS recorded), which is exactly why this is a policy decision and not a
mechanical one: the recorded readback's own verdict says not to promote.

## 4. Kernel check (`#print axioms`) on a fresh build of the CURRENT artifact

No built copy of the island exists in this worktree; instead `quasicrystal/lean/.lake`
here is a root-owned SYMLINK (created 2026-09-22 01:30) to
`/Users/peterwmurphy/arda-million/telperion/examples/quasicrystal/lean/.lake`, not a
reflink copy. That sibling's `lake-manifest.json` is byte-identical to this worktree's,
its toolchain is `v4.32.0`, and its Mathlib package checkout is at
`81a5d257c8e410db227a6665ed08f64fea08e997`. However the sibling no longer carries a
`TorusSectionLadder.lean` source, and its `TorusSectionLadder.olean` dates from
2026-09-18 03:02, so that olean cannot be trusted as a build of the artifact as it is
today. I therefore did NOT run `lake env lean` against the stale olean and did NOT build
through the symlink (a `lake build` here would write into the sibling's shared tree).

Instead: a private APFS reflink copy (`cp -Rc`) of the sibling `.lake` plus this
worktree's current island sources was made in the session scratchpad (27 s, 13 GB
logical, ~0 physical), and `lake build TorusSectionLadder` was run there. Lake
trace-checked 2033 Mathlib jobs and compiled exactly two modules:

```
Built TwoFreqRigidity (8.6s)
Built TorusSectionLadder (1.6s)
Build completed successfully (2035 jobs).
```

Then a guard file importing only `TorusSectionLadder` printed:

```
'Quasicrystal.torus_section_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.twoFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.linearTorusForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.torusOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.expSum_eq_linearTorusForm_torusOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.torus_section_n2_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Quasicrystal.twoFreq_realRooted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fin.sum_univ_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`. The elaborated statement checks as
`∀ (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ), twoFreq c₁ c₂ lam₁ lam₂ x = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x)`.
The scratch copy was deleted afterwards; nothing in either worktree was modified.

CI coverage: the `disjoint-discs-compiles` job of `.github/workflows/telperion-lean-e2e.yml`
(push to `main` and pull requests touching `telperion/**`) runs a full `lake build`
of every default target (which includes `TorusSectionLadder`) followed by
`lake env lean AxiomGuardQC.lean` and fails on any `sorryAx` in the output. So the
guard line 88 is live, with the standing caveat (recorded elsewhere) that island CI
jobs are not required checks on the branch protection.

## 5. Definitional probes: where exactly is the content?

Each probe was elaborated against the fresh build.

| Probe | Goal | Result |
|---|---|---|
| P1 | node statement by bare `rfl` | **fails** (Type mismatch), confirming the 2026-09-19 readback |
| P2 | `simp [twoFreq, linearTorusForm, torusOrbit]` (no `Fin.sum_univ_two` named) | closes |
| P3 | the artifact's own script | closes |
| P4 | `unfold twoFreq linearTorusForm torusOrbit; rw [Fin.sum_univ_two]; rfl` | closes |
| P5 | `(∑ j : Fin 2, f j) = f 0 + f 1` by `rfl` | **fails** |
| P6 | `![c₁, c₂] 0 = c₁`, `![c₁, c₂] 1 = c₂`, `![l₁, l₂] 1 = l₂` by `rfl` | all close |
| P7 | both sides after the one rewrite, by `rfl` | closes |
| P8 | the identity at `c₁ = c₂ = 0`, `lam₁ = lam₂` | holds (no hypothesis is used) |

Reading: the ENTIRE non-definitional gap between the two sides is the single rewrite
`Fin.sum_univ_two` (P4, P5, P7). The vector-literal projections are definitional (P6),
and the default simp set closes the goal without even being told the lemma (P2,
because `Fin.sum_univ_two` is simp-tagged in Mathlib). The proof term printed by
`#print` is `of_eq_true (... Finset.sum_congr rfl ... Fin.sum_univ_two ... Matrix.cons_val_fin_one ...)`,
i.e. one sum unfolding and two literal projections.

One immaterial correction to the 2026-09-19 readback: it attributed the failure of
bare `rfl` to `add_zero` on ℂ. P5 shows the failure is upstream of that: the `Fin 2`
sum `∑ j, f j` does not unfold to `f 0 + f 1` at default transparency at all
(`Fin.sum_univ_two` has no trailing zero to discharge). The verdict is unchanged; if
anything the content is thinner than that readback said.

## 6. The mathematics, re-derived by hand

Definitions (all verbatim, section 2):

* `twoFreq c₁ c₂ lam₁ lam₂ x := c₁ · exp(lam₁ · x · i) + c₂ · exp(lam₂ · x · i)`
* `torusOrbit N lam x := (j ↦ exp(lam_j · x · i))`
* `linearTorusForm N c z := Σ_{j : Fin N} c_j · z_j`

Right-hand side at `N = 2`, `c = ![c₁, c₂]`, `lam = ![lam₁, lam₂]`:

```
linearTorusForm 2 ![c₁,c₂] (torusOrbit 2 ![lam₁,lam₂] x)
  = Σ_{j : Fin 2} (![c₁,c₂] j) · exp((![lam₁,lam₂] j) · x · i)     (unfold)
  = (![c₁,c₂] 0) · exp((![lam₁,lam₂] 0) · x · i)
      + (![c₁,c₂] 1) · exp((![lam₁,lam₂] 1) · x · i)                 (Fin.sum_univ_two)
  = c₁ · exp(lam₁ · x · i) + c₂ · exp(lam₂ · x · i)                   (literal projections, rfl)
  = twoFreq c₁ c₂ lam₁ lam₂ x.                                        (unfold)
```

That is the whole proof. Observations a number theorist would make:

* No hypothesis is used: not `c₁ ≠ 0`, not `c₂ ≠ 0`, not `lam₁ ≠ lam₂` (P8), and the
  identity is an identity of expressions, valid for every complex `x`.
* Nothing about a torus is used or asserted. For non-real `x`,
  `|exp(lam · x · i)| = exp(-lam · Im x) ≠ 1`, so `torusOrbit 2 lam x` does NOT lie on
  the 2-torus; the name overstates the object in exactly the way the 2026-09-20 second
  read-back of the sibling node flagged for the word "torus". No Kronecker, no
  rational independence, no cut-and-project hypothesis appears anywhere.
* The general-N identity `expSum N c lam x = linearTorusForm N c (torusOrbit N lam x)`
  is literally `rfl` in the artifact (`expSum_eq_linearTorusForm_torusOrbit`); the
  node statement is that identity at `N = 2` composed with the `twoFreq` spelling,
  which is why the 2026-09-14 triviality finding was answered by a sum unfolding
  rather than by content.
* Independent numerical sanity check (Python, 2000 random complex `c₁, c₂, x` and real
  `lam₁, lam₂`): maximum relative discrepancy between the two sides `0.0`, exactly,
  because both sides evaluate the identical expression.

## 7. Overclaims and incompleteness markers

* `grep -nwE "sorry|admit|axiom|opaque|native_decide|unsafe|partial|implemented_by|extern"`
  over `TorusSectionLadder.lean` and its only island import `TwoFreqRigidity.lean`:
  no matches at all (the registry marker check, which strips comments, also returns `[]`).
* The artifact header is honest: "BOTH are vocabulary bridges, not mathematics ... NOT
  counted as wins", the general-N identity is labelled "DEFINITIONAL (rfl)", and
  `conjecture1_proved = False` is stated. The theorem docstring says "simp-grade".
* The lakefile comment says "vocabulary bridges over TwoFreqRigidity (simp-grade; not a win)".
* The node title, the recorded readback, and all three attempts-ledger entries say the
  same thing. No overclaim was found in the artifact, the node, or the ledger.
* Documentation drift (not overclaims): `docs/QC_TORUS_SECTION_LADDER_MEMO_2026-09-14.md`
  section 6 still describes the node's content as the ORIGINAL general-N identity
  (`expSum = linearTorusForm ∘ torusOrbit`), i.e. the statement that was replaced on
  2026-09-14; and `WALL_BACKLOG_MAP_2026-09-18.md` / `RH_ASCENT_PLAN_2026-09-18.md` (F3-4)
  still say this draft "blocks" `MM_torus_section_n2_rigidity`. That is stale: the
  attempts ledger shows `MM_torus_section_n2_rigidity` GRANTED on 2026-09-19 by the
  integrator with `via = "direct"` (direct proofs are exempt from the reduction-premise
  check, so a draft dependency did not block it). The one stated reason to promote the
  dictionary has therefore lapsed.

## 8. The status gate and what each lead option would do

Consumers inside the campaign (read-only query): `MM_torus_section_n2_rigidity`
(proved, `via = direct`) and `MM_zeta_comb_membership` (draft goal, no proof link,
out of scope) list this node in `depends_on`.

* **Promote then grant.** Mechanically possible (`promote_to_open` only requires
  `draft` + a recorded readback), but it would grant as a rung a theorem whose own
  readback, node title, artifact header and this audit all say has no content. It would
  also make the third grant of the same fact (the 2026-09-20 read-back of the sibling
  already counts `twoFreq_realRooted_iff` granted twice plus this notation change).
  NOT recommended.
* **Deprecate with reason (R5).** `deprecate` requires a non-empty reason
  (`registry.py:407`). Effect on the battery, verified by an in-memory simulation
  (nothing written): NO closure flag changes; `MM_torus_section_n2_rigidity` keeps
  `closure_clean = True` because `_compute_closures` recomputes only `reduction`-via
  nodes and treats a direct node's stored flag as authoritative; the goal node has no
  proof link and is not in the closure map at all; `verify_campaign` has no check on
  edges into a deprecated node (its only deprecation check is that a reason exists).
  So `mission verify mirrormere` stays green. The two remaining `depends_on` edges into
  the node become documentary edges to a deprecated node, which is acceptable and
  already the registry's convention (cf. `BG_r2_multihub_maximality`). This is the
  action R5 prescribes when the re-audit finds triviality again, and it did.
* **Hold at draft as plumbing.** The status quo; `verify` is green today; the artifact
  keeps compiling as a default target and keeps its guard line. Acceptable if the lead
  prefers to keep the N=2 rigidity restatement's helper visible in the registry, but
  R5 says deprecate.

Recommendation: deprecate with reason (R5), or hold at draft; do not promote and grant.
A suggested reason string for the lead: "Re-audited 2026-09-22 (two independent blind
auditors): notation-only Fin-2 sum unfolding of twoFreq, zero mathematical content;
per WALL_BACKLOG_MAP R5 deprecated rather than promoted. Artifact remains compiled and
axiom-guarded on the quasicrystal island as the helper consumed by
MM_torus_section_n2_rigidity."

## 9. Environment notes for the lead

* The worktree's `quasicrystal/lean/.lake` is a root-owned symlink to the
  `arda-million` build, not a reflink copy. `lake env lean` works through it, but any
  `lake build` here writes into the sibling's shared tree, and its cached
  `TorusSectionLadder.olean` is from 2026-09-18 with no matching source in the sibling.
  If the lead wants a self-contained build here, replace the symlink with
  `cp -Rc ~/arda-million/telperion/examples/quasicrystal/lean/.lake <here>/.lake`
  (manifest and toolchain already match); the remaining rebuild is two small modules.
* Only one `lake build` was run by this audit, in a private scratch copy, and it has
  been deleted. No build was started on any shared island.

## 10. Read-back text (for the lead to record verbatim)

A1 blind re-audit 2026-09-22 of the proof artifact for MM_torus_section_dictionary. The node theorem in TorusSectionLadder.lean is byte-identical to the registry statement (200 bytes, raw and whitespace-normalized), and twoFreq, torusOrbit, linearTorusForm and expSum are byte-identical across MMDefs.lean, the artifact and TwoFreqRigidity.lean. I rebuilt the current artifact from source on a private reflink copy of the v4.32.0 quasicrystal build (Mathlib 81a5d25, same lake-manifest and toolchain as this worktree; only TwoFreqRigidity and TorusSectionLadder recompiled) and ran #print axioms: torus_section_dictionary, twoFreq, linearTorusForm, torusOrbit, expSum_eq_linearTorusForm_torusOrbit, torus_section_n2_rigidity, twoFreq_realRooted_iff and Fin.sum_univ_two all print exactly [propext, Classical.choice, Quot.sound]; no sorryAx, no ofReduceBool. The registry marker check returns [] and a grep for axiom, opaque, unsafe, partial, native_decide, implemented_by and extern over the artifact and its island import finds nothing. Mathematics: both sides are the two-term sum c1 exp(i lam1 x) + c2 exp(i lam2 x); the identity uses no hypothesis (it holds with c1 = c2 = 0 and lam1 = lam2), nothing about a torus (for non-real x the 'orbit' is not on the torus), no independence and no cut-and-project structure. The entire non-definitional gap is the single rewrite Fin.sum_univ_two: the Fin-2 sum unfolding is not rfl, the vector-literal projections and everything after that rewrite are rfl, and the default simp set closes the goal without being told the lemma. One immaterial correction to the 2026-09-19 read-back: bare rfl fails at the sum unfolding, not at add_zero. VERDICT: true, proved, kernel-clean, and notation only; zero mathematical content; not a rung and not to be granted as one. The 2026-09-19 verdict stands. The stated reason to promote it, unblocking MM_torus_section_n2_rigidity, has lapsed: that node was granted via direct on 2026-09-19. Deprecating the dictionary per WALL_BACKLOG_MAP R5 flips no closure flag and leaves mission verify green (closure recomputes only reduction-via nodes; the two edges into it are documentary). Recommend deprecate with reason, or hold at draft as plumbing; do not promote and grant. conjecture1_proved = False; nothing here proves or advances RH.
