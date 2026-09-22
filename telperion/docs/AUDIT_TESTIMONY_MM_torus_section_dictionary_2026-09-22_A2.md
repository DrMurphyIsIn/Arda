The artifact proves a notation-only identity (the island's two-term exponential sum equals its own Fin-2 summation-sign spelling) kernel-clean and byte-identical to the registered statement; it carries no mathematical content, is not a rung, and nothing here proves or approaches RH. conjecture1_proved = False.

# Audit testimony: MM_torus_section_dictionary (mirrormere, quasicrystal island), auditor 2 of 2

Auditor: A2 (blind, adversarial, independent of auditor 1; no coordination). Date: 2026-09-22.
Worktree /Users/peterwmurphy/arda-goal-weil, branch mm/gauss-window. No git command was run.
Island: telperion/examples/quasicrystal/lean, Lean v4.32.0, Mathlib v4.32.0
(rev 81a5d257c8e410db227a6665ed08f64fea08e997).
Artifact: TorusSectionLadder.lean (78 lines, namespace Quasicrystal, 3 definitions + 3 theorems,
imports TwoFreqRigidity; lakefile defaultTarget; AxiomGuardQC.lean line 88).
Node: missions/mirrormere/nodes/MM_torus_section_dictionary.toml (status draft, kind lemma,
via direct, depends_on [], readback dated 2026-09-19).
Statement: missions/mirrormere/lean/Statements/MM_torus_section_dictionary.lean
(header sha256 88b005abb1ab77e0).
Probes left in the worktree (not lean_libs, not default targets, not guarded; byte-identical to
the files I ran): examples/quasicrystal/lean/Probes/AuditTorusDict_Source.lean,
AuditTwoFreq_Source.lean, AuditTorusDict_Probes.lean;
missions/mirrormere/lean/Probes/AuditTorusDict_RegistryVocab.lean.
conjecture1_proved = False.

## 1. Verdict

PASS as a proof artifact; NOT a rung. One sentence: `Quasicrystal.torus_section_dictionary` is
stated byte-for-byte as the registry statement, is proved with axioms
[propext, Classical.choice, Quot.sound] when re-elaborated from this worktree's source, and asserts
only that c1 e^{i lam1 x} + c2 e^{i lam2 x} equals the same two terms written as a Fin 2 sum over
the literals ![c1, c2] and ![lam1, lam2]; after the single rewrite Fin.sum_univ_two the two sides
are definitionally equal (probe P3b closes the goal by rfl), so the whole gap between them is one
rewrite and there is no mathematical content. This is the second independent re-audit to find the
revised statement trivial (the 2026-09-19 read-back recorded on the node found the same), so
WALL_BACKLOG_MAP_2026-09-18 op R5 applies: deprecate rather than promote. The status gate is the
only mechanical gate refusing a grant, and it is refusing correctly. Do not promote; do not grant.

## 2. Kernel evidence (my runs, all from source)

No build of the quasicrystal island exists in this worktree. The only sibling build on this
machine (~/arda-million/telperion/examples/quasicrystal/lean/.lake, 13 GB; lake-manifest.json and
lean-toolchain byte-identical to this worktree's) contains a TorusSectionLadder.olean dated
2026-09-18 whose SOURCE no longer exists in that worktree (orphaned; the T1 branch report
docs/MM_mm-torus-ladder-t1_2026-09-18.md already warned that the T1 and T2 branches clobbered each
other's olean in the shared cache). I did not trust it. I reflink-copied the sibling .lake into an
isolated scratch copy of the island (cp -Rc into my scratchpad, NOT into this worktree, so no
collision with the other auditor and no `lake build` was started; the clone has since been
deleted), removed the orphaned TorusSectionLadder build products from the copy, and ran every
probe with `lake env lean` (single-file elaboration; nothing is written to any build directory).
TwoFreqRigidity.lean is byte-identical here and in the sibling, and probe 2 re-elaborates it from
source anyway, so the only pre-built oleans relied on are Mathlib's at the pinned rev.

Probe 1 (Probes/AuditTorusDict_Source.lean = TorusSectionLadder.lean verbatim between markers,
then prints), exit 0, output verbatim:

    def Quasicrystal.twoFreq : ℂ → ℂ → ℝ → ℝ → ℂ → ℂ :=
    fun c₁ c₂ lam₁ lam₂ x => c₁ * cexp (↑lam₁ * x * I) + c₂ * cexp (↑lam₂ * x * I)
    'Quasicrystal.twoFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.torusOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.linearTorusForm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.expSum' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.expSum_eq_linearTorusForm_torusOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.torus_section_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.torus_section_n2_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.twoFreq_realRooted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Fin.sum_univ_two' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Matrix.cons_val_zero' depends on axioms: [propext]
    'Matrix.cons_val_one' depends on axioms: [propext]
    'Matrix.head_cons' depends on axioms: [propext]

Probe 2 (Probes/AuditTwoFreq_Source.lean = TwoFreqRigidity.lean verbatim, then prints), exit 0:

    'Quasicrystal.twoFreq_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.twoFreq_zero_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Quasicrystal.twoFreq_realRooted_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

Probe 4 (scratchpad only; not left in the worktree because it embeds MMDefs.lean, which carries
two `sorry` support lemmas): Statements/MMDefs.lean verbatim, re-elaborated from source under the
same Mathlib, followed by the registered statement proved against the registry's OWN constants,
once with the artifact's tactic line and once in the one-rewrite form; exit 0:

    AuditRegistryVocab_MMDefs.lean:154:8: warning: declaration uses `sorry`
    AuditRegistryVocab_MMDefs.lean:470:6: warning: declaration uses `sorry`
    'torus_section_dictionary_REGISTRY_VOCAB' depends on axioms: [propext, Classical.choice, Quot.sound]
    'torus_section_dictionary_REGISTRY_VOCAB_rw' depends on axioms: [propext, Classical.choice, Quot.sound]

(The two warnings are MMDefs.lean:156 and :470, the pre-existing support lemmas that file's own
comments flag as scaffolding; the axiom lines show they are not reachable from this node.)

Probe 5 (missions/mirrormere/lean/Probes/AuditTorusDict_RegistryVocab.lean, importing the BUILT
Statements.MMDefs of this worktree's Statements project, run with `lake env lean` from that
directory), exit 0:

    'torus_section_dictionary_registry_vocab' depends on axioms: [propext, Classical.choice, Quot.sound]
    'torus_section_dictionary_registry_vocab_rw' depends on axioms: [propext, Classical.choice, Quot.sound]

Token grep (`sorry`/`admit`/axiom/opaque/native_decide/unsafe/implemented_by/extern/partial/
set_option/decide) over TorusSectionLadder.lean and TwoFreqRigidity.lean, code and comments:
nothing. The registry's own artifact_incompleteness_markers on the artifact: [].

## 3. Registry byte comparison and gate dry-run (python, read-only, the registry's own functions)

- Theorem text from `theorem torus_section_dictionary` to `:= by`, statement module vs artifact:
  RAW BYTE-IDENTICAL, and identical after whitespace normalisation. The statement file ends
  `:= by sorry`; the artifact continues `simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]`.
- _normalized_statement = 'theorem torus_section_dictionary (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
  twoFreq c₁ c₂ lam₁ lam₂ x = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x)';
  containment in normalize_lean(artifact): True.
- Definitions: `twoFreq` MMDefs.lean:33-35 vs TwoFreqRigidity.lean:40-42 IDENTICAL; `torusOrbit`,
  `linearTorusForm`, `expSum` MMDefs.lean:69-76 vs artifact lines 40-49 IDENTICAL (whitespace-
  normalised). The artifact mirrors the definitions into its own namespace instead of importing
  MMDefs; probes 4 and 5 show the registered statement is closed by the same tactic against
  MMDefs's constants, so the mirror is faithful.
- regen_diff on the statement file (header sha256 88b005abb1ab77e0 re-derived from the on-disk
  body with toolchain leanprover/lean4:v4.32.0 and mathlib v4.32.0): '' (no drift).
- grant_status preconditions, dry-run without calling it: (1) status == open: FALSE, status is
  'draft'; the gate raises "Node 'MM_torus_section_dictionary' has status 'draft'; grant_status
  only operates on open nodes." (2) proof link: present. (3) artifact exists: yes. (4) normalized
  statement non-empty: yes. (5) containment True, markers [], refutation_matches False, so the
  outcome would be 'proved'. (6) via == reduction: no, so the premise check does not apply
  (depends_on is [] anyway).
- promote_to_open would mechanically succeed (status draft, readback recorded 2026-09-19).
- verify_campaign(missions/mirrormere), read-only battery: ok, 0 errors, 0 warnings.
- Dependents: MM_torus_section_n2_rigidity (proved, via direct, closure_clean True) and
  MM_zeta_comb_membership (goal, draft, RH-equivalent, out of scope).

## 4. Mathematics re-derived by hand

LHS: twoFreq c1 c2 lam1 lam2 x = c1 * exp((lam1:ℂ) * x * I) + c2 * exp((lam2:ℂ) * x * I)
(TwoFreqRigidity.lean:40-42).
RHS: linearTorusForm 2 ![c1,c2] (torusOrbit 2 ![lam1,lam2] x)
   = ∑ j : Fin 2, ![c1,c2] j * exp((![lam1,lam2] j : ℂ) * x * I).
Fin.sum_univ_two (Mathlib Algebra/BigOperators/Fin.lean:110-112, the to_additive twin of
prod_univ_two, tagged @[simp], proved there by simp [prod_univ_succ] because the underlying
Multiset fold ends in `+ 0`): ∑ j, f j = f 0 + f 1. Then ![c1,c2] 0 = c1 and ![c1,c2] 1 = c2
(Matrix.cons_val_zero and cons_val_one, both rfl, Data/Fin/VecNotation.lean:126 and :271),
likewise for lam, and the real-to-complex casts commute with the projections definitionally.
RHS = c1 * exp((lam1:ℂ) x I) + c2 * exp((lam2:ℂ) x I) = LHS. Checked.

Probe P3b confirms this decomposition exactly: `rw [linearTorusForm, Fin.sum_univ_two]; rfl`
closes the goal, so everything except the single sum unfolding is definitional. Bare `rfl` fails
(P3a) for the reason the 2026-09-19 read-back gave (the fold's trailing `+ 0` is not definitional
over ℂ because real addition is a quotient of Cauchy sequences); that is a fact about Lean's
reals, not about the statement.

Content assessment. N is the literal 2, both vectors are literals, and no irrationality, rational
independence, Kronecker or cut-and-project hypothesis appears: the two sides are one expression in
two spellings. The 2026-09-14 audit rejected the general-N identity expSum = linearTorusForm on
torusOrbit as definitionally rfl (it is still in the artifact as
`expSum_eq_linearTorusForm_torusOrbit := rfl`, guarded, and correctly not a node); the revision
instantiated that identity at N = 2 against the island's `twoFreq` spelling, which adds one rewrite
and no content. I concur with the 2026-09-19 read-back verdict: notation change, not a bridge
lemma, not a rung. The artifact header (lines 15-21), lakefile.toml:66 and the node title say the
same.

## 5. Probes (Probes/AuditTorusDict_Probes.lean; exits 1 by design at P3a and P3f)

Expected successes, all elaborated: P3b one rewrite then rfl; P3c the explicit simp-only set
(linter: Matrix.head_cons unused, because cons_val_one lands on `u 0` and cons_val_zero closes it);
P3d the artifact's exact tactic line; P3e `simp [twoFreq, linearTorusForm, torusOrbit]` without
naming Fin.sum_univ_two (it is @[simp], so the artifact's explicit mention is redundant).
Expected failures, each at the intended point, verbatim:

    Probes/AuditTorusDict_Probes.lean:32:70: error: Type mismatch        -- P3a: bare rfl does not close the identity
      rfl
    has type
      ?m.17 = ?m.17
    but is expected to have type
      twoFreq c₁ c₂ lam₁ lam₂ x = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x)
    Probes/AuditTorusDict_Probes.lean:67:70: error: unsolved goals       -- P3f: negative control, coefficient literal reversed
    ⊢ c₁ * cexp (↑lam₁ * x * I) + c₂ * cexp (↑lam₂ * x * I) = c₂ * cexp (↑lam₁ * x * I) + c₁ * cexp (↑lam₂ * x * I)

P3f shows the tactic really evaluates the projections: the identity is order-sensitive and the
battery is discriminating.

## 6. Overclaim grep

TorusSectionLadder.lean:27 "No RH progress is claimed. conjecture1_proved = False."; lines 15-21
grade both theorems "vocabulary bridges, not mathematics ... NOT counted as wins"; the only
"rung" language is the T1 track label. Node title: "NOTATION ONLY (not a bridge lemma) ... HELD AT
DRAFT and NOT to be granted as a rung". lakefile.toml:66 "(simp-grade; not a win)".
AxiomGuardQC.lean:10 and :84-86 "recorded, not counted". No overclaim in the artifact, the node,
the statement or the island plumbing.

## 7. Findings for the lead

1. Trivial again, so R5 applies: deprecate with reason rather than promote. Nothing in the
   artifact needs changing; the Lean theorem may stay in the island as the plumbing
   `torus_section_n2_rigidity` rewrites through (its tactic is `simp only [← torus_section_dictionary]`).
   Deprecating the registry node touches no Lean; the artifact stays a default target and stays guarded.
2. "Leave at draft" is not a stable state. The node already carries a readback, so promote_to_open
   succeeds mechanically, and `mission audit` (cli.py cmd_mission_audit) has no hold flag: any
   readback recorded through the CLI is written and then draft -> open is attempted
   unconditionally. Once open, every other gate passes (section 3), so a routine grant pass would
   grant it. The 2026-09-19 readback can only have been recorded without promotion by editing the
   TOML directly.
3. There is no `deprecate` subcommand in the mission CLI (status, open-leaves, claim, release,
   add, audit, link, attempt, grant, verify, graph). Deprecation is registry.deprecate(campaign,
   slug, reason) from Python, or a hand edit setting status = "deprecated" plus a non-empty
   deprecated_reason (schema.py:145 refuses an empty reason). load_campaign and verify_campaign
   impose no rule against depending on a deprecated node, so deprecation breaks no invariant.
4. Two nodes list this one in depends_on. (a) MM_torus_section_n2_rigidity (proved, via direct):
   the edge is documentary (direct proofs are exempt from the premise check and closure is never
   recomputed for them), so its status and closure_clean stay as they are; the lead may prune or
   annotate the edge. (b) MM_zeta_comb_membership (goal, draft, RH-equivalent, out of my scope)
   lists it among 17 dependencies; prune that edge when the placeholder is replaced (R7).
5. Recording my read-back on the node: the node has one [readback] table, so `mission audit`
   OVERWRITES the 2026-09-19 text and (finding 2) promotes. To put my text on the node verbatim,
   deprecate FIRST and then run `mission audit`: the readback is written durably before
   promote_to_open refuses the non-draft node (exit 1, harmless). Alternatively append it to
   attempts.jsonl with `mission attempt --verdict NoGo`, which touches nothing else.
6. Sibling accounting note: MM_torus_section_n2_rigidity's 2026-09-20 readback says the notation
   change "is granted as a third". It is not granted; it is draft. Awareness only.
7. Documentation drift: QC_TORUS_SECTION_LADDER_MEMO_2026-09-14.md section 6 still describes this
   node's content as "expSum = linearTorusForm on torusOrbit", the general-N form retired 2026-09-14.
8. Guard coverage: AxiomGuardQC.lean:88 lists the theorem and the disjoint-discs CI job runs the
   whole guard and fails on any sorryAx, but that job asserts the presence only of the OfflineDiscs
   lines, so a dropped torus line would pass unnoticed there (PR #592 "island axiom guards
   hardened" is the place for it). The only pre-built TorusSectionLadder.olean on this machine is
   orphaned (~/arda-million); anyone running the guard against a shared .lake must rebuild from
   source first, as the T1 report itself warned.
9. Cosmetic: Fin.sum_univ_two is @[simp] in Mathlib v4.32.0, so naming it in the artifact's simp
   call is redundant (P3e).
10. MMDefs.lean carries two `sorry` support lemmas (lines 156 and 470, self-flagged as
    scaffolding). They are not reachable from this node (probes 4 and 5 are axiom-clean) and lie
    outside the artifact, so the marker gate does not see them; noted because the statement
    package is what every mirrormere containment check reads.

## 8. What this does and does not establish

Established: the registered statement is proved kernel-clean, byte-identical, from source, on
Lean v4.32.0 / Mathlib v4.32.0, and it is a change of notation. Not established: anything about
zeta, the torus, Kronecker orbits, or any rung of the ladder. NOT a proof of anything about RH.
conjecture1_proved = False.
