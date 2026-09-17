# Telperion shapes & skills assessment — from the RH wall campaign (2026-09-16)

*Consolidation pass per the standing order (build reusable capabilities into Telperion).
Source material: the arithmetic-FQ/wall-map campaign on this branch — the reflection
certificate family (OrdinateInsensitivity, CompletedZetaConjugation, ReflectionForced,
ReflectionDetect, LiTermReflection/Li-razor), five+ adversarial sweeps with audit and
independent replication, and the corrected kill lemma. `conjecture1_proved = False`
throughout the source material; nothing here changes any mathematical claim.*

## A. Candidate emitter shapes (priority order)

| # | Shape | Source artifacts | What it emits | Self-check (sympy side) | Lean deps (v4.32 pin, verified present) | Feasibility |
|---|-------|------------------|---------------|--------------------------|------------------------------------------|-------------|
| 1 | `conj_equivariance` | `Gammaℝ_conj` + `completedRiemannZeta_conj` derived independently TWICE (ed7c94a72, 21fa2e5a2) — the derivation is mechanical, i.e. emitter-shaped | For an expression tree over `{+, −, ×, /, cpow(positive-real base, ·), Γ, ofReal constants}`: the certificate `f(conj s) = conj (f s)`, with hypothesis synthesis for pole/branch avoidance | Symbolic conjugation commutation on the tree; **forge face**: any non-equivariant node (`re`, `im`, `abs`, `arg`, cpow with non-positive-real base) must refuse | `Gamma_conj`, `cpow_conj` (+ `arg_ofReal_of_nonneg`), `map_mul/map_div₀/map_neg/map_ofNat`, `conj_ofReal` | **HIGH** — compositional rewrite chain; the two hand derivations are the golden tests |
| 2 | `cosh_excess` | `ReflectionDetect.lean` (6 thms, this branch) + ZooDH's numerical cosh bracket | Parametric detection identities: `x^a + x^{−a} ≥ 2` with equality iff `a = 0`, on `(a, x)` grids; composed pair-coordinate excess statements (Bragg-defect envelope style) | Exact factorization `(x^{a/2} − x^{−a/2})² ≥ 0`; **forge face**: refuse strict-excess claims at `a = 0` and at `x = 1` | `one_le_cosh`, `one_lt_cosh`, `rpow_def_of_pos`, `rpow_add`, `cosh_eq` | **HIGH** — small; reuses the bragg emitters' registry wiring pattern |
| 3 | `zero_symmetry_partner` | OrdinateInsensitivity family (pair/quadruple partner theorems) | For a function with certified symmetry set (functional equation + conjugation): partner/quadruple statements for parametric points | Closure of the symmetry group on sample points | `completedRiemannZeta_one_sub`, shape-1 output | MEDIUM — few distinct instances needed; consider folding into shape 1 as a mode |
| 4 | `finite_range_li_localization` | Sweep-4 probe #6 (Palojärvi τ-Li ↔ Möbius disk, Turán power-sum) | Kernel joint zero-localization disks from the certified Li ladder + computed data | Ladder values + Turán lemma arithmetic | Li ladder artifacts (main), Backlund S(T) | LOW-NOW — multi-week instrument; registry ticket, not an emitter sprint |

Authoring notes binding all four: every emitter enters through the standard registry
(kind, adapter, `emitter_sensitivity` stance decided AT AUTHORING TIME with the
Hermitian-square precedent in mind — shapes 1 and 3 are rewrite-chain structural, shape 2
carries per-instance certificates), with forge-face refusal tests and frozen-output drift
guards from day one. The two independent hand derivations of shape 1's flagship instance
are the acceptance tests: the emitter must reproduce both.

## B. Skill: the adversarial wall-sweep harness (added this commit)

`telperion/claude-plugin/skills/wall-sweep/SKILL.md` — the probe → refute → synthesize
workflow used five+ times this campaign, now twice on the same question with independent
convergence (`wu0aecd5x`, `wbba5wa6f`) and once audited (`w7m91imr9`). The skill encodes
what made it trustworthy: the verdict taxonomy (FOOTHOLD / COLLAPSE_TO_RH /
COLLAPSE_TO_FREE / TRANSFER / UNRESOLVED), abstention-is-not-refutation, primary-source
verification with an UNRESOLVED ledger, self-limiting survivors, and the
replication-then-reconcile pattern.

## C. Registry ticket (next steward step, not this commit)

Migrate the wall campaign into the missions registry (ANDÚRIL/MIRRORMERE pattern):
statement nodes for the reflection certificate family + the corrected kill lemma's two
kernel halves; sweep docs as attempt-ledger evidence; the campaign goal honest-draft.
Statement files MUST go through the registry writer — the #533 lesson: hand-authored
headers without the sha256 pin fail `mission verify` and ride green CI until grant time.
