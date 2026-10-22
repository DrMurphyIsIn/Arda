# Emitter design: `range_completeness_decide` (2026-10-22)

`RangeCompletenessEmitter`, kind `range_completeness_decide`, module
`src/telperion/emit_range_completeness.py`. It is a FACE of the existing `finite_decide` kind:
the AST that `emit_finite_decide.py` evaluates in Python and renders to Lean gains the nodes
needed to state a coverage claim, and the new module adds the surrogate-predicate bridge and
the companion theorems around that claim.

`conjecture1_proved = False`. This kind certifies finite decidability facts about explicit
lists of natural numbers. It says nothing about RH or any other open problem.

## The problem

A table-driven proof often ends with a claim of the form "every `m < N` with property `P` is
one of these": the 190 radicands of the class-number-one finite search, the 65 idoneal numbers,
the squarefree discriminants in a window. The claim is decidable, and the Lean kernel can
decide it, but only if `P` reduces. Mathlib's `Squarefree` does not: its `Decidable` instance
goes through `Nat.minFac`, a well-founded recursion that `decide` cannot unfold. The
hand-built CN-1 proof (tenth-discriminant, `CN1/Finite/Witnesses.lean` and
`CN1/Finite/SplitPrime.lean`) solved this with a surrogate: a bounded predicate

    SqfBelow K m := ∀ k ∈ Finset.Icc 2 K, ¬ k * k ∣ m

that the kernel evaluates by trial division, a once-proved lemma
`Squarefree m → SqfBelow K m`, and the coverage decided against `SqfBelow`. This kind is that
pattern as a generator.

## The shape

Inputs: a bound `N`, an explicit list `L`, an optional exclusion list, optional extra decidable
guards over the bound variable (any `finite_decide` prop, for example `m % 4 = 3`), and
optionally the surrogate pair. Output, per instance `nm`:

* `nm_list : List ℕ` (and `nm_excl` when there are exclusions);
* the coverage theorem, kernel-decided:

      theorem nm : ∀ m ∈ Finset.range N, (∀ k ∈ Finset.Icc 2 K, ¬ (k * k) ∣ m) → G m → m ∉ nm_excl → m ∈ nm_list := by
        decide +kernel

* the bridge `nm_sqfBelow_of_squarefree {m : ℕ} (hm : Squarefree m) : ∀ k ∈ Finset.Icc 2 K, ¬ (k * k) ∣ m`,
  a four-line tactic proof (`Nat.isUnit_iff` turns `IsUnit k` into `k = 1`; `Finset.mem_Icc`
  gives `2 ≤ k`; `omega`);
* the consumer theorem `nm_of_squarefree : ∀ m < N, Squarefree m → G m → m ∉ nm_excl → m ∈ nm_list`,
  a one-line term through the bridge;
* on request, `nm_length : nm_list.length = |L|`, `nm_nodup : nm_list.Nodup`, and
  `nm_sound : ∀ m ∈ nm_list, m < N ∧ (surrogate) ∧ G m ∧ m ∉ nm_excl`, all by `decide +kernel`.

With all three companions the four theorems say "L is exactly the guarded set and has |L|
elements", which is the list-completeness claim one wants for a published table.

## The bound K^2 > N: a sufficient policy, not the exact condition

The bridge is sound for every `K`: it is the direction `P → P'`, and the coverage theorem with
`P'` as hypothesis is weaker than one with `P`, so the consumer theorem follows for any `K`. The
bound is about meaning, not soundness. `SqfBelow K` agrees with `Squarefree` on `[0, N)` exactly
when every prime `p` with `p^2 ≤ N - 1` is at most `K`, that is `K ≥ isqrt(N - 1)`. If some
such `p` exceeds `K`, `SqfBelow K` is strictly weaker on the range, the coverage theorem forces
`L` to contain non-squarefree numbers, and "the squarefree numbers below N" would be a lie
about what `L` is.

`K^2 > N` is a simpler SUFFICIENT condition (a non-squarefree `m < N` has a square factor
`p^2 ≤ m < N`, so `p < sqrt N ≤ K`), and the emitter enforces it as a stated POLICY: the
decision taken after review (REVIEW_PR762, D1) was to keep the simple bound rather than relax
it to the exact one. So `range_completeness_certificate` refuses `K^2 ≤ N` even where a smaller
`K` would still be exact: the example's bound check uses `K = 14` against `N = 200`
(`196 ≤ 200`), and `K = 14` or `K = 13` would in fact agree with `Squarefree` on `[0, 200)`,
since the largest prime whose square is below 200 is 13. The refusal message says so and names
the smallest `K` the policy accepts. The authority on agreement is not the bound but the
per-`m` cross-check of the surrogate against exact `Squarefree` over the whole range, which
runs on every certificate.

## The certificate (Layer 1, in Python)

The coverage and soundness propositions are built as `finite_decide` AST and evaluated by the
same exact evaluator the `finite_decide` kind uses, so the Python check and the Lean statement
are one structure rendered two ways. `range_completeness_certificate` refuses:

* a float, a negative number or a bool anywhere (`N`, the list, the exclusions);
* `N = 0`;
* a surrogate bound with `K < 2` or `K^2 ≤ N`;
* a coverage that is false, naming the first uncovered `m`;
* a VACUOUS coverage: no `m < N` satisfies the guards, so any list would do. This is the one way
  the shape can be empty, and it is the analogue of `finite_decide`'s "no atomic comparison was
  ever evaluated" refusal;
* a repeated element when `emit_nodup` is requested;
* an element outside the guarded set when `emit_soundness` is requested.

The returned check count is the number of atomic comparisons and memberships the evaluator
performed (4,251 for the example).

## Decision: extend `finite_decide`'s AST, and add a sibling emitter

The survey called N6 a face of `finite_decide`, needing an AST extension `Mem(var, list)` and
`Finset.range` as a domain, not a new kind. Both halves of that are right, and the code
follows both.

* The AST extension lives in `emit_finite_decide.py`: `ForallRange`, `ForallIcc`, `Not`, `And`,
  `Mem`, `NotMem`, the expression node `Mod`, and the comparison `dvd`. The evaluator and the
  renderer were extended in place, so `FiniteDecideEmitter` can state a range coverage by
  plain `decide` (a test pins this). Evaluation of the pre-existing nodes is unchanged, and
  their text is byte-identical whenever every `Imp` hypothesis is a `Cmp`, the only form
  existing callers use (the `finite_decide` example's drift check still passes; a test pins
  the unchanged `Imp`-of-`Cmp` rendering). The one rendering change is a FIX: an `Imp` whose
  hypothesis is itself an `Imp` or a `ForallIn` is now parenthesised, `(∀ v ∈ T, a) → b`. The
  old text `∀ v ∈ T, a → b` was re-associated by Lean as `∀ v ∈ T, (a → b)`, a different
  proposition from the one Python evaluated, a latent text/semantics divergence found in review
  (bb rendered 3,000 old-node ASTs with both modules: evaluation agreed in all, text in all
  2,057 with comparison hypotheses).
* The bundle around the coverage theorem is a sibling module. `FiniteDecideEmitter.emit_body`
  emits one `theorem … := by decide` per instance and nothing else; the N6 instance is a list
  definition, a `decide +kernel` theorem under `set_option maxRecDepth`, a tactic-proved
  bridge about Mathlib's `Squarefree`, a term-mode consumer theorem and up to three companions.
  Folding that into `FiniteDecideEmitter` would have meant a second payload shape and a mode
  switch inside a 30-line emitter, and `emitter_for(kind)` resolves one emitter class per kind.
  So the sibling has its own kind, `range_completeness_decide`, its own certificate dataclass
  (`RangeCompletenessCert`, which the adapter forges by `dataclasses.replace`), and imports the
  AST, evaluator and renderer from `emit_finite_decide`. There is one evaluator and one
  renderer; nothing is duplicated.

The surrogate is a small dataclass (`SquarefreeSurrogate(K)`) exposing the guard as AST, the
bridge lemma text, the consumer hypothesis and the bound check. It is the only surrogate today.
A second one (a bounded primality test, a residue condition on prime factors) would be a second
dataclass with the same five members; the emitter does not know which one it holds.

## Lean details, measured on v4.32.0 / Mathlib v4.32.0

* `decide +kernel`, not `decide`: the elaborator's `Decidable.decide` evaluation of a 200-fold
  `Finset.decidableDforallFinset` instance is far slower than the kernel's, and the CN-1 template
  used `+kernel`.
* `set_option maxRecDepth 8192 in` is emitted on the coverage and soundness theorems (a
  parameter, `max_rec_depth`, defaulting to the CN-1 value). The probe found the DEFAULT depth
  sufficient at N = 200, 400, 653, 1000 and 2000 (see the table), so at these sizes no
  recursion-depth limit is hit; the option is kept because it is free and the CN-1 proof set it.
* Kernel time (`set_option profiler true`, `lake env lean`, Apple Silicon, one slot):

  | theorem | N | kernel type checking | `maxRecDepth` |
  |---|---|---|---|
  | coverage `sqf_lt_200` (113 members, 9 exclusions, K = 15) | 200 | 0.45 s | default suffices |
  | soundness `sqf_lt_200_sound` | 200 | 0.64 s | default suffices |
  | length `sqf_lt_200_length` (113) | 200 | 0.44 s | |
  | nodup `sqf_lt_200_nodup` (113) | 200 | 0.88 s | |
  | coverage, all squarefree below N, K = isqrt(N) + 1 | 400 | 1.8 s | default suffices |
  | coverage (the CN-1 size; 397 members) | 653 | 4.9 s | default suffices |
  | coverage | 1000 | 11.8 s | default suffices |
  | coverage | 2000 | 50.9 s | default suffices |

  Each row was run twice, once with no `set_option` at all and once with 8192; the times agree
  to within noise and no run hit a recursion-depth error, so on this toolchain the
  `maxRecDepth 8192` of the CN-1 template was not needed up to N = 2000. The cost grows a little
  faster than N^2 (the `Finset.range` fold is N deep, each step does K trial divisions and a
  membership scan of a list of length about 0.6 N).

  The whole example module (`lake build`, 10 theorems) built in 30 s, of which about 5.3 s is
  kernel type checking and the rest is loading Mathlib.

  All of these numbers are on Lean v4.32.0 / Mathlib v4.32.0, the island toolchain. The CN-1
  proof itself is on v4.34.1 / Mathlib d13f23b; neither the depth behaviour nor the timings
  were re-measured there (the survey's open check 1 stays open for that toolchain).
* Precedence: `¬ (k * k) ∣ m` parses as `¬ ((k * k) ∣ m)`; a binder under `∧` or as an `→`
  hypothesis is parenthesised by the renderer; an atomic comparison is not, so pre-existing
  `finite_decide` output is unchanged.
* `0 ∣ b ↔ b = 0` in Lean; the Python `dvd` matches that convention.

## Dogfood (`examples/range_completeness_decide/`)

| instance | claim | K | companions |
|---|---|---|---|
| `sqf_lt_200` | every squarefree `m < 200` outside the nine Heegner radicands {1, 2, 3, 7, 11, 19, 43, 67, 163} is in the 113-element list | 15 (225 > 200) | length, nodup, soundness |
| `sqf_3mod4_lt_60` | every squarefree `m < 60` with `m % 4 = 3` is in the 14-element list | 8 (64 > 60) | length |

Ten theorems; every one prints axioms `[propext, Classical.choice, Quot.sound]`. The
generator's validation report carries two refusals: the list with 199 dropped ("coverage is
FALSE -- m = 199 …") and the bound `K = 14`.

## Stance: STRUCTURALLY_NONVACUOUS, with a registered kernel adapter

The question is whether the list `L` is a corruptible WITNESS (CERTIFICATE_SENSITIVE) or the
STATEMENT (STRUCTURALLY_NONVACUOUS). It is the statement: the theorem is about `L`, there is no
separately supplied identity or cofactor whose corruption would leave the statement intact while
breaking the proof, and the kernel re-decides every membership from the list literal. Dropping
an element changes the theorem, and the changed theorem is false. That is the same situation as
`ScaledIntervalEvalEmitter` (the boxes are the statement) and the registry's ruling there was
STRUCTURALLY_NONVACUOUS with an adapter. The one way this shape can be hollow is a vacuous
guard, and Layer 1 refuses that; the structural non-vacuity check plus the kernel then suffice.

The honest objection is that "structural" must not mean "untested", so the control is
demonstrated, not inferred:

* **Registered adapter** (`negctrl_adapters/adapter_range_completeness.py`). The true twin is
  the 30 squarefree `m < 60` outside the seven Heegner radicands below 60, `K = 8`. The forgery
  drops the largest element, 59 (prime, squarefree, not excluded), by editing the frozen
  dataclass, bypassing Layer 1, which on its own refuses it naming `m = 59`. No length, nodup
  or soundness companion is emitted for the control, so the rejection is pinned to the coverage
  `decide` and not to a companion that would also be false. The bridge and the consumer theorem
  are emitted with it; in the false twin the bridge compiles and the consumer inherits
  `sorryAx` from the rejected coverage theorem. The two emitted texts differ in exactly one
  line, the list literal.
* **Result.** The kernel rejects the forged theorem (`decide +kernel` reports the proposition
  false) and the true twin compiles axiom-clean; the two-sided check `generic_negative_control`
  passes in `tests/test_emit_range_completeness.py::test_lean_negative_control_dropped_element`.
  The Lean output of both twins is recorded in the PR.

## What is NOT guaranteed

* Only the `Squarefree` surrogate exists. A property with no kernel-friendly surrogate cannot
  use the bridge; it can still be stated directly if it is a `finite_decide` guard.
* The kind proves what the kernel decides. It does not prove that the list is "the squarefree
  numbers" unless the soundness companion is requested; without it the theorem is one-sided
  (coverage only), and the length companion then counts a superset.
* Kernel time is roughly quadratic in `N` (about N^2.1 on the table: the per-step list scan
  of length about 0.6 N dominates the K trial divisions); the probe stops at N = 2000. The
  CN-1 size (N = 653) is comfortable; tables in the tens of thousands were not measured.
* The bridge uses `Nat.isUnit_iff`, `Finset.mem_Icc`, `Finset.mem_range` and `omega`; a
  Mathlib rename would break the bridge, not the kernel fact, and the compile gate would catch it.
