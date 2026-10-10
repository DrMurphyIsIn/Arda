# scaled_interval_eval -- kernel-recomputed fixed-scale interval evaluation (2026-10-09)

Prototype of Part C shape C1 (`~/oai-math-review/PART_C_EMITTERS.md`, "C1. scaled_interval_eval").
Branch `telperion/scaled-interval-eval`, local only. `conjecture1_proved = False`: the emitter
encloses explicit elementary expressions. It says nothing about RH.

## What it is

A real number `x` is enclosed by an integer pair `(lo, hi)` at a fixed scale `S` when
`lo <= S*x <= hi`. Every operation is computable integer arithmetic. Division is floor division,
and each result is rounded outward by one unit in the last place (ulp). So the Lean kernel can
evaluate it on literal boxes with `decide +kernel`. The soundness of each operation is proved once,
over the reals, in a small prelude. A certificate instance is then only literal data plus kernel
evaluation.

This is the architecture OpenAI's `openai/math` library uses everywhere (finding 4 of the Part C
sweep). The prior art is `lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean`
(Apache-2.0, https://github.com/openai/math). It has `RI`, `CI`, `RI.mul`, `CI.taylor`, `CI.exp`
and the `mem_*` lemmas. Our prelude is a minimal rewrite in Telperion's style and credits that
file in its header. It differs in four ways:

- The scale `S` is a parameter, not the constant `10^60`.
- It covers real intervals only. Complex intervals are left for later.
- `exp` closes its Taylor remainder with Mathlib's `Real.exp_bound`. The widen `r` is chosen by the
  emitter and checked by `decide`.
- Per-node checks are Bool subset checks, as the design note recommends.

## Files

| File | Role |
|---|---|
| `src/telperion/emit_scaled_interval_eval.py` | Python mirror of the integer semantics, DAG builder, certificate, emitter, family builder; holds the prelude text as the single source |
| `examples/scaled_interval_eval/lean/ScaledInterval.lean` | The prelude, written by `generate.py` (drift-checked) |
| `examples/scaled_interval_eval/lean/ScaledIntervalEval.lean` | Four emitted instances |
| `examples/scaled_interval_eval/lean/AxiomGuardScaledIntervalEval.lean` | Hand-written `#print axioms` guard |
| `examples/scaled_interval_eval/generate.py` | certify, emit, write; `--check` is the drift check |
| `src/telperion/negctrl_adapters/adapter_scaled_interval_eval.py` | One-ulp negative control |
| `tests/test_emit_scaled_interval_eval.py` | 38 tests, three of them Lean-gated |

The island pins Lean `v4.32.0` and Mathlib `v4.32.0`, the same manifest as `log_combination`.

## The prelude (`ScaledInterval`)

- **Data.** `RI := {lo hi : ℤ}`. `RI.Mem S a x := lo ≤ S*x ∧ S*x ≤ hi`.
- **Operations.** These are `ofRange`, `ofFrac`, `add`, `neg`, `sub` and `mul` (four corner
  products, floor-divided by `S`, plus one ulp). Then come `divNat`, `widen`, `square` (k
  squarings) and `taylor`, which gives the boxes of `x^n/n!` and the partial sum. Finally
  `expR S a k n r` divides by `2^k`, takes the order-`n` Taylor sum, widens by `r`, and squares
  `k` times.
- **Checks.** These are `Bool`-valued: `subset`, `lowerOK`, `upperOK`, `expSmallOK` (the reduced
  argument lies in `[-1, 1]`) and `expRemOK` (`S(n+2) ≤ r·(n+1)!·(n+1)`).
- **Soundness.** Each check or operation has one lemma: `mem_ofRange`, `mem_ofFrac`, `mem_add`,
  `mem_neg`, `mem_sub`, `mem_mul`, `mem_divNat`, `mem_widen`, `mem_square`, `mem_taylor`,
  `mem_expR`, `mem_of_subset`, `le_of_mem` and `ge_of_mem`. Every one depends only on
  `[propext, Classical.choice, Quot.sound]`.

## What the generator emits per instance

The input is a sympy expression over rationals and declared variables. Each variable has a
rational range. The supported operations are `+`, `-`, `*`, positive integer powers and `exp`.
Shared subtrees are built once. For node `k` the emitter writes:

```lean
def p_bk : RI := ⟨lo, hi⟩                                  -- literal box
noncomputable def p_vk (x : ℝ) : ℝ := p_vi x * p_vj x     -- the real value
theorem p_bk_calc : RI.subset (RI.mul p_S p_bi p_bj) p_bk = true := by decide +kernel
theorem p_bk_mem (x) (h_x_lo) (h_x_hi) : RI.Mem p_S p_bk (p_vk x) :=
  RI.mem_of_subset (RI.mem_mul p_hS (p_bi_mem ..) (p_bj_mem ..)) p_bk_calc
```

Exp nodes add two more facts, `_small` and `_rem`, each closed by `decide +kernel`. The final
theorem is stated over the reals, quantified over the variables and their ranges. For example:

```lean
theorem sie_cubic : ∀ x : ℝ, (1/3 : ℝ) ≤ x → x ≤ (1/2 : ℝ) →
    lo ≤ ((x * x) * x - 2 * x) + 1/3 ∧ ((x * x) * x - 2 * x) + 1/3 ≤ hi
```

It is closed by `le_of_mem` and `ge_of_mem` against `lowerOK` and `upperOK`, both decided by the
kernel. A statement-match `example` follows each theorem. `norm_num` appears only at the leaves,
where it equates a literal like `(1 : ℝ) / 3` with `((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)`.

## Guarantees

- **Nothing numeric is trusted from Python.** The kernel recomputes every box. The Python fold
  mirrors Lean's integer semantics exactly. Lean's `Int` `/` is Euclidean division, which equals
  floor division for the positive divisors used here. Since the checks are subset checks, a mirror
  bug could only make a check fail, never let a false box pass.
- **No escape hatches.** There is no `native_decide`, `sorry`, `axiom` or heartbeat override, and
  no `maxRecDepth` override either.
- **Refusals in Python (Layer 1).** Certification refuses a claim that does not contain the
  computed root box, including a claim one ulp too tight. It also refuses floats, irrational
  constants, unsupported functions, negative or fractional powers, inverted ranges, a declared but
  unused variable, a scale below 2, an inverted claim and an exp argument needing more than 64
  halvings.
- **Kernel rejection (Layer 2).** These tests ran against the built island:
  - The adapter shrinks the root box's upper end by one ulp. The kernel rejects it, and the
    unmodified twin compiles clean. The two texts differ in exactly one line.
  - A hand-forged claim whose upper end lies below the true value of `exp(1/3)/7 + 2/9` is
    rejected. The `upperOK` decide fails.
- **Registry.** The emitter is registered as `STRUCTURALLY_NONVACUOUS` with an explicit
  `NEG_CONTROL_ADAPTER` stance, following `ExpEnclosureEmitter`. The box is the statement, and
  there is no separately supplied identity to corrupt.

## Costs (measured)

Measured on this Mac under load with `profiler.threshold 0`, one `lake env lean` run, scale
`S = 10^40`. "Decide fact" means one `_calc`, `_small`, `_rem` or claim check, timed as elaboration
plus kernel time. The kernel share alone is in parentheses.

| Instance | Nodes | Decide facts | Decide total | Median per fact | Slowest fact |
|---|---|---|---|---|---|
| `sie_exp_third`, exp(1/3)/7 + 2/9 | 6 | 8 | 80 ms (17 ms) | 8.4 ms | exp node, 20.5 ms |
| `sie_cubic`, x^3 - 2x + 1/3 on [1/3, 1/2] | 8 | 8 | 70 ms (5 ms) | 8.8 ms | 9.3 ms |
| `sie_sinh_reduced`, e^{5/2} - e^{-5/2}, k = 2 | 6 | 10 | 113 ms (32 ms) | 8.8 ms | exp node, 23.2 ms |
| `sie_exp_series`, sum of exp(-j/4) x^j, j <= 6, on [0, 1/2] | 31 | 43 | 457 ms (106 ms) | 8.9 ms | exp node, 22.7 ms |

- **Per node.** An arithmetic node costs about 9 ms, nearly all of it elaboration overhead. An
  exp node with a 34-term Taylor sum and up to two squarings costs about 20 to 23 ms.
- **Membership lemmas.** These cost about 12 to 15 ms per node. They are dominated by the leaf
  `norm_num` calls and the delta-unfolding of the value definitions.
- **Whole file.** The 51-node file elaborates in 2.8 s, after the 9 s `import Mathlib` load. A
  first probe ran three exp-only decides in 39 ms of total type checking.
- **Comparison.** `exp_enclosure` reaches the same kind of bracket through `norm_num
  [Nat.factorial]` on exact rationals. That cost grows with the Taylor order and the size of the
  rationals, while here the per-node cost stays flat at about 9 ms.
- **Scaling.** Sharding at about 200 nodes per file, as OAI does, is not implemented. The emitter
  refuses instances above 2000 nodes.

## Discharging an Arb seam: the BraggDefect off-line defect (proposal, not implemented)

**Target.** In `examples/zeta_zero_localization/lean/BraggDefect.lean`, `bragg_defect_witness`
and `defect_leakage_gap` both take the hypothesis below. It is the Arb enclosure of `e^{1/10}`,
`expLo` and `expHi`, and it is documented as a non-kernel input.

```lean
hexp : expLo ≤ Real.exp (1/10) ∧ Real.exp (1/10) ≤ expHi
```

The conclusion they need is the off-line defect bracket `L ≤ defectFunctional excess ≤ U`. Here
`defectFunctional d = -(d^2)` and `excess = (exp(1/10) + exp(-(1/10))) - 2`. So the quantity is
one elementary expression:

```
-(exp(1/10) + exp(-1/10) - 2)^2
```

**Checked in Python today.** I ran `scaled_interval_eval_certificate` on that expression with the
island's own 150-digit constants `L` and `U` as the claim. It certifies at `S = 10^30` and at
`S = 10^40`. The DAG has 9 nodes and two exp nodes with `k = 0`. The root box width is 3 ulp,
far inside `[L, U]`.

**The discharge would take three steps.**

1. Add an instance to the zeta island. This needs a `[[require]]` on `ScaledInterval` from the
   island's lakefile, or a copy of the prelude onto the island's toolchain.
2. Emit `defect_offline_sie : L ≤ -((Real.exp (1/10) + Real.exp (-(1/10)) - 2)^2) ∧ ... ≤ U`.
   There is one subtlety: sympy writes `exp(-1/10)` with the constant `-1/10`, while the island
   writes `-(1/10)`. The bridge must equate the two forms with a short `norm_num` rewrite.
3. Write a two-line bridge that unfolds `defectFunctional`, `excess`, `Aoff` and `Aon`. It
   rewrites the goal to the emitted statement, proving `defect_witness_offline` with no `hexp`.
   `bragg_defect_witness` and `defect_leakage_gap` then follow unconditionally.

**Why bother when `exp_enclosure` already exists?** The `exp_enclosure` bridge discharges `hexp`
itself, through `norm_num` on Taylor sums. This route discharges the downstream bracket directly,
with no hand-written interval algebra between `hexp` and the defect bracket. The same instrument
then applies to every finite exp/polynomial seam.

**Next candidates.** The cos boxes in `BraggAmplitude` and `BraggH100` would follow once the
complex `CI` layer is added (cos(γu) = Re exp(iγu)). The design note lists that layer as optional,
and it is not built here. The seams that involve ζ, ξ, log or γ (`LiPositivity hlo`,
`RobinGrowth hR`, `LehmerPair`, `WeilFormEnclosure`) are not elementary. They are out of reach
until log and arg atoms exist (shape C3).

## Not done (honest scope)

- Complex intervals (`CI`), `inv`/`invPos`, `abs`, `log`, `sqrt`.
- Sharding of large DAGs into row files.
- A CI job in `.github/workflows/telperion-lean-e2e.yml`. Other islands have one, such as
  `exp-enclosure-compiles`; this island needs one before merging.
- The prelude lives in the Telperion examples tree, as the RHInertia prelude does. Under the
  licensing split (math is Apache-2.0 and ported OAI Lean belongs in the Apache math tree), the
  prelude may need to move. The Python generator is engine code.
