# `nat_root_bracket_table` -- kernel-decided brackets of `m^(+-p/q)`, singly and as blocked range-sum tables (2026-10-22)

`conjecture1_proved = False`. Everything below is a finite arithmetic fact about a rational power of
a rational number, or about a partial sum of such powers (`L/S <= sum_{i<M} (i+1)^(-p/q) <= U/S`).
Nothing here says anything about the zeros of zeta or about class numbers, and nothing here is a step
toward RH.

Source: the CN-1 emitter-shape survey, phase 2 (rev 2), item N1 `nat_root_bracket_table`, ranked
first of the five shapes the user decided to build; its independent review (REVIEW_E) found the
registry dedupe to hold and added the design note that the single-bracket face is the natural
`rpow_rat` atom of phase 1's E0. The kernel-checked template is the hand-built CN-1 formalization
in the public `tenth-discriminant` repository: `formalization/CN1/Numerics/RpowBounds.lean` (the
transport lemmas, PROVED on Lean v4.34.1 / Mathlib d13f23b), the generated `ZetaTables.lean`
(about 3000 bracket instances in 60 kernel-decided block facts) with its generator
`certificates/gen_zeta_tables.py`, and the rational-base lemma `rpow_rat_neg_div_lower` of
`GammaRatio.lean`. Module: `src/telperion/emit_nat_root_bracket_table.py`.

## The shape that had no certificate type

Every numeric input of the CN-1 proof is one object: a natural-number inequality that the kernel
decides on literals, transported once to a real `rpow` bound.

| CN-1 site | what it proves | face |
|---|---|---|
| `ZetaTables.lean` (generated; sigma = 3/4, 7/8, 7/4; M = 1000 = 5 x 200; scale 10^10) | `L/10^10 <= sum_{n<1000} (n+1)^(-sigma) <= U/10^10` from 60 kernel-decided block facts | table |
| `ZetaValues.lean` `n1001_*` (scale 10^12) | `1001^(1/4)`, `1001^(-3/4)`, `1001^(-7/4)`, `1001^(1/8)`, `1001^(-7/8)`, `1001^(-15/8)`, `1001^(-11/4)` to one ulp | single, natural base, both signs |
| `GammaRatio.lean` `g_hA`..`g_hD` (scale 10^12) | `(8000 + 3/8)^(-5/8)`, `8000^(7/8)`, `8000^(3/8)`, `(8000 + 7/8)^(-1/8)` | single, rational base |
| `Threshold.lean` constants | the `d_0 = 655` archimedean factors | single |

The registry had no q-th-root bracket for `q > 2` and nothing that blocks a 1000-term range sum
through kernel-decided naturals (see "Dedupe" below).

## Statement family

One kind, two faces. `p, q, S >= 1` are naturals; the exponent is written exactly as the prelude
lemmas state it, `(-((p : ℝ) / q))` or `((p : ℝ) / q)`.

**The single face** (`K = 1`; a natural base `m` or a rational base `a/b` in lowest terms):

```
theorem nm_lo_fact : L ^ q * m ^ p ≤ S ^ q := by decide +kernel          -- negative exponent
theorem nm_hi_fact : S ^ q ≤ U ^ q * m ^ p := by decide +kernel
theorem nm : (L : ℝ) / S ≤ (m : ℝ) ^ (-((p : ℝ) / q)) ∧ (m : ℝ) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S
```

with the facts `L ^ q ≤ m ^ p * S ^ q`, `m ^ p * S ^ q ≤ U ^ q` for a positive exponent, and
`L ^ q * a ^ p ≤ b ^ p * S ^ q`, `b ^ p * S ^ q ≤ U ^ q * a ^ p` (negative) or
`L ^ q * b ^ p ≤ a ^ p * S ^ q`, `a ^ p * S ^ q ≤ U ^ q * b ^ p` (positive) for the base
`((a : ℝ) / b)`.

**The table face** (negative exponent, the PROVED transport; `M = C * K`): per block `c < C`

```
def nm_lo_c : List ℕ := [...]            def nm_hi_c : List ℕ := [...]
theorem nm_lo_c_fact : ∀ n < K, (nm_lo_c.getD n 0) ^ q * (K * c + n + 1) ^ p ≤ S ^ q := by decide +kernel
theorem nm_hi_c_fact : ∀ n < K, S ^ q ≤ (nm_hi_c.getD n 0) ^ q * (K * c + n + 1) ^ p := by decide +kernel
theorem nm_lo_c_sum : ∑ n ∈ Finset.range K, nm_lo_c.getD n 0 = <literal> := by decide +kernel
theorem nm_hi_c_sum : ...
```

and the three real theorems

```
theorem nm_lo : (L_tot : ℝ) / S ≤ ∑ i ∈ Finset.range M, ((i : ℝ) + 1) ^ (-((p : ℝ) / q))
theorem nm_hi : ∑ i ∈ Finset.range M, ((i : ℝ) + 1) ^ (-((p : ℝ) / q)) ≤ (U_tot : ℝ) / S
theorem nm : nm_lo ∧ nm_hi
```

followed by the statement gate `example : <type of nm> := nm`.

## The certificate

`NatRootBracketCert(num, den, p, q, sign, scale, lo, hi)` and
`NatRootBracketTableCert(p, q, scale, block, n_blocks, lo_blocks, hi_blocks, lo_sums, hi_sums,
lo_total, hi_total)`, all Python ints. Untrusted Python computes, in exact integer arithmetic:

1. **The integer q-th root by Newton's method** (`nat_iroot`): from the power of two
   `2^ceil(bits(x)/q) >= x^(1/q)` iterate `r <- ((q-1) r + x // r^(q-1)) // q` until it stops
   decreasing, then verify `r^q <= x < (r+1)^q`. No floats anywhere, and no decrement loop (the
   CN-1 generator's note: a 10^12-scale root by decrement hung for over two minutes).
2. **The tightest bracket.** For the negative exponent, `X = (den^p S^q) // num^p`, `lo = iroot(X, q)`,
   `hi = lo` when `lo^q num^p = den^p S^q` and `lo + 1` otherwise; so `hi - lo <= 1` and the two
   facts the kernel decides hold by construction and are re-asserted before emission. The positive
   exponent swaps `num` and `den`. An exact power (`16^(-3/4) = 1/8`) collapses to `lo = hi`.
3. **A supplied endpoint** (single face only) is checked against the SAME integer fact the kernel
   will decide and refused if it fails; it may be looser than the tightest one, never tighter.
4. **The table** is the single bracket at `m = K c + n + 1` for every `n < K`, `c < C`, plus the
   per-block sums and their totals, which are what the block-sum theorems and the final statement
   quote.

The emitted proof term is fully determined by the certificate: every ℕ fact is `decide +kernel`
on literals (`Nat.pow`, `Nat.mul`, `Nat.ble` and `Nat.decidableBallLT` reduce in the kernel with
GMP-accelerated arithmetic), and the real side is one prelude lemma application per fact plus
`exact_mod_cast` (single face) or `sum_range_chunk` + `Finset.sum_range_succ` + `push_cast` +
`linarith` (table face). The kernel's recursion depth is bounded by `K` (the `∀ n < K` and the
`range K` sum), never by `M`; `C` only lengthens the `linarith` call.

## Tactic skeleton (the hand proofs' own lines)

```
-- single bracket (ZetaValues.lean n1001_*, GammaRatio.lean g_hA: the same lemma applications)
have h1 := rpow_neg_div_lower m p q L S (by norm_num) (by norm_num) (by norm_num) nm_lo_fact
have h2 := rpow_neg_div_upper m p q U S (by norm_num) (by norm_num) (by norm_num) nm_hi_fact
exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
-- blocked sum (ZetaTables.lean zsum34_lo, verbatim)
set f : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ (-((p : ℝ) / q)) with hf
have hf' : ∀ i, f i = ((i : ℝ) + 1) ^ (-((p : ℝ) / q)) := fun i => by rw [hf]
have h0 := sum_block_lo_neg f (-((p : ℝ) / q)) p q S K (K * 0) (by norm_num) (by norm_num) rfl hf' nm_lo_0 nm_lo_0_fact
rw [nm_lo_0_sum] at h0
...
rw [show (M : ℕ) = C * K from rfl, sum_range_chunk f C K]
rw [Finset.sum_range_succ, ..., Finset.sum_range_zero, zero_add]
push_cast at h0 ... ⊢
linarith
```

Two departures from the hand-built files, both forced by the pin:

* the hand proofs close the single brackets with `convert this using 2 <;> norm_num` (and the
  statement carries the consumer's own exponent expression, `1 - (3 : ℝ) / 4`); the emitter states
  the exponent in the lemma's form and closes with `exact_mod_cast`, which needs no `convert`.
  A consumer whose exponent is spelled differently must `convert` on its own side (the survey's
  open check 6, "exponent hygiene"); the emitter does not take a consumer term as input;
* inside the prelude, `sum_block_lo_neg/hi_neg` end in `convert this using 2; push_cast; ring` on
  v4.34.1. On v4.32.0 that `convert` leaves an instance goal `Real.instPreorder.toLE = Real.instLE`
  that `ring` cannot touch (kernel-observed: "ring_nf made no progress"), so the port rewrites the
  one cast `((base + n : ℕ) : ℝ) + 1 = ((base + n + 1 : ℕ) : ℝ)` explicitly and finishes with
  `exact this`. The statements are unchanged.

## The prelude

`NatRootBracket.lean` (module `NatRootBracket`, Mathlib only, 190 lines; the single source is
`telperion.nat_root_bracket_prelude_lean()`, written by the example's `generate.py` and drift-checked
by `--check`): `rpow_div_lower/upper`, `rpow_neg_div_lower/upper` (RpowBounds.lean :26-75, ported),
`rpow_rat_neg_div_lower` (GammaRatio.lean :32, ported) and its three siblings
`rpow_rat_neg_div_upper`, `rpow_rat_div_lower`, `rpow_rat_div_upper` (new, by the same proof),
`sum_range_chunk` (:78) and `sum_block_lo_neg/hi_neg` (:99, :114). Mathlib names used, all present at
v4.32.0: `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_nonneg`,
`pow_le_pow_iff_left₀`, `div_le_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `div_mul_cancel₀`,
`div_pow`, `inv_div`, `Finset.sum_range_add`, `Finset.sum_le_sum`, `Nat.cast_sum`. The prelude
builds in about 29 s on v4.32.0 (COMPUTED, this machine); its axioms are
`[propext, Classical.choice, Quot.sound]`.

## Refusals (the forge face)

| phantom | why it is refused |
|---|---|
| a supplied `lo` with `lo^q * A > B`, or a supplied `hi` with `B > hi^q * A` (the forge `U := L` on a non-exact bracket) | exactly the fact the kernel decides; the `_fact` would be false (the negative control) |
| `p < 1`, `q < 1`, `scale < 1` | `m^0 = 1` carries no content; `q = 0` and `S = 0` are outside the lemmas' hypotheses |
| a base `<= 0`, or a `(num, den)` pair with a zero | `0 < m` is a hypothesis of the negative-exponent lemmas; a zero base is a reflexive stub |
| floats, sympy `Float`s, bools, non-integers, non-rational bases (`sqrt 2`) | exactness; a float scale or exponent would silently round |
| `sign` not `-1` or `+1` | the two lemma families are the whole kind |
| a block size above `MAX_BLOCK`, or `terms` not a positive multiple of the block | the measured kernel-depth cap (next section); the sum is chunked as `C * K` |
| more than `MAX_BLOCKS = 64` blocks | one file; sharding across files is future work (each block is independent, so the split is free) |
| a Lean name that is not an identifier | hygiene |

Every refusal has its own test in `tests/test_emit_nat_root_bracket_table.py`.

## Depth measurement on Lean v4.32.0 (survey open check 1)

The survey's figures (ℚ range sums of about 1500 terms exhaust the kernel's recursion depth; blocks
of 300 pass; CN-1 used `K = 200` with `maxRecDepth 4000` set defensively) were COMPUTED on
v4.33.0-rc2 and v4.34.1. Re-measured here on the pinned v4.32.0 / Mathlib v4.32.0, with one file
per row holding the two shapes the table face emits (`∀ n < K, (tbl.getD n 0)^4 * (n+1)^3 ≤ (10^10)^4`
and `∑ n ∈ range K, tbl.getD n 0 = <literal>`, both `decide +kernel`, no `set_option` unless stated;
wall time is `lake env lean` on a warm Mathlib, this machine):

| K | `List ℕ` (default options) | wall time | `Array ℕ` (default options) |
|---|---|---|---|
| 200 | PASS | 23.1 s and 40.0 s re-timed on a loaded machine (the CN-1 default; a first run logged 1073 s, which was time spent queued behind another builder on the shared Lean slot, not elaboration) | PASS, 6.6 s |
| 300 | PASS | 6.7 s | -- |
| 500 | PASS | 11.3 s | PASS, 16.1 s |
| 1000 | PASS | 34.4 s | -- |
| 1500 | PASS | 76.4 s | -- |
| 2000 | FAIL: "maximum recursion depth has been reached" at the `def tbl : List ℕ := [...]` line itself, with the default `maxRecDepth` AND with `set_option maxRecDepth 4000`; the two kernel facts were never reached | 135 s | -- |

So on this pin the binding limit is the ELABORATOR's recursion depth on a 2000-element list literal,
not the kernel's evaluation of the `∀ n < K` fact or of the range sum, both of which pass at
K = 1500 with no option set.  The `Array` literal buys nothing (the kernel has no array
acceleration and `#[...]` is `List.toArray` of the same literal), so it is not emitted.  The time
grows faster than linearly in K (`List.getD` is O(n) per lookup, as the survey noted), which is a
second reason to keep blocks small and let `C` grow instead.  Re-timed K = 200 twice at the end of the session: 40.0 s and 23.1 s, while other builders' lake
jobs were running on the same machine (the 6.6 s Array figure and the 6.7 s K = 300 figure were taken
in a quiet window), so the per-K times above are upper bounds on a loaded machine, not benchmarks;
the PASS/FAIL column is what the measurement is for.

The default block of 200 is kept (it is what CN-1 shipped and it needs no option on this pin);
`MAX_BLOCK` is set at the largest block that passed with the default options, not beyond it. The
emitted files set no `maxRecDepth`.

## Negative control (`negctrl_adapters/adapter_nat_root_bracket_table.py`)

Stance CERTIFICATE_SENSITIVE: the emitted theorems carry the supplied naturals `L`, `U` (and, on the
table face, two `List ℕ` per block plus the block sums) as literal witnesses, and a corrupted witness
must break the claim.

FALSE twin: the honest table for `∑_{i<40} (i+1)^(-3/4)` at scale `10^10` in two blocks of 20, with
the entry `n = 7` of the second block's `lo` list raised by 1 (block sum and total recomputed so the
forgery is internally consistent), hand-minted past Layer 1 with `dataclasses.replace`. The tightest
`lo` satisfies `lo^4 m^3 <= 10^40 < (lo+1)^4 m^3` at `m = 28`, so the block's `∀`-fact is FALSE and
`decide +kernel` fails on `_lo_1_fact`; the final theorem loses its hypothesis with it. The forged
CLAIM stays TRUE: the forged lower total `66495196525/10^10 = 6.6495196525` is still below the true
sum `6.64951965419698...` (COMPUTED, mpmath at 50 digits; pinned by
`test_adapter_twins_differ_by_one_entry_only`), so what the kernel rejects is a corrupted WITNESS
under a true claim, which is what CERTIFICATE_SENSITIVE requires. TRUE twin:
the honest certificate, compiles over `import Mathlib` plus the spliced prelude, with
`[propext, Classical.choice, Quot.sound]`. The emitted texts differ in the forged list, its block
sum and the totals in the final statements (`test_adapter_twins_differ_by_one_entry_only` pins
this). A second, Lean-gated control forges `U := L` on the single face (`2^(-1/2)` at scale `10^6`,
`707107 -> 707106`): `10^12 <= 707106^2 * 2` is false and `_hi_fact` is rejected. Run by hand on
the island: FALSE twin `decide` fails (the kernel evaluates the proposition to `false`), TRUE twin
exit 0, clean; the output is kept with the build record.

## Dedupe (why the registry did not already have this)

* `algebraic_bracket` (`AlgebraicBracketEmitter`): `lo <= Real.sqrt a <= hi` for a rational `a`,
  closed by `Real.le_sqrt_of_sq_le` / `Real.sqrt_le_iff` and `norm_num`. That is `q = 2` with no
  exponent `p`, no natural-base `rpow`, and `norm_num` (not the kernel) deciding the squares; it has
  no table and no range sum.
* `bracket` (`IntervalBracketEmitter`): two-sided enclosure of `exp(-theta)` from a rational Taylor
  heart; a transcendental atom, no `rpow`, "log deferred".
* `enclosure_tree`: an interval fold over an expression tree whose root atom is `sqrt` only (exact
  integer square roots at a `10^-12` grid) and whose `^` is an integer exponent (`MAX_POW = 8`); it
  closes with `linarith`/`nlinarith`, not kernel-decided facts, and has no range sum. REVIEW_E's
  design note stands: this kind's single face is the natural `rpow_rat` atom such a tree could
  consume, and the blocked range-sum face is the part no registry kind had.
* `scaled_interval_eval`: fixed-scale integer boxes for `{+, -, *, integer powers, exp}` with
  `decide +kernel` subset checks; its operation set has no `rpow` and no root, and a sum of 400
  terms would be 400 DAG nodes with a one-ulp loss per operation rather than one block fact.
* `rpow_budget` (`RpowBudgetEmitter`): exponent-level `linarith` with the factor bounds as
  HYPOTHESES; it consumes brackets, it does not produce them.
* `exact_fact`, `exp_enclosure`, `transcendental_enclosure`, `tight_cap_enclosure`,
  `factored_endpoint_enclosure`, `enclosure_interval_fold`: none brackets a rational-exponent power
  (REVIEW_E closed the survey's open check 3 on the last four).

## Example (`examples/nat_root_bracket_table/`)

`generate.py` writes the prelude and `NatRootBracketTable.lean` (28 theorems, 20 generation-time
self-checks); `--check` pins both byte for byte and `telperion.toml` lists it in group `quick`.

| instance | statement | kernel work |
|---|---|---|
| `sum_neg34_400` | `144528468361/10^10 <= ∑_{i<400} (i+1)^(-3/4) <= 144528468758/10^10` | 2 blocks of 200: 4 `decide +kernel` block facts + 4 block sums |
| `sum_neg78_400` | `94886213312/10^10 <= ∑_{i<400} (i+1)^(-7/8) <= 94886213710/10^10` | the same at `q = 8` |
| `pow_1001_pos14` | `5624818578328/10^12 <= 1001^(1/4) <= 5624818578329/10^12` | 2 facts |
| `rat_64003_8_neg58` | `3635432077/10^12 <= (64003/8)^(-5/8) <= 3635432078/10^12` | 2 facts |

The first sigma = 3/4 block reproduces the CN-1 `ZetaTables.lean` `zlo34_0_sum / zhi34_0_sum`
(`116105226077 / 116105226275`) and the second its `zlo34_1 / zhi34_1` sums; the two singles are the
CN-1 `n1001_quarter` and `g_hA` endpoints, from an independent generator. `lake build` of the
emitted file takes about 34 s on v4.32.0 after the prelude (COMPUTED, this machine); the axiom guard
`AxiomGuardNatRootBracketTable.lean` prints the three Mathlib axioms for every capstone and the CI
job `nat-root-bracket-table-compiles` fails unless every `depends on axioms` line lists a subset of
those three (an allow-list; see the last section).

## What this does NOT guarantee

* **Statement intent.** The kernel checks that `L/S <= x <= U/S` for the `x` written; whether that
  `x` is the quantity a consumer means (the exponent spelled as `1 - 3/4` rather than `-(3/4)`, a
  base `8000 + 3/8` rather than `64003/8`) is the consumer's `convert`, not this emitter's. The
  emitter takes no consumer term as input.
* **Only the negative-exponent range sum is built.** `sum_block_lo_neg/hi_neg` is the PROVED CN-1
  transport; a positive-exponent sum face (`∑ (i+1)^(p/q)`) would need two more prelude lemmas and
  is not emitted. Sums with a base offset other than `i + 1` are not emitted either.
* **One file, at most 64 blocks.** Sharding a long sum across files is not implemented; the block
  facts are independent so it is a free follow-on, but nothing here does it.
* **`List.getD` is O(n) per lookup.** The measured times above are what the kernel pays for it at
  each `K`; an `Array` variant is measured for information and not emitted.
* **The brackets are one ulp wide at the chosen scale and no tighter.** A consumer that needs
  `10^-12` must ask for `scale = 10^12`; the emitter never widens a claim and never rounds a total.
* **The example compiles in CI; a user's instance is checked when the user builds it.** Nothing in
  the Python layer is trusted: a Layer-1 refusal is a convenience, and the kernel is the arbiter.
* **The CI axiom guard is an allow-list, and only that.** It fails the job unless every
  `depends on axioms` line of `AxiomGuardNatRootBracketTable.lean` lists a subset of `propext`,
  `Classical.choice`, `Quot.sound`. A deny-list for `sorryAx | ofReduceBool` would NOT catch
  `native_decide` on this pin, which produces a per-theorem axiom `<thm>._native.native_decide.ax_1_1`
  rather than `Lean.ofReduceBool` (REVIEW_PR765 C1), and Lean wraps a long axiom list one axiom per
  line, so a line-based check reads only `[propext,` and accepts the hidden axiom (REVIEW_PR766
  Add.1, demonstrated on real v4.32.0 output). The step therefore joins the lines, parses every closed
  `depends on axioms: [...]` list whole, requires one closed list per header and exactly ten anchors,
  and allow-lists with fixed strings (`grep -vxF`; with `-E` the dot in `Classical.choice` matches a
  look-alike). `test_ci_axiom_guard_is_an_allow_list` EXECUTES the step's run block against fixtures
  under `tests/fixtures/nat_root_bracket_table/`: the real guard output (accept), the real wrapped
  `native_decide` output (reject), a wrapped `sorryAx` (reject), a look-alike axiom name (reject) and
  ten axiom-free declarations (accept). The guard covers the declarations it names and no others.
* **Nothing about zeta or class numbers.** `conjecture1_proved = False`.
