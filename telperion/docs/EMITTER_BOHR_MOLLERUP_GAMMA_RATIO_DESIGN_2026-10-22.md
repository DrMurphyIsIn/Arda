# `bohr_mollerup_gamma_ratio` -- a kernel-checked enclosure of `Real.Gamma x1 / Real.Gamma x2` at rational points (2026-10-22)

`conjecture1_proved = False`. Every theorem this kind writes is a two-sided rational bound on one ratio
of Gamma values at rational arguments in `(0, 1)`. It proves nothing about class numbers, nothing about
zeta, and nothing about RH.

Source: the emitter survey after the hand-built class-number-one Lean (`EMITTER_SURVEY_PHASE2.md` rev 2,
item N2, "the general form of E2", ranked 4th), and its independent review (REVIEW_E), which confirmed
that no module in the registry mentions `Real.Gamma`. The kernel-checked templates are the hand-built
`GammaBounds.lean` (the Bohr-Mollerup bounds and `Gamma_ratio_bounds`) and `GammaRatio.lean`
(`Gamma_ratio_enclosure : 2.1753 <= Gamma(3/8)/Gamma(7/8) <= 2.1755` at `n = 8000`, forty blocks of
200, about 10 s of kernel time) in the public tenth-discriminant repository, together with its generator
`gen_gamma_numbers.py`. Those are on Lean v4.34.1 / Mathlib d13f23b; this emitter is on v4.32.0 /
Mathlib v4.32.0, and the prelude ported without a single edit: every name it uses
(`Real.convexOn_log_Gamma`, `Real.BohrMollerup.f_add_nat_le`, `Real.Gamma_add_one`,
`Real.Gamma_pos_of_pos`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `pow_le_pow_iff_left₀`,
`le_div_iff₀`, `div_le_iff₀`, `div_le_div_iff₀`, `Finset.prod_range_add`, `Finset.prod_div_distrib`)
exists under the same name in the v4.32.0 pin.

## The shape that had no certificate type

The class-number proof needs the constant `Gamma(3/8)/Gamma(7/8)` to four digits. The hand-built route
is Bohr-Mollerup: Mathlib has the log-convexity of `Gamma` on `(0, oo)` and the inequality
`f_add_nat_le`, and from them, for `n >= 1` and `0 < x < 1`,

```
Gamma(n+1) (n+x)^(x-1)  <=  Gamma(n+x)  <=  Gamma(n) n^x .
```

With `Gamma(n+x) = Gamma(x) prod_{k<n} (x+k)` the ratio is enclosed by elementary functions of `n` times
an exact rational:

```
n (n+x1)^(x1-1) / n^x2 * P  <=  Gamma x1 / Gamma x2  <=  n^x1 / (n (n+x2)^(x2-1)) * P,
P = prod_{k<n} (x2+k)/(x1+k).
```

The two sides differ by the factor `(1+x1/n)^(1-x1) (1+x2/n)^(1-x2) = 1 + O(1/n)`, so the relative
width of the enclosure is about `(x1(1-x1) + x2(1-x2))/n`: each extra digit costs ten times the shift.
This is the same mechanism for every `x1, x2`, and only its numbers change: a shift `n`, the integer
product `P` as a ratio of two big naturals, four root brackets for the `rpow` factors, and two integer
comparisons. That is a certificate kind. The registry had enclosures of `exp(-theta)` (`bracket`), of
`Real.sqrt` of a rational (`algebraic_bracket`), fixed-point interval evaluation of `+ - * exp`
(`scaled_interval_eval`) and the discrete log-convexity law for sequences (`logconvex_interp`); none of
them bracketed a rational power `m^(p/q)` with `q > 2`, and none touched `Real.Gamma`.

## Statement family

One instance is `(x1, x2, n, S, K, LO, HI)`: two reduced rationals in the OPEN interval `(0, 1)`, a shift
`n = C K` (`K` the block size, default 200), a bracket scale `S` (default `10^12`), and the two claimed
bounds. The emitted theorem, for an instance named `nm`:

```
theorem nm : (LO : ℝ) ≤ Real.Gamma (a1 / q1) / Real.Gamma (a2 / q2)
           ∧ Real.Gamma (a1 / q1) / Real.Gamma (a2 / q2) ≤ (HI : ℝ)
```

`LO` and `HI` are spelled as decimal literals when they terminate (`2.174`, the hand-built statement's
spelling) and as `(p : ℝ) / q` otherwise. When they are not supplied, the generator takes the certified
bounds rounded outward to the enclosure's decimal resolution, `ceil(-log10(hi - lo))` digits.

Only the RATIO is enclosed. A single value `Gamma(x)` is not a face of this kind (nor was it needed).
Arguments outside `(0, 1)` are refused rather than reduced: `Gamma_add_one` reduction is the caller's.

## The certificate

Exact integers throughout; floats are refused at the door, including a float claim.

* `q = lcm(q1, q2)`, `a1' = x1 q`, `a2' = x2 q`; `gA = prod_{k<n} (q k + a2')`, `gB = prod_{k<n} (q k + a1')`,
  so `P = gA / gB` exactly. The products are DEFINED in Lean as `C` blocks of `K`
  (`∏ c ∈ range C, ∏ j ∈ range K, (q (K c + j) + a)`) and only the kernel ever evaluates them; Python
  computes them too, but only to decide whether to refuse.
* Four root brackets at scale `S`, each the floor or ceiling of an exact integer root
  (Newton from above, then an integer fix-up; `l^q a^p <= b^p S^q` or `m^p S^q <= u^q`):
  `l1/S <= (n+x1)^(x1-1)`, `n^x2 <= u2/S`, `n^x1 <= u3/S`, `l4/S <= (n+x2)^(x2-1)`. Each is about the
  REDUCED fraction (`(n q1 + a1)/q1` to the power `-(q1-a1)/q1`), so the product's common denominator
  never enters the real statement.
* The two kernel comparisons, which are exactly `LO <= n l1 gA/(u2 gB)` and `u3 gA/(n l4 gB) <= HI`
  cleared of denominators:

  ```
  key_lo : LOn * u2 * gB ≤ LOd * n * l1 * gA
  key_hi : HId * u3 * gA ≤ HIn * n * l4 * gB
  ```

The Python refusal and the kernel's decision are the SAME two predicates (`BohrMollerupGammaRatioCert.
key_lo_holds` / `key_hi_holds`, evaluated on the Python products), so a certificate the generator emits
compiles, and one the generator refuses would not have.

## Tactic skeleton

Per instance, twelve declarations (the emitted `gamma_3_8_over_7_8` at `n = 400`, abridged):

```
def nm_gA : ℕ := ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 7)
def nm_gB : ℕ := ∏ c ∈ Finset.range 2, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 3)
lemma nm_gA_eq : (∏ k ∈ Finset.range 400, (8 * k + 7)) = nm_gA := by
  rw [show (400 : ℕ) = 2 * 200 from rfl, BohrMollerupPrelude.prod_range_chunk]
  rfl
lemma nm_P_eq : (∏ k ∈ Finset.range 400, ((7 : ℝ) / 8 + k) / ((3 : ℝ) / 8 + k)) = (nm_gA : ℝ) / nm_gB := by
  rw [← nm_gA_eq, ← nm_gB_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : (3 : ℝ) / 8 + k ≠ 0 := by positivity
  have h1' : (8 : ℝ) * k + 3 ≠ 0 := by positivity
  push_cast; field_simp; ring
lemma nm_gB_pos : 0 < nm_gB := by
  unfold nm_gB; exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega
lemma nm_key_lo : 1087 * 189148321800636 * nm_gB ≤ 500 * 400 * 23629697132 * nm_gA := by decide +kernel
lemma nm_key_hi : 1000 * 9457416090032 * nm_gA ≤ 2177 * 400 * 472741662745 * nm_gB := by decide +kernel
lemma nm_hA : (23629697132 : ℝ) / 1000000000000 ≤ ((400 : ℝ) + 3 / 8) ^ ((3 : ℝ) / 8 - 1) := by
  have := BohrMollerupPrelude.rpow_rat_neg_div_lower 3203 8 5 8 23629697132 1000000000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num
-- nm_hB, nm_hC (rpow_div_upper), nm_hD likewise
theorem nm_aux (gA gB : ℕ) (gB_pos : 0 < gB) (P_eq : ... = (gA : ℝ) / gB) (key_lo : ...) (key_hi : ...) :
    (2.174 : ℝ) ≤ Real.Gamma (3 / 8) / Real.Gamma (7 / 8) ∧ ... ≤ (2.177 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := BohrMollerupPrelude.Gamma_ratio_bounds 400 (by norm_num)
    (x₁ := 3 / 8) (x₂ := 7 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [P_eq] at hlo hhi
  clear P_eq
  push_cast at hlo hhi
  ... two calc blocks: field_simp / le_div_iff₀ / linarith against key_lo, then gcongr with nm_hA nm_hB, then hlo
theorem nm : ... := nm_aux nm_gA nm_gB nm_gB_pos nm_P_eq nm_key_lo nm_key_hi
example : <the same type string> := nm          -- the statement gate
```

Two idioms carry over from the hand-built proof and are the reason it compiles at all. The real-number
argument is made for ABSTRACT `gA gB : ℕ`, with the product identity and the two comparisons as
hypotheses, and `P_eq` is `clear`ed before `positivity`, `linarith` or `field_simp` run: otherwise those
tactics try to normalise the thousand-digit product and hit `maxRecDepth` or the heartbeat limit
(`irreducible_def` does not help; `decide +kernel` then gets stuck). And the products are defined in
blocks, because the kernel's recursion depth is bounded by the block, not by `n`; the hand-built proof set
`maxRecDepth 4000` "defensively, not needed", and at `K = 200` nothing here needs it, so the emitted file
sets no options.

`decide +kernel` appears six times per instance (the two comparisons and the four root inequalities);
no `native_decide`, no `sorry`, no `axiom`, no heartbeat override.

## Prelude (`BohrMollerupPrelude.lean`)

Emitted from the same Python module as the instances (`bohr_mollerup_prelude_lean`), so the drift check
covers it; `import Mathlib` only. `Gamma_add_nat_eq`, `log_Gamma_add_one`, `Gamma_add_le`, `Gamma_add_ge`
and `Gamma_ratio_bounds` are the hand-built `GammaBounds.lean` verbatim; `prod_range_chunk` is the
hand-built `RpowBounds.lean` chunker; `rpow_div_upper` and `rpow_rat_neg_div_lower` are the two root
brackets this kind needs.

Those two brackets are a MINIMAL INLINE COPY of what survey item N1 (`nat_root_bracket_table`, being
built in parallel) ships as a general table prelude (the four `rpow_div_*` / `rpow_neg_div_*` lemmas, the
rational-base variant, the block transports). Once N1 merges, this prelude should import N1's and drop
its copies; nothing in the emitted instances changes except the two qualified names.

## Refusals (the forge face)

| phantom | why it is refused |
|---|---|
| `x1` or `x2` not in the open interval `(0, 1)` (including `0`, `1`, `9/8`) | the Bohr-Mollerup bounds are proved for `0 < x < 1`; reduce by `Gamma_add_one` first |
| a float anywhere (`0.375`, a float claim) | exactness; pass a `Fraction`, a sympy `Rational`, or a string |
| `n` not a positive multiple of the block size; `n > MAX_N = 20000`; `scale < 1` | the chunked definition needs `n = C K`; one file |
| claimed `LO` above the certified lower bound `lo = n l1 gA/(u2 gB)`, by any margin | `key_lo` is a FALSE `Nat` inequality; the message gives `lo`, the width and the remedy (lower the claim or raise `n`) |
| claimed `HI` below the certified upper bound | `key_hi` is FALSE, likewise |
| `LO > HI` | ill-formed |

The hand-built generator's control (`LO = 2.1754` at `n = 8000`; REVIEW_E C6 noted it was only PRINTED as
`key1: False` and caught downstream by a `grep`) is here a `ValueError` from `certify`, so
`generate.py` exits nonzero and nothing is written. `tests/test_emit_bohr_mollerup_gamma_ratio.py` pins
that exact instance, and pins that the refusal predicate is the emitted comparison.

## Negative control (`negctrl_adapters/adapter_bohr_mollerup_gamma_ratio.py`)

Stance CERTIFICATE_SENSITIVE: the four bracket integers and the two comparisons ARE the witness. The
adapter takes the honest `Gamma(3/8)/Gamma(7/8)` certificate at `n = 200` (certified `[2.173540, 2.177274]`, claims `2.173 .. 2.178`) and
forges `LO := HI = 2.178` by `dataclasses.replace`, past Layer 1 (which refuses it). Since `HI` is at or
above the certified upper bound it is strictly above the true value `2.17540591...`, so the forged
statement is a FALSE theorem, not merely an unprovable one; and `LO <= lo` fails exactly, so
`negctrl_forged_false_key_lo : 1089 * 103133853772125 * gB ≤ 500 * 200 * 36420658219 * gA` is a false
`Nat` inequality and `decide +kernel` reports it. The TRUE twin is the unmodified certificate. The two
texts differ only in the lines that carry the lower claim (the test pins this). Both elaborate over
`import Mathlib` with the prelude body spliced in, so the generic harness needs no island.

## Dogfood (`examples/bohr_mollerup_gamma_ratio`)

Three instances at `n = 400` (two blocks of 200), brackets at `10^12`, generated by `generate.py`
(`--check` for drift; `test_example_regenerates_byte_for_byte` pins the bytes):

| theorem | statement | true value | certified `[lo, hi]` | width |
|---|---|---|---|---|
| `gamma_3_8_over_7_8` | `2.174 ≤ Γ(3/8)/Γ(7/8) ≤ 2.177` | 2.1754059157 | `[2.174472, 2.176340]` | 1.87e-3 |
| `gamma_1_3_over_2_3` | `1.977 ≤ Γ(1/3)/Γ(2/3) ≤ 1.98` | 1.9783642596 | `[1.977266, 1.979463]` | 2.20e-3 |
| `gamma_1_2_over_1_4` | `0.4886 ≤ Γ(1/2)/Γ(1/4) ≤ 0.4892` | 0.4888705337 | `[0.488603, 0.489138]` | 5.34e-4 |

The third has distinct denominators: the exact product runs over the common denominator 4
(`gA = ∏ (4k+1)`, `gB = ∏ (4k+2)`) while the brackets and the statement use `1/2` and `1/4`. At the
hand-built `n = 8000` the same generator reproduces the hand-built integers exactly
(`l1 u2 u3 l4 = 3635432077, 2601379650496946, 29084308668980, 325168010868`) and the enclosure
`[2.175359180, 2.175452652]`, width 9.35e-5.

## Measurements (2026-10-22, Lean v4.32.0, local build, machine shared with another builder's run)

`lake build` of the example: `BohrMollerupPrelude` 3.8 s, `BohrMollerupGammaRatio` (the three
instances) 4.5 s; 58 s wall including Mathlib's olean check. Single files through `lake env lean`
against the built prelude, wall / user (the user column is the one to read; the wall clock includes
import of Mathlib and contention):

| file | wall | user |
|---|---|---|
| `import BohrMollerupPrelude` only (baseline) | 5.1 s | 2.0 s |
| one instance, `Γ(3/8)/Γ(7/8)`, `n = 400` (2 x 200) | 18.8 s | 3.1 s |
| one instance, `Γ(3/8)/Γ(7/8)`, `n = 8000` (40 x 200), the hand-built size | 8.2 s | 4.9 s |
| the TRUE twin of the control (`n = 200`, prelude spliced in) | 6.6 s | 4.6 s |

So the kernel's own share at the hand-built `n = 8000` is about 3 s of user time here (the hand-built
record on v4.34.1 says about 10 s; the products have 34,977 digits either way), and at `n = 400` it is
about a second. Width achieved: `1.87e-3` at `n = 400`, `9.35e-5` at `n = 8000` (table above).

The negative control's rejection, verbatim (the forged `key_lo` at line 210 of the spliced file):

```
scratch/NegCtrlForged.lean:210:2: error: [Error pretty printing: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information]
```

`decide +kernel` evaluated the comparison to `false` and then tried to print the thousand-digit
proposition in its failure message, which is what exhausts the pretty-printer's recursion depth; the
declaration is not added and `lean` exits 1. The true twin compiles with no output and exits 0.

## What it does NOT do

* It proves nothing about class numbers and nothing about RH; the class-number proof's use of the
  constant is downstream of this kind, not inside it.
* It does not enclose a single `Gamma(x)`, a Beta function, or `Gamma` at a non-rational or
  out-of-`(0, 1)` argument. The ratio-only shape is what `Gamma_ratio_bounds` gives for free; a
  single-value face would need an independent handle on one Gamma value.
* It does not pick `n` for a requested width: the caller sets `n`, and the generator reports the width
  it achieved and refuses a claim it cannot meet. The width formula above is the sizing rule.
* It does not shard: one file per family, `n <= 20000`. Larger `n` is the hand-built proof's territory
  (block count grows linearly; the hand-built 8000 took about 10 s on v4.34.1).
* The root brackets duplicate N1's prelude until N1 lands (above).
* `List`/`Array` block tables, range SUMS and the `sum_block_*` transports of the hand-built
  `RpowBounds.lean` are N1's, not this kind's.

## Provenance

Built 2026-10-22 from the survey's N2 section and the hand-built CN-1 Lean, as one of the five emitter
shapes the user decided to build. The prelude is the hand-built Lean ported to v4.32.0 (no edits
needed); the generator is a rewrite of `gen_gamma_numbers.py` with the common-denominator product,
reduced-fraction brackets, decimal claim rounding, and the refusal in place of the printed flag.
