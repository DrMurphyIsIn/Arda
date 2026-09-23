# `exp_threshold` -- from a threshold on the width to exponential domination (2026-09-22)

`conjecture1_proved = False`. Everything below is an elementary real inequality: a threshold
hypothesis on a real parameter implies an exponential bound, by `1 + t <= e^t`. Nothing here says
anything about the zeros of zeta, and nothing here is a step toward RH.

Source: `SHAPES_AUDIT_48H_2026-09-22.md` section 2 (rank 5, "value per line"), merging
`SHAPES_AUDIT_B_WEIL_WALL_2026-09-22.md` N2 and `SHAPES_AUDIT_C_B7_PARTIAL_FRACTION_2026-09-22.md`
4.5. Build order: sprint 1, item 3.

## The shape that had no certificate type

Every "for lam beyond an explicit threshold the exponential wins" closure in the Weil-wall cluster
is written by hand, and the same eight lines recur (B N2 counted six sites, C 4.5 four more):

| site | what it proves | mode |
|---|---|---|
| `E6Bridge7.lean:575-590` (`hexpeta`, `hexpM`) | `A/(2 eta K) <= lam -> A <= K e^{2 lam eta}`, and the strict twin for `B`, `M` | linear, twice |
| `E6Bridge12.lean:311-316` (`hexpkappa`) | `e^{-2 lam kappa} (2 lam kappa) <= 1` | product |
| `E6Bridge14.lean:78-86` (`le_exp_of_log_le`) | `log(max 1 Q)/(2 a) <= lam -> Q <= e^{2 lam a}` | log (the only site factored into a lemma) |
| `E6Bridge11.lean:1084-1095` | `e^{-x} <= 1/x` at `x >= 64000` | inv, rational floor |
| `E6Bridge11.lean:910-925` (`bumpR_le`), `E6Bridge16.lean:315-317` (`hye`) | `y e^{-y} <= 1` | product |

`eventual_threshold` already emits the max-of-ratios witness `p0 = max(a_i/c_i)`; what was missing
is the kind that CONSUMES each conjunct into an exponential. The audit also asked for the
`max 1 (...)` guard to be accepted as an ordinary conjunct (B C1, section 2.3 fold-in): this kind
reads the whole nested-max hypothesis and returns the guard alongside the consequences.

## Statement family

One theorem per instance. A **bundle** instance (mode `linear`, `log`, or `mixed`) states

```
theorem nm (<symbols> lam : R) (h<a>0 : 0 < a) ... (h<K>0 : 0 < K) ...
    (h : max 1 (max t_1 (max t_2 ... t_n)) <= lam) :
    1 <= lam /\ C_1 /\ ... /\ C_n
```

(the guard `1` and the outer `max` are omitted when absent; a single unguarded step is
`t_1 <= lam -> C_1`), where each step is

| mode | threshold `t` | consequence `C` | route |
|---|---|---|---|
| `linear` | `Q / (s * a * K)` | `Q <= K * exp (s * lam * a)` (`<` when `strict`) | `div_le_iff0` + `Real.add_one_le_exp` + `linarith`, then `rwa [div_le_iff0, mul_comm]` to clear `K` |
| `log` | `Real.log (max 1 (Q / K)) / (s * a)` | `Q <= K * exp (s * lam * a)` | `lt_max_of_lt_left one_pos` + `Real.exp_log` + `Real.exp_le_exp`, then the same `K`-clearing tail |

`K` is optional (the audit's "downstream `Q <= K exp(lam a)` after clearing `Q/K`"); `s` is a
positive rational (the cluster's `2 * lam * eta`); `Q`, `a`, `K` are each INDEPENDENTLY a symbol
(a universally quantified real, with `0 < a`, `0 < K` as hypotheses) or an exact rational literal
(then the threshold is an exact number the generator computes and the kernel re-decides the signs
by `positivity` / `norm_num`). The linear route needs no sign on `Q` (`Q <= s lam a <= s lam a + 1
<= e^{s lam a}`); the log route makes `Q <= 0` trivial (`Q <= max 1 Q`).

Standalone **atoms** (no threshold hypothesis):

| mode | statement | route |
|---|---|---|
| `product` | `y * exp (-y) <= 1` and `nm_comm : exp (-y) * y <= 1` | `Real.exp_neg` + `div_le_one` / `inv_mul_le_iff0` + `Real.add_one_le_exp` |
| `inv` | `0 < x -> exp (-x) <= 1 / x`; floor face `x0 <= x -> exp (-x) <= bound` | `Real.exp_neg` + `one_div` + `inv_anti0`; `one_div_le_one_div_of_le` + `norm_num` |
| `shifted_rate` | `0 <= y -> (c1 * y + c0) * exp (-(r * y)) <= K * exp (-(r' * y))` | `Real.add_one_le_exp` at `r - r'`, `mul_le_mul_of_nonneg_left/right`, `Real.exp_add` + `ring` |

## The certificate

`ExpThresholdCert(mode, steps, guard, lam, ...)` with one `ExpThresholdStep(mode, Q, a, K, scale,
strict, threshold)` per conjunct. Untrusted Python computes, in exact arithmetic:

1. each quantity as a symbol or an `sp.Rational` (floats refused);
2. the EXACT threshold expression of each step -- `Q/(s a K)` or `log(Max(1, Q/K))/(s a)` -- which
   the emitted hypothesis states verbatim; when the proposer DECLARES a `threshold`, it must match
   this recomputation exactly (`sp.simplify` of the difference is `0`), otherwise the instance is
   refused: the proposer never gets to state a threshold the route does not certify;
3. for `shifted_rate`, the constant `K = max(c0, c1/(r - r'), 0)` (or a declared `K` at least
   that): the `1 + t <= e^t` route proves `c1 y + c0 <= K (1 + (r - r') y)`, which needs exactly
   `c0 <= K` and `c1 <= K (r - r')` on `y >= 0`;
4. for `inv`, `bound >= 1/x0` (the route proves exactly `1/x0`).

The emitted proof term is fully determined by the certificate: no tactic searches (no `nlinarith`
hint lists, no `decide`, no `simp` sets), only `linarith` on named hypotheses with numeral
coefficients, `positivity` on products of positive atoms, and `norm_num` on rational literals.

## Tactic skeleton (verbatim from the hand proofs)

Linear step with `K` (E6Bridge7.lean:576-590), reading `ht : Q / (s * a * K) <= lam`:

```
have h1 : Q / K ≤ s * lam * a := by
  rw [div_le_iff₀ hK0]
  have := (div_le_iff₀ (by positivity : (0 : ℝ) < s * a * K)).mp ht
  linarith
have h2 : s * lam * a + 1 ≤ Real.exp (s * lam * a) := Real.add_one_le_exp _
have h3 : Q / K ≤ Real.exp (s * lam * a) := by linarith          -- `<` when strict
rwa [div_le_iff₀ hK0, mul_comm] at h3                               -- `div_lt_iff₀` when strict
```

Log step (E6Bridge14.lean:78-86), reading `h : Real.log (max 1 Q) / (s * a) <= lam`:

```
have hmax : 0 < max 1 Q := lt_max_of_lt_left one_pos
have h1 : Real.log (max 1 Q) ≤ s * lam * a := by
  have := (div_le_iff₀ (by positivity : (0 : ℝ) < s * a)).mp h
  linarith
calc Q ≤ max 1 Q := le_max_right _ _
  _ = Real.exp (Real.log (max 1 Q)) := (Real.exp_log hmax).symm
  _ ≤ Real.exp (s * lam * a) := Real.exp_le_exp.mpr h1
```

Bundle extraction (E6Bridge7.lean:568-573): `have hlam1 : 1 ≤ lam := (le_max_left _ _).trans h`,
then `((le_max_left _ _).trans (le_max_right _ _)).trans h` for the first threshold and
`le_max_right` chains for the rest; `refine ⟨hlam1, ?_, ..., ?_⟩` and one bullet per step.

Product (E6Bridge11.lean:914-916 / E6Bridge12.lean:311-316), inverse (E6Bridge11.lean:1090-1093)
and shifted-rate routes are in `emit_exp_threshold.py`; each is a fixed block with the instance's
literals substituted.

## Refusals (the forge face)

| phantom | why it is refused |
|---|---|
| rational `a <= 0` | the exponent `s lam a` shrinks with `lam`; the implication is FALSE at `lam = 0` (the negative-control forgery) |
| rational `K <= 0` | the `K`-clearing step divides by `K` |
| `scale <= 0`, non-rational scale | same exponent-direction failure |
| declared `threshold` not matching `Q/(s a K)` or `log(max 1 (Q/K))/(s a)` | the audit's "a rational `Q` whose `Q/a` or `log(max 1 Q)/a` does not match the declared threshold" |
| `strict` in `log` mode | the `max 1` route has no `+1` slack |
| an atom inside a bundle, a guard or steps on an atom, `K` on `product` / `inv` | shape mismatch |
| empty bundle, arity `> 6`, both `steps` and single-step keywords | ill-formed |
| `inv` with `x0 <= 0`, or `bound < 1/x0`, or a bound without a floor | the route proves exactly `1/x0`; a tighter claim belongs to `exp_enclosure` |
| `shifted_rate` with `r' >= r`, or `K` below `max(c0, c1/(r - r'), 0)` | no rate to trade / the affine domination fails |
| floats anywhere, non-identifier or reserved symbol names, a quantity named like `lam`, a symbol colliding with a generated hypothesis name | exactness and hygiene |

## Negative control (`negctrl_adapters/adapter_exp_threshold.py`)

FALSE twin: the linear instance `Q = 3`, `a = -1`, `s = 2`, hand-minted past Layer 1. The emitted
statement `3 / (2 * (-1)) <= lam -> 3 <= exp (2 * lam * (-1))` is false at `lam = 0`, and the
kernel rejects the proof at `(by positivity : (0 : ℝ) < 2 * ((-1) : ℝ))`. TRUE twin: `a = 1`,
same everything else, compiles over `import Mathlib` alone. The two texts differ only in the sign
literal (`tests/test_negctrl_exp_threshold.py` pins this).

## Dogfood targets (`examples/rvm_bridge/lean/Probes/Dogfood_exp_threshold.lean`)

Generated by `examples/rvm_bridge/dogfood_exp_threshold.py` (`--check` for drift; the test
`test_dogfood_file_is_regenerable_byte_for_byte` pins the bytes). It imports `E6Bridge7` and
`E6Bridge14` and states the regenerated lemmas under NEW names, so the lead can compile it on the
island without touching the originals:

```
cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_exp_threshold.lean
```

| emitted theorem | regenerates | kernel cross-check appended |
|---|---|---|
| `gaussian_dominance_thresholds` | `E6Bridge7.lean:554-590`: `lam0`, `hlam1`, `hlamA`, `hlamB`, `hexpeta`, `hexpM` as one guarded linear bundle | `example` deriving `hexpeta ∧ hexpM` from the `lam0 <= lam` hypothesis |
| `le_exp_of_log_le_regen` | `E6Bridge14.lean:78-86` `le_exp_of_log_le` | both directions: each proves the other's statement |
| `effectiveThreshold_consequences` | `E6Bridge14.lean:66-75, 281-291`: `effectiveThreshold` unfolded, `hlam1`, `hthr1`, `hthr2`, `hQ1`, `hQ2` | `example` consuming `RvMBridge14.effectiveThreshold y0 xmin N B D <= lam` by definitional unfolding |

Expected axioms for every theorem: `[propext, Classical.choice, Quot.sound]` (the probe prints
them). `tests/test_emit_exp_threshold.py` additionally asserts, line by line, that the emitted
tactic blocks are the island's own lines (E6Bridge7 with `eta` for `η`; E6Bridge14 verbatim).

## What it does NOT do

* It proves nothing about zeros or about RH; every instance is already kernel-checked by hand on
  the island. The value is regeneration and the kernel gate on the next island.
* The `shifted_rate` mode is the audit's `P(y) e^{-r y} <= K e^{-r' y}` restricted to AFFINE `P`
  with RATIONAL rates, the case the `1 + t <= e^t` discipline actually proves. The four C 4.5
  sites are not instances of it: `E6Bridge16.lean:315-317` and `E6Bridge11.lean:910-925` are
  `product` atoms (`y := lam c^2`, `y := 2 lam (r - c)^2`); `E6Bridge16.lean:352-364`
  (`sqrt lam e^{-lam/2} <= 1`) is a square-root face (`Real.sqrt_le_left` + `Real.exp_nat_mul`)
  this kind does not emit; `E6Bridge17.lean:129-141` has a SYMBOLIC rate `2 lam` and a `min`;
  `E6Bridge16.lean:563-598` is an exponent comparison (`Real.exp_le_exp` + `Real.exp_add`), not a
  polynomial absorption. Degree `>= 2` at a uniform rate remains `poly_exp_absorption`'s `(4m)^m`.
  There is no island instance of `shifted_rate` today; the mode ships because the audit specified
  it and its refusals are exact, not because a site consumes it.
* A `log`-mode threshold with a rational `Q > 1` is stated as `Real.log (max 1 Q) / (s a)`, never
  as a rational number: turning `log 400 / (1/50)` into `[297, 300]` is `exp_enclosure` /
  `transcendental_enclosure` territory (Audit14_Probes does it by hand), composed downstream.
* Symbolic `K` is cleared, not bounded: `Q <= K exp(...)` is the audit's downstream form, and
  `K > 0` is a hypothesis the island supplies (`hK0 := mul_pos ...`).
* It does not touch `E6Bridge7` / `E6Bridge14`; the standing-order REGEN of those sites (48H
  audit section 3 row 4) is the lead's call once the probe is green.
