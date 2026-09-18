# `interval_gram_inertia` — kernel-certified inertia of an interval matrix (2026-09-18)

`conjecture1_proved = False`. Everything below is finite linear algebra over explicit rational
boxes. Nothing here says anything about zeta, and nothing here is a step toward RH.

## The shape that had no certificate type

Read any D2 / D3 / T3 numeric instance in the Mirrormere program and it ends in the same sentence:

> *this Arb-enclosed Hermitian matrix has negative index exactly `q` (or is PSD).*

Before this emitter, Telperion could certify only pieces of that sentence:

| emitter | what it gives | what it misses |
|---|---|---|
| `psd_form` | exact rational PSD of ONE explicit matrix | no interval; PSD only, never a signature |
| `hermitian_moment` / `rank_trace_scalar` | scalar shadows (trace, rank counts) | not a signature |
| `rayleigh_gram` | one Rayleigh direction `cᵀJc − θcᵀIc > 0` | one direction, not a subspace pair |
| `two_moment_count` | eigenvalue COUNT from two moments | count, not inertia, and not over a box |

Consequence: `BraggDefect.lean` carries **hand-written 2x2 and 4x4 blocks**, and every new rung of
the D2/D3/T3 ladders needed a fresh hand proof. `interval_gram_inertia` replaces those with one
generic `n x n` instrument.

## The certificate

Input: rational entrywise bounds `lo ≤ hi`, both symmetric.

Untrusted Python computes, in exact rationals:

1. midpoint `M = (lo + hi)/2` and half-width `w = max_ij (hi_ij − lo_ij)/2`;
2. an exact congruence `BᵀMB = D` with `D` diagonal — symmetric Gaussian elimination with
   symmetric pivoting, i.e. `emit_psd_form`'s completing-the-square LDLᵀ primitive run to a FULL
   diagonalization (so it handles indefinite matrices, which `psd_certificate` refuses) and
   returning the change of basis, not just the pivots. It also rotates `e_k ↦ e_k + e_j` when the
   trailing diagonal vanishes, so `[[0,1],[1,0]]` is diagonalized rather than rejected;
3. the witness bases `X` (the columns of `B` at positive pivots, `p` of them) and `Y` (at negative
   pivots, `q` of them), each column rescaled to absolute-sum ONE. Because the congruence is exact,
   the compressed forms `C_X = XᵀMX` and `C_Y = Yᵀ(−M)Y` come out **diagonal** with strictly
   positive entries `cx_k`, `cy_k`;
4. margins `δ_X = min_k cx_k`, `δ_Y = min_k cy_k`, and Cauchy-Schwarz constants `S_X = p`,
   `S_Y = q` (one per unit-abs-sum column).

Soundness condition: `w · S < δ` on **both** sides. Then for any `G` in the box,

```
|xᵀ(G − M)x|  ≤  w · (Σ_i |x_i|)²          (entrywise bound, |x_i||x_j| ≤ (x_i²+x_j²)/2)
(Σ_i |(Xv)_i|)²  ≤  S · |v|²                (unit-abs-sum columns + Cauchy-Schwarz)
⟹ vᵀ(XᵀGX)v  ≥  (δ − w·S) · |v|²  >  0     for v ≠ 0
```

so the Hermitian form of `G` is positive definite on a `p`-dimensional subspace and that of `−G`
on a `q`-dimensional one.

## The Lean side (`RHInertia`, emitted by `interval_gram_inertia_prelude_lean`)

Five general lemmas over the ported RHLinalg block, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`) and free of placeholder tactics:

| lemma | statement | role |
|---|---|---|
| `hermForm_neg` | `hermForm (−A) x = −hermForm A x` | vocabulary |
| `defect` | `defect hA := posIndex hA.neg` | definitionally `DefectDictionary.defect` |
| `posIndex_add_posIndex_neg_le` | `n₊(A) + n₊(−A) ≤ n` | **upper** half of Sylvester: a form and its negative cannot both be positive definite on a shared nonzero vector, so the two maximal `PosDefOn` subspaces meet in `⊥` and their dimensions add to at most `n` |
| `card_le_posIndex_of_compress_posDef` | `XᴴAX` positive definite ⟹ `card p ≤ posIndex hA` | **lower** half: positive definiteness of the compressed form makes `X` injective for free, so `range X` is a `card p`-dimensional `PosDefOn` subspace and `finrank_le_posIndex_of_posDefOn` applies. This is the `offline_pairs_le_defect` mechanism, made generic in the witness basis |
| `compress_posDef_of_interval` | the interval step above | absorbs the box into the margin |
| `inertia_eq_of_witnesses` | two bases with `p + q = n` ⟹ `posIndex hG = p ∧ defect hG = q` | assembly (lower bounds + upper bound + `omega`) |

Emitted per box:

```lean
theorem <name> (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsHermitian)
    (hlo : ∀ i j, (!![…] : Matrix (Fin n) (Fin n) ℝ) i j ≤ G i j)
    (hhi : ∀ i j, G i j ≤ (!![…] : Matrix (Fin n) (Fin n) ℝ) i j) :
    RHLinalg.posIndex hG = p ∧ RHInertia.defect hG = q
```

### Tactic-cost note (measured, worth keeping)

A bare `simp` reduces `!![…] i j` at numeral indices, but on a 4x4 literal its full simp set blows
the `isDefEq` heartbeat budget. The prelude therefore ships four macros — `inertia_entries`,
`inertia_entries_sum`, `inertia_entries_mul`, `inertia_entries_using` — wrapping the minimal
`simp only` set, and the emitted per-entry box obligations use `linarith only [lo_i_j, hi_i_j]`
rather than letting `linarith` sweep a 32-hypothesis context `n²` times. With those two changes the
4-box example elaborates in ~10 s instead of timing out.

## Refusals (the anti-phantom face)

`interval_gram_inertia_certificate` refuses, by name:

- **asymmetric box** — an asymmetric box may contain NO Hermitian matrix, so the theorem would be
  vacuously true. This is the phantom the emitter exists to avoid;
- **empty box** (`lo_ij > hi_ij`) — the same phantom;
- **singular midpoint** (zero pivot) — the box straddles a zero eigenvalue; no constant signature;
- **wrong claimed signature** — `(p, q)` is checked against the exact congruence, never corrected;
- **definite box** (`p = 0` or `q = 0`) — that is `emit_psd_form`'s shape, and a `Fin 0` witness
  basis has no Lean matrix literal;
- **box wider than the pivot margin** (`w·S ≥ δ`) — the headline refusal: the signature is not
  certifiably constant on the box. This is exactly the "box straddling an eigenvalue sign" case,
  and it is what the negative control forges past.

## Negative control

`negctrl_adapters/adapter_interval_gram_inertia.py` targets the emitter's private pure-real route
`_emit_compress_margin`, which states the certificate's whole arithmetic content:

```lean
theorem <name> (v0 … : ℝ) (hv : 0 < Σ v_k²) : 0 < (Σ cx_k · v_k²) − (w · S_X) · (Σ v_k²)
```

- **forged FALSE**: `cx = 1/10` against slack `w·S_X = 1/2` — a box straddling the eigenvalue sign.
  Layer 1 refuses it; the adapter mints the frozen dataclass by hand to bypass that, and the Lean
  KERNEL rejects the proof (`nlinarith` cannot close a false inequality).
- **TRUE twin**: `cx = 1`, `w = 1/10` — a separated box; compiles clean.

Both twins are pure `(· : ℝ)` polynomial inequalities, so the control runs against plain Mathlib
with no RHLinalg import. Verified locally: `negative[kernel REJECTED the forged FALSE proof] |
positive[TRUE twin compiled clean]`.

## Scope and the island pin (the honest limits)

- **Real symmetric only.** Complex Hermitian instances need the `2n` real embedding (inertia
  doubles), proved once in the prelude. That lemma is **not built**; a complex instance is refused
  rather than faked.
- **Island-pinned.** `posIndex` / `hermForm` / `PosDefOn` / `finrank_le_posIndex_of_posDefOn` are
  NOT upstream Mathlib — they are the ported RHLinalg block (Apache-2.0, `anthropics/zeta-23-lean`,
  Lean v4.32.0) carried by the `hermitian_moment` island, which the `gram_inertia` island
  `path`-requires. The emitter is therefore pinned to v4.32.0.
- **What it does NOT do.** It certifies a signature; it does not produce eigenvalues, does not
  bound them, and says nothing about any matrix outside the stated box. The Arb enclosure that
  produced `lo`/`hi` for a real consumer remains the documented non-kernel trust seam, exactly as
  in the Li ladder.

## Consumers

- `mm-d2-weil-gram-trace` instances (Weil-Gram trace readings whose conclusion is a defect count);
- `mm-d3` certified partial sums;
- `mm-t3` rungs — replaces `BraggDefect.lean`'s hand-written 2x2 / 4x4 blocks with a generic `n x n`
  instrument (the shipped `inertia_pair_block_2` and `inertia_offline_pairs_4` are exactly those two
  shapes);
- Route B B4 windows;
- `RvMRoutePInertia` on the li_positivity island (consumes the emitted certificates; not wired here).

## Where things live

| artifact | path |
|---|---|
| emitter | `telperion/src/telperion/emit_interval_gram_inertia.py` |
| negative control | `telperion/src/telperion/negctrl_adapters/adapter_interval_gram_inertia.py` |
| stance | `telperion/src/telperion/emitter_sensitivity.py` (`CERTIFICATE_SENSITIVE` + adapter) |
| dispatch | `telperion/src/telperion/certify.py` (`_SPECIAL_KINDS`, `_SPECIAL_DISPATCH`) |
| tests | `telperion/tests/test_emit_interval_gram_inertia.py` |
| dogfood example | `telperion/examples/gram_inertia/` (drift-gated, `telperion.toml` `[[check]]`) |
| CI | `.github/workflows/telperion-lean-e2e.yml`, job `gram-inertia-compiles` |
