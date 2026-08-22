# Matrix-PSD (LDLᵀ) certificate — status & Lean-emit design (2026-08-21)

From [COVERAGE_GAPS_2026-08-21](COVERAGE_GAPS_2026-08-21.md) rank #2. Matrix
inequalities are a class Telperion's scalar-polynomial emitters cannot state.

## Shipped (this PR) — exact finder + verifier, fully tested

`telperion/psd.py`:
- `find_psd_certificate(A)` — exact square-root-free LDLᵀ of a symmetric rational
  `A` (no-pivot recursion, zero-pivot tolerant): returns `A = L D Lᵀ` with
  unit-lower-triangular `L`, diagonal `D ≥ 0`, and a `positive_definite` flag
  (`Dᵢᵢ > 0`). Returns `None` for indefinite / non-symmetric / PSD-only-under-
  pivoting.
- `verify_psd_certificate` — independent exact re-check: `L` unit lower
  triangular, `D` diagonal, `A = L D Lᵀ` exactly, `Dᵢᵢ ≥ 0`, flag matches.
- CLI `telperion psd '[[2,1],[1,2]]'` — find + verify + report PD/PSD.

Tested (`tests/test_psd.py`): PD, singular-PSD (rank-deficient), indefinite
(rejected), exact 3×3 reconstruction, tampered-diagonal rejection. All exact
rationals — no SDP, no floating point, no Lean needed for this layer.

## Follow-up (CI-gated) — the Lean emitter

Mathlib carries the load-bearing definitions: `Matrix.PosSemidef`,
`Matrix.PosDef`, and an `LDL` decomposition. The soundness argument is
`xᵀAx = Σᵢ Dᵢᵢ (Lᵀx)ᵢ² ≥ 0`. Emission shape (per matrix, exact rational entries):

```lean
theorem A_posSemidef : (!![...] : Matrix (Fin n) (Fin n) ℚ).PosSemidef := by
  -- exhibit A = L D Lᵀ (a `decide`/`ext; norm_num` matrix identity),
  -- then xᵀAx = (Lᵀx)ᵀ D (Lᵀx) = Σ Dᵢᵢ yᵢ² with Dᵢᵢ ≥ 0 (`norm_num`), so ≥ 0.
```

The open question (why CI-gated, not shipped): the cleanest Lean route from the
LDLᵀ data to `Matrix.PosSemidef` — whether to (a) reuse Mathlib's `LDL`
namespace directly, (b) prove `A = Lᴴ * D * L` and apply a
`posSemidef_of_LDL`-style lemma if one exists, or (c) go through the quadratic
form `Σ Dᵢᵢ yᵢ²` explicitly — must be settled against the pinned Mathlib and
verified in CI (this machine cannot build Lean; see memory
"System crashes = SoC watchdog panics"). Until a CI-green emission is
demonstrated, no matrix-PSD Lean is claimed to compile; the finder/verifier ship
now.

Extensions once the base emitter is green: Schur-complement block reduction
(certify block-PSD via a smaller PSD + one rational Schur complement) and
Loewner comparisons `A ≼ B` (certify `B − A` PSD).
